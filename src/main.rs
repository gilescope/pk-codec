//! Spike: structure-aware lossless codec for Midnight prover keys.
//!
//! A `.prover` file is `tag ‖ SCALE-compact len ‖ gzip(MidnightPK::write(RawBytesUnchecked))`.
//! The gzip payload ends with two halo2 polynomial slices (`midnight-proofs` 0.7.x
//! `ProvingKey::write`): `fixed_values` then permutation `σ`. Each slice is
//! `u32 BE count`, then per column `u32 BE n` and `n` field elements as 32-byte
//! Montgomery LE limbs. Those two slices are >99% of the bytes.
//!
//! Why they compress badly and what we do instead:
//! - `σ[i][j] = δ^c·ω^r` for the cell `(c, r)` it is wired to. Uniform-looking as bytes, but it
//!   carries only `log2(cols·n)` bits. We invert it with a table of every `δ^c·ω^r` and store
//!   `cell - own_cell` (0 for unwired cells).
//! - Fixed columns hold selectors and constants with heavy repetition. We store a dictionary of
//!   distinct values plus a per-cell index.
//!
//! Everything before the fixed slice (header, IR, VK) is kept verbatim. Decoding reproduces the
//! gzip payload byte for byte; the outer file matches too iff re-gzipping at level 6 does.

use std::collections::HashMap;
use std::io::{Read, Write};
use std::path::Path;
use std::time::Instant;

use anyhow::{bail, ensure, Context, Result};
use ff::{Field, PrimeField};
use flate2::{read::GzDecoder, write::GzEncoder, Compression};
use midnight_curves::bls12_381::Fq as Fr;
use midnight_curves::serde_traits::SerdeObject;

const MAGIC: &[u8; 4] = b"PKC1";
const FE: usize = 32;
const GZIP_MAGIC: [u8; 3] = [0x1f, 0x8b, 0x08];
/// `transient-crypto` `PK_COMPRESSION_LEVEL`.
const LEDGER_GZIP_LEVEL: u32 = 6;
const ZSTD_LEVEL: i32 = 19;

/// A parsed `.prover` file.
struct ProverFile {
    /// Ledger tag and SCALE length, verbatim.
    outer_header: Vec<u8>,
    /// The gzip-decompressed `MidnightPK` bytes.
    raw: Vec<u8>,
}

impl ProverFile {
    fn parse(file: &[u8]) -> Result<Self> {
        let gz_at = file
            .windows(GZIP_MAGIC.len())
            .position(|w| w == GZIP_MAGIC)
            .context("no gzip stream found: expected `1f 8b 08` after the ledger tag")?;
        let mut raw = Vec::new();
        GzDecoder::new(&file[gz_at..]).read_to_end(&mut raw)?;
        Ok(Self {
            outer_header: file[..gz_at].to_vec(),
            raw,
        })
    }

    /// Rebuilds the file the way the ledger writes it.
    fn to_file(&self) -> Result<Vec<u8>> {
        let mut out = self.outer_header.clone();
        let mut gz = GzEncoder::new(Vec::new(), Compression::new(LEDGER_GZIP_LEVEL));
        gz.write_all(&self.raw)?;
        out.extend(gz.finish()?);
        Ok(out)
    }
}

/// Byte layout of the two trailing polynomial slices.
#[derive(Debug, Clone, Copy)]
struct Tail {
    /// Offset of the fixed slice's `u32` count.
    start: usize,
    fixed_cols: usize,
    perm_cols: usize,
    n: usize,
}

impl Tail {
    fn slice_len(cols: usize, n: usize) -> usize {
        4 + cols * (4 + FE * n)
    }

    fn col_offset(&self, slice_start: usize, col: usize) -> usize {
        slice_start + 4 + col * (4 + FE * self.n) + 4
    }

    fn perm_start(&self) -> usize {
        self.start + Self::slice_len(self.fixed_cols, self.n)
    }

    /// Finds the unique `(fixed_cols, perm_cols)` whose slices end exactly at EOF with every
    /// header consistent. `k` is `MidnightPK`'s second byte.
    fn locate(raw: &[u8]) -> Result<Self> {
        ensure!(
            raw.len() > 2,
            "payload too short ({} bytes) to hold a MidnightPK",
            raw.len()
        );
        let k = raw[1];
        ensure!(k <= 32, "implausible k = {k} at payload offset 1");
        let n = 1usize << k;
        let be = |at: usize| {
            raw.get(at..at + 4)
                .map(|b| u32::from_be_bytes(b.try_into().unwrap()))
        };
        let mut hits = Vec::new();
        let max_cols = raw.len() / (FE * n);
        for fixed_cols in 0..=max_cols {
            for perm_cols in 0..=max_cols - fixed_cols {
                let len = Self::slice_len(fixed_cols, n) + Self::slice_len(perm_cols, n);
                let Some(start) = raw.len().checked_sub(len) else {
                    continue;
                };
                let t = Tail {
                    start,
                    fixed_cols,
                    perm_cols,
                    n,
                };
                let ok = be(start) == Some(fixed_cols as u32)
                    && be(t.perm_start()) == Some(perm_cols as u32)
                    && (0..fixed_cols).all(|c| be(t.col_offset(start, c) - 4) == Some(n as u32))
                    && (0..perm_cols)
                        .all(|c| be(t.col_offset(t.perm_start(), c) - 4) == Some(n as u32));
                if ok {
                    hits.push(t);
                }
            }
        }
        // A field element can spell a plausible `u32` count, so shorter spurious layouts also fit
        // (seen: `fixed_cols = 0` starting inside the last fixed column). The real one covers
        // the most bytes; round-trip verification backstops the choice.
        hits.into_iter()
            .min_by_key(|t| t.start)
            .with_context(|| format!("no fixed/σ slice layout with n = 2^{k} ends at EOF; not a midnight-proofs 0.7 key?"))
    }
}

fn put_varint(out: &mut Vec<u8>, mut v: u64) {
    while v >= 0x80 {
        out.push((v as u8) | 0x80);
        v >>= 7;
    }
    out.push(v as u8);
}

fn get_varint(buf: &[u8], at: &mut usize) -> Result<u64> {
    let mut v = 0u64;
    for shift in (0..64).step_by(7) {
        let b = *buf.get(*at).context("varint runs past end of stream")?;
        *at += 1;
        v |= u64::from(b & 0x7f) << shift;
        if b & 0x80 == 0 {
            return Ok(v);
        }
    }
    bail!("varint longer than 10 bytes at stream offset {}", *at)
}

fn zigzag(v: i64) -> u64 {
    ((v << 1) ^ (v >> 63)) as u64
}

fn unzigzag(v: u64) -> i64 {
    ((v >> 1) as i64) ^ -((v & 1) as i64)
}

fn fe_bytes(f: &Fr) -> [u8; FE] {
    f.to_raw_bytes()
        .try_into()
        .expect("Fr raw encoding is 32 bytes")
}

/// Every `δ^c·ω^r`, indexed by cell `c·n + r`, as raw Montgomery bytes.
fn delta_omega(perm_cols: usize, k: u32) -> Vec<[u8; FE]> {
    let n = 1usize << k;
    // halo2 `EvaluationDomain`: ω = ROOT_OF_UNITY squared (S - k) times.
    let omega = (k..Fr::S).fold(Fr::ROOT_OF_UNITY, |w, _| w.square());
    let mut out = Vec::with_capacity(perm_cols * n);
    let mut d = Fr::ONE;
    for _ in 0..perm_cols {
        let mut v = d;
        for _ in 0..n {
            out.push(fe_bytes(&v));
            v *= omega;
        }
        d *= Fr::DELTA;
    }
    out
}

/// Section sizes of one encoding, compressed.
#[derive(Default, Debug)]
struct Sizes {
    prefix: usize,
    fixed_dict: usize,
    fixed_idx: usize,
    perm: usize,
    total: usize,
    dict_entries: usize,
    wired_cells: usize,
    perm_cells: usize,
    escapes: usize,
}

/// Entropy backend for the transformed sections; `PKC_BACKEND=gzip` for the gzip-6 comparison.
fn gzip_backend() -> bool {
    std::env::var("PKC_BACKEND").is_ok_and(|b| b == "gzip")
}

fn zstd_section(out: &mut Vec<u8>, data: &[u8]) -> Result<usize> {
    let z = if gzip_backend() {
        let mut gz = GzEncoder::new(Vec::new(), Compression::new(LEDGER_GZIP_LEVEL));
        gz.write_all(data)?;
        gz.finish()?
    } else {
        zstd::bulk::compress(data, ZSTD_LEVEL)?
    };
    put_varint(out, data.len() as u64);
    put_varint(out, z.len() as u64);
    out.extend_from_slice(&z);
    Ok(z.len())
}

fn unzstd_section(buf: &[u8], at: &mut usize) -> Result<Vec<u8>> {
    let raw_len = get_varint(buf, at)? as usize;
    let z_len = get_varint(buf, at)? as usize;
    let z = buf
        .get(*at..*at + z_len)
        .context("zstd section truncated")?;
    *at += z_len;
    let data = if gzip_backend() {
        let mut d = Vec::with_capacity(raw_len);
        GzDecoder::new(z).read_to_end(&mut d)?;
        d
    } else {
        zstd::bulk::decompress(z, raw_len)?
    };
    ensure!(
        data.len() == raw_len,
        "zstd section decoded to {} bytes, header says {raw_len}",
        data.len()
    );
    Ok(data)
}

fn encode(pf: &ProverFile) -> Result<(Vec<u8>, Sizes)> {
    let raw = &pf.raw;
    let t = Tail::locate(raw)?;
    let k = t.n.trailing_zeros();
    let mut s = Sizes::default();
    let mut out = MAGIC.to_vec();
    for v in [t.fixed_cols, t.perm_cols, k as usize] {
        put_varint(&mut out, v as u64);
    }

    let mut prefix = pf.outer_header.clone();
    let hdr_len = prefix.len();
    prefix.extend_from_slice(&raw[..t.start]);
    put_varint(&mut out, hdr_len as u64);
    s.prefix = zstd_section(&mut out, &prefix)?;

    // Fixed: dictionary in first-seen order (deterministic), then per-cell varint indices.
    let mut dict: Vec<[u8; FE]> = Vec::new();
    let mut seen: HashMap<[u8; FE], u64> = HashMap::new(); // lookup only, never iterated
    let mut idx = Vec::new();
    for c in 0..t.fixed_cols {
        let col = &raw[t.col_offset(t.start, c)..][..FE * t.n];
        for fe in col.chunks_exact(FE) {
            let fe: [u8; FE] = fe.try_into().unwrap();
            let i = *seen.entry(fe).or_insert_with(|| {
                dict.push(fe);
                dict.len() as u64 - 1
            });
            put_varint(&mut idx, i);
        }
    }
    s.dict_entries = dict.len();
    s.fixed_dict = zstd_section(&mut out, &dict.concat())?;
    s.fixed_idx = zstd_section(&mut out, &idx)?;

    // σ: invert δ^c·ω^r to a cell index; store zigzag(cell - own) + 1, 0 = escape + raw bytes.
    let table = delta_omega(t.perm_cols, k);
    let lookup: HashMap<&[u8; FE], u64> = table.iter().zip(0u64..).collect(); // lookup only
    let mut perm = Vec::new();
    for c in 0..t.perm_cols {
        let col = &raw[t.col_offset(t.perm_start(), c)..][..FE * t.n];
        for (r, fe) in col.chunks_exact(FE).enumerate() {
            let own = (c * t.n + r) as i64;
            match lookup.get(<&[u8; FE]>::try_from(fe).unwrap()) {
                Some(&cell) => {
                    let d = cell as i64 - own;
                    s.wired_cells += usize::from(d != 0);
                    put_varint(&mut perm, zigzag(d) + 1);
                }
                None => {
                    s.escapes += 1;
                    perm.push(0);
                    perm.extend_from_slice(fe);
                }
            }
        }
    }
    s.perm_cells = t.perm_cols * t.n;
    s.perm = zstd_section(&mut out, &perm)?;
    s.total = out.len();
    Ok((out, s))
}

fn decode(buf: &[u8]) -> Result<ProverFile> {
    ensure!(
        buf.get(..4) == Some(MAGIC),
        "not a PKC1 stream: bad magic {:02x?}",
        buf.get(..4)
    );
    let mut at = 4;
    let fixed_cols = get_varint(buf, &mut at)? as usize;
    let perm_cols = get_varint(buf, &mut at)? as usize;
    let k = get_varint(buf, &mut at)? as u32;
    let n = 1usize << k;
    let hdr_len = get_varint(buf, &mut at)? as usize;
    let prefix = unzstd_section(buf, &mut at)?;
    let dict = unzstd_section(buf, &mut at)?;
    let idx = unzstd_section(buf, &mut at)?;
    let perm = unzstd_section(buf, &mut at)?;
    ensure!(
        at == buf.len(),
        "{} trailing bytes after last section",
        buf.len() - at
    );

    let (outer_header, pk_prefix) = prefix.split_at(hdr_len);
    let mut raw = pk_prefix.to_vec();
    let n_be = (n as u32).to_be_bytes();

    raw.extend_from_slice(&(fixed_cols as u32).to_be_bytes());
    let mut i = 0;
    for _ in 0..fixed_cols {
        raw.extend_from_slice(&n_be);
        for _ in 0..n {
            let e = get_varint(&idx, &mut i)? as usize;
            raw.extend_from_slice(
                dict.get(e * FE..(e + 1) * FE)
                    .context("fixed index past dictionary")?,
            );
        }
    }

    let table = delta_omega(perm_cols, k);
    raw.extend_from_slice(&(perm_cols as u32).to_be_bytes());
    let mut i = 0;
    for c in 0..perm_cols {
        raw.extend_from_slice(&n_be);
        for r in 0..n {
            match get_varint(&perm, &mut i)? {
                0 => {
                    raw.extend_from_slice(perm.get(i..i + FE).context("escape truncated")?);
                    i += FE;
                }
                z => {
                    let cell = (c * n + r) as i64 + unzigzag(z - 1);
                    let cell = usize::try_from(cell).context("σ cell index negative")?;
                    raw.extend_from_slice(table.get(cell).context("σ cell index past table")?);
                }
            }
        }
    }
    Ok(ProverFile {
        outer_header: outer_header.to_vec(),
        raw,
    })
}

fn mb(b: usize) -> f64 {
    b as f64 / 1e6
}

fn run(path: &Path) -> Result<()> {
    let file = std::fs::read(path)?;
    let pf = ProverFile::parse(&file)?;
    let t = Tail::locate(&pf.raw)?;

    let t0 = Instant::now();
    let (enc, s) = encode(&pf)?;
    let t_enc = t0.elapsed();
    let t0 = Instant::now();
    let dec = decode(&enc)?;
    let t_dec = t0.elapsed();

    ensure!(dec.outer_header == pf.outer_header, "outer header mismatch");
    ensure!(dec.raw == pf.raw, "payload mismatch after round trip");
    let file_exact = dec.to_file()? == file;
    let zstd_raw = zstd::bulk::compress(&pf.raw, ZSTD_LEVEL)?.len();

    println!(
        "{} k={} fixed={} σ={}\n  file(gzip6) {:>8.2} MB · raw {:>8.2} MB · zstd19(raw) {:>8.2} MB · codec {:>7.3} MB = {:.1}x vs file\n  \
         sections: prefix {:.3} · dict {:.3} ({} entries) · fixed idx {:.3} · σ {:.3} MB\n  \
         σ wired {}/{} cells ({:.2}%) · escapes {} · enc {:.2?} dec {:.2?}\n  \
         ◈ payload round-trip byte-exact · file byte-exact: {}",
        path.display(),
        t.n.trailing_zeros(),
        t.fixed_cols,
        t.perm_cols,
        mb(file.len()),
        mb(pf.raw.len()),
        mb(zstd_raw),
        mb(s.total),
        file.len() as f64 / s.total as f64,
        mb(s.prefix),
        mb(s.fixed_dict),
        s.dict_entries,
        mb(s.fixed_idx),
        mb(s.perm),
        s.wired_cells,
        s.perm_cells,
        100.0 * s.wired_cells as f64 / s.perm_cells as f64,
        s.escapes,
        t_enc,
        t_dec,
        if file_exact { "yes" } else { "no (gzip bytes differ; payload identical)" },
    );
    Ok(())
}

fn main() -> Result<()> {
    let paths: Vec<_> = std::env::args_os().skip(1).collect();
    ensure!(!paths.is_empty(), "usage: pk-codec <file.prover>...");
    let mut failed = 0;
    for p in &paths {
        if let Err(e) = run(Path::new(p)) {
            failed += 1;
            eprintln!("✗ {}: {e:#}", Path::new(p).display());
        }
    }
    ensure!(failed == 0, "{failed} of {} files failed", paths.len());
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn varint_zigzag_round_trip() {
        for v in [0i64, 1, -1, 63, -64, 1 << 40, -(1 << 40), i64::MAX >> 1] {
            let mut b = Vec::new();
            put_varint(&mut b, zigzag(v));
            let mut at = 0;
            assert_eq!(unzigzag(get_varint(&b, &mut at).unwrap()), v);
            assert_eq!(at, b.len());
        }
    }

    #[test]
    fn delta_omega_is_injective() {
        let t = delta_omega(8, 10);
        let set: std::collections::BTreeSet<_> = t.iter().collect();
        assert_eq!(set.len(), t.len());
    }
}
