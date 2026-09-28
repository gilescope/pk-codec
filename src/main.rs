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
use midnight_curves::fft::best_fft;
use midnight_curves::serde_traits::SerdeObject;

const MAGIC: &[u8; 4] = b"PKC1";
const FE: usize = 32;
const GZIP_MAGIC: [u8; 3] = [0x1f, 0x8b, 0x08];
/// `transient-crypto` `PK_COMPRESSION_LEVEL`.
const LEDGER_GZIP_LEVEL: u32 = 6;
const ZSTD_LEVEL: i32 = 19;
/// Decoder limits: a stream is untrusted input, so every declared size is checked before it
/// is allocated. `k` ≤ 26 covers the largest keys seen (~k = 19) with room to spare.
const MAX_K: u32 = 26;
const MAX_COLS: usize = 4096;
const MAX_OUTPUT: usize = 8 << 30;

/// Entropy coder for the transformed sections, recorded in the stream after the magic.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
enum Backend {
    /// Sections stored uncompressed; any outer compressor is applied to the whole stream.
    Store = 0,
    Zstd = 1,
    Gzip = 2,
}

impl Backend {
    fn from_byte(b: u8) -> Result<Self> {
        match b {
            0 => Ok(Self::Store),
            1 => Ok(Self::Zstd),
            2 => Ok(Self::Gzip),
            _ => bail!(
                "unknown entropy backend byte {b:#04x}: expected 0 (store), 1 (zstd) or 2 (gzip)"
            ),
        }
    }
}

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

fn put_section(out: &mut Vec<u8>, data: &[u8], backend: Backend) -> Result<usize> {
    let z = match backend {
        Backend::Gzip => {
            let mut gz = GzEncoder::new(Vec::new(), Compression::new(LEDGER_GZIP_LEVEL));
            gz.write_all(data)?;
            gz.finish()?
        }
        Backend::Zstd => zstd::bulk::compress(data, ZSTD_LEVEL)?,
        Backend::Store => data.to_vec(),
    };
    put_varint(out, data.len() as u64);
    put_varint(out, z.len() as u64);
    out.extend_from_slice(&z);
    Ok(z.len())
}

/// Reads one section, refusing to allocate more than `limit` bytes for it.
fn get_section(
    buf: &[u8],
    at: &mut usize,
    backend: Backend,
    limit: usize,
    what: &str,
) -> Result<Vec<u8>> {
    let raw_len = usize::try_from(get_varint(buf, at)?)?;
    ensure!(
        raw_len <= limit,
        "{what} section claims {raw_len} bytes, limit for this key is {limit}"
    );
    let z_len = usize::try_from(get_varint(buf, at)?)?;
    let z = at
        .checked_add(z_len)
        .and_then(|end| buf.get(*at..end))
        .with_context(|| format!("{what} section truncated: needs {z_len} bytes at offset {at}"))?;
    *at += z_len;
    let data = match backend {
        Backend::Gzip => {
            let mut d = Vec::with_capacity(raw_len);
            GzDecoder::new(z)
                .take(raw_len as u64 + 1)
                .read_to_end(&mut d)?;
            d
        }
        Backend::Zstd => zstd::bulk::decompress(z, raw_len)?,
        Backend::Store => z.to_vec(),
    };
    ensure!(
        data.len() == raw_len,
        "{what} section decoded to {} bytes, header says {raw_len}",
        data.len()
    );
    Ok(data)
}

fn encode(pf: &ProverFile, backend: Backend) -> Result<(Vec<u8>, Sizes)> {
    let raw = &pf.raw;
    let t = Tail::locate(raw)?;
    let k = t.n.trailing_zeros();
    let mut s = Sizes::default();
    let mut out = MAGIC.to_vec();
    out.push(backend as u8);
    for v in [t.fixed_cols, t.perm_cols, k as usize] {
        put_varint(&mut out, v as u64);
    }

    let mut prefix = pf.outer_header.clone();
    let hdr_len = prefix.len();
    prefix.extend_from_slice(&raw[..t.start]);
    put_varint(&mut out, hdr_len as u64);
    s.prefix = put_section(&mut out, &prefix, backend)?;

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
    s.fixed_dict = put_section(&mut out, &dict.concat(), backend)?;
    s.fixed_idx = put_section(&mut out, &idx, backend)?;

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
    s.perm = put_section(&mut out, &perm, backend)?;
    s.total = out.len();
    Ok((out, s))
}

fn decode(buf: &[u8]) -> Result<ProverFile> {
    ensure!(
        buf.get(..4) == Some(MAGIC),
        "not a PKC1 stream: bad magic {:02x?}",
        buf.get(..4)
    );
    let backend = Backend::from_byte(*buf.get(4).context("stream ends before backend byte")?)?;
    let mut at = 5;
    let mut header = || -> Result<usize> { Ok(usize::try_from(get_varint(buf, &mut at)?)?) };
    let (fixed_cols, perm_cols, k, hdr_len) = (header()?, header()?, header()?, header()?);
    ensure!(
        k <= MAX_K as usize,
        "k = {k} exceeds the decoder limit {MAX_K}"
    );
    ensure!(
        fixed_cols <= MAX_COLS && perm_cols <= MAX_COLS,
        "{fixed_cols} fixed / {perm_cols} σ columns exceeds the decoder limit {MAX_COLS}"
    );
    let k = u32::try_from(k)?;
    let n = 1usize << k;
    // Both slices together; checked so a wasm32 `usize` cannot wrap.
    let cells = (fixed_cols + perm_cols)
        .checked_mul(n)
        .context("cell count overflows usize")?;
    let tail = cells
        .checked_mul(FE)
        .filter(|&b| b <= MAX_OUTPUT)
        .with_context(|| {
            format!("{cells} cells × {FE} B exceeds the decoder output limit {MAX_OUTPUT} B")
        })?;
    let prefix = get_section(buf, &mut at, backend, MAX_OUTPUT - tail, "prefix")?;
    let dict = get_section(
        buf,
        &mut at,
        backend,
        fixed_cols * n * FE,
        "fixed dictionary",
    )?;
    let idx = get_section(buf, &mut at, backend, fixed_cols * n * 10, "fixed index")?;
    let perm = get_section(buf, &mut at, backend, perm_cols * n * (1 + FE), "σ")?;
    ensure!(
        hdr_len <= prefix.len(),
        "outer header length {hdr_len} exceeds prefix {} B",
        prefix.len()
    );
    ensure!(
        at == buf.len(),
        "{} trailing bytes after last section",
        buf.len() - at
    );

    let (outer_header, pk_prefix) = prefix.split_at(hdr_len);
    let mut raw = pk_prefix.to_vec();
    let n_be = u32::try_from(n)?.to_be_bytes();

    raw.extend_from_slice(&u32::try_from(fixed_cols)?.to_be_bytes());
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

    ensure!(
        i == idx.len(),
        "fixed index has {} trailing bytes",
        idx.len() - i
    );

    let table = delta_omega(perm_cols, k);
    raw.extend_from_slice(&u32::try_from(perm_cols)?.to_be_bytes());
    let mut i = 0;
    for c in 0..perm_cols {
        raw.extend_from_slice(&n_be);
        for r in 0..n {
            match get_varint(&perm, &mut i)? {
                0 => {
                    let fe = i.checked_add(FE).and_then(|end| perm.get(i..end));
                    raw.extend_from_slice(fe.context("σ escape truncated")?);
                    i += FE;
                }
                z => {
                    let own = i64::try_from(c * n + r)?;
                    let cell = own
                        .checked_add(unzigzag(z - 1))
                        .and_then(|v| usize::try_from(v).ok());
                    let cell = cell.context("σ cell index out of range")?;
                    raw.extend_from_slice(table.get(cell).context("σ cell index past table")?);
                }
            }
        }
    }
    ensure!(
        i == perm.len(),
        "σ stream has {} trailing bytes",
        perm.len() - i
    );
    Ok(ProverFile {
        outer_header: outer_header.to_vec(),
        raw,
    })
}

/// Rebuilds what `ProvingKey::read` derives on load (coefficient form via inverse FFT, then
/// an extended coset via forward FFT) and reports its compressibility and cost. `ext` is the
/// extended-domain factor as a power of two; it depends on the circuit's gate degree, which
/// this file does not record.
fn fft_forms(raw: &[u8], t: &Tail, ext: u32) -> Result<()> {
    let k = t.n.trailing_zeros();
    let root = |bits: u32| (bits..Fr::S).fold(Fr::ROOT_OF_UNITY, |w, _| w.square());
    let omega_inv = root(k).invert().unwrap();
    let n_inv = Fr::from(u64::try_from(t.n)?).invert().unwrap();
    let ext_omega = root(k + ext);
    let zeta = Fr::MULTIPLICATIVE_GENERATOR;
    let cols: Vec<usize> = (0..t.fixed_cols)
        .map(|c| t.col_offset(t.start, c))
        .chain((0..t.perm_cols).map(|c| t.col_offset(t.perm_start(), c)))
        .collect();
    let (mut coeff_bytes, mut coset_bytes) = (Vec::new(), Vec::new());
    let (mut t_ifft, mut t_fft) = (std::time::Duration::ZERO, std::time::Duration::ZERO);
    for off in cols {
        let mut a: Vec<Fr> = raw[off..][..FE * t.n]
            .chunks_exact(FE)
            .map(Fr::from_raw_bytes_unchecked)
            .collect();
        let t0 = Instant::now();
        best_fft(&mut a, omega_inv, k);
        a.iter_mut().for_each(|v| *v *= n_inv);
        t_ifft += t0.elapsed();
        a.iter().for_each(|v| coeff_bytes.extend(fe_bytes(v)));
        let t0 = Instant::now();
        let mut shift = Fr::ONE;
        let mut e: Vec<Fr> = a
            .iter()
            .map(|&v| {
                let x = v * shift;
                shift *= zeta;
                x
            })
            .collect();
        e.resize(t.n << ext, Fr::ZERO);
        best_fft(&mut e, ext_omega, k + ext);
        t_fft += t0.elapsed();
        e.iter().for_each(|v| coset_bytes.extend(fe_bytes(v)));
    }
    let z = |b: &[u8]| zstd::bulk::compress(b, 3).map(|z| 100.0 * z.len() as f64 / b.len() as f64);
    println!(
        "  coeff form {:.1} MB → zstd {:.1}% · coset ×{} {:.1} MB → zstd {:.1}%\n  \
         load FFTs (rayon, all cores): inverse {t_ifft:.2?} + extended {t_fft:.2?}",
        mb(coeff_bytes.len()),
        z(&coeff_bytes)?,
        1 << ext,
        mb(coset_bytes.len()),
        z(&coset_bytes)?,
    );
    Ok(())
}

/// Columns whose load-time FFTs are trivial: constant fixed columns, identity σ columns.
fn column_stats(raw: &[u8], t: &Tail) {
    let fixed_const = (0..t.fixed_cols)
        .filter(|&c| {
            let col = &raw[t.col_offset(t.start, c)..][..FE * t.n];
            col.chunks_exact(FE).all(|fe| fe == &col[..FE])
        })
        .count();
    let table = delta_omega(t.perm_cols, t.n.trailing_zeros());
    let perm_id = (0..t.perm_cols)
        .filter(|&c| {
            let col = &raw[t.col_offset(t.perm_start(), c)..][..FE * t.n];
            col.chunks_exact(FE)
                .zip(&table[c * t.n..])
                .all(|(fe, id)| fe == id)
        })
        .count();
    println!(
        "  trivial columns: fixed constant {fixed_const}/{} · σ identity {perm_id}/{}",
        t.fixed_cols, t.perm_cols
    );
}

fn mb(b: usize) -> f64 {
    b as f64 / 1e6
}

fn run(path: &Path) -> Result<()> {
    let file = std::fs::read(path)?;
    let t0 = Instant::now();
    let pf = ProverFile::parse(&file)?;
    let t_gunzip = t0.elapsed();
    let t = Tail::locate(&pf.raw)?;

    let t0 = Instant::now();
    let backend = match std::env::var("PKC_BACKEND").as_deref() {
        Ok("gzip") => Backend::Gzip,
        Ok("store") => Backend::Store,
        _ => Backend::Zstd,
    };
    let (enc, s) = encode(&pf, backend)?;
    let t_enc = t0.elapsed();
    let t0 = Instant::now();
    let dec = decode(&enc)?;
    let t_dec = t0.elapsed();
    if std::env::var_os("PKC_STATS").is_some() {
        column_stats(&pf.raw, &t);
        println!("  gunzip {t_gunzip:.2?} vs codec decode {t_dec:.2?}");
        fft_forms(&pf.raw, &t, 2)?;
    }

    ensure!(dec.outer_header == pf.outer_header, "outer header mismatch");
    ensure!(dec.raw == pf.raw, "payload mismatch after round trip");
    let file_exact = dec.to_file()? == file;
    let zstd_raw = zstd::bulk::compress(&pf.raw, ZSTD_LEVEL)?.len();
    if backend == Backend::Store {
        let mut gz = GzEncoder::new(Vec::new(), Compression::new(LEDGER_GZIP_LEVEL));
        gz.write_all(&enc)?;
        let outer_gz = gz.finish()?.len();
        let outer_zstd = zstd::bulk::compress(&enc, ZSTD_LEVEL)?.len();
        println!(
            "  outer layer over stored stream {:.3} MB: gzip6 {:.3} MB ({:.1}x) · zstd19 {:.3} MB ({:.1}x)",
            mb(enc.len()), mb(outer_gz), file.len() as f64 / outer_gz as f64,
            mb(outer_zstd), file.len() as f64 / outer_zstd as f64,
        );
    }

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

    const K: u32 = 4;
    const N: usize = 1 << K;

    fn push_slice(raw: &mut Vec<u8>, cols: &[Vec<[u8; FE]>]) {
        raw.extend_from_slice(&u32::try_from(cols.len()).unwrap().to_be_bytes());
        for col in cols {
            raw.extend_from_slice(&u32::try_from(col.len()).unwrap().to_be_bytes());
            col.iter().for_each(|fe| raw.extend_from_slice(fe));
        }
    }

    /// A minimal key: 2 fixed columns (repeating constants) and 2 σ columns that are the
    /// identity except one swapped pair and one value outside the δ^c·ω^r table (an escape).
    fn synthetic_key() -> ProverFile {
        let fixed: Vec<Vec<[u8; FE]>> = (0..2u8)
            .map(|c| {
                (0..N)
                    .map(|r| [u8::try_from(r % 3).unwrap() + c; FE])
                    .collect()
            })
            .collect();
        let table = delta_omega(2, K);
        let mut perm: Vec<Vec<[u8; FE]>> = table.chunks(N).map(<[_]>::to_vec).collect();
        perm[0].swap(1, 5);
        perm[1][7] = [0xee; FE];
        let mut raw = vec![0, u8::try_from(K).unwrap(), 0xab, 0xcd];
        push_slice(&mut raw, &fixed);
        push_slice(&mut raw, &perm);
        ProverFile {
            outer_header: b"tag:".to_vec(),
            raw,
        }
    }

    #[test]
    fn synthetic_round_trip_both_backends() {
        let pf = synthetic_key();
        for backend in [Backend::Zstd, Backend::Gzip] {
            let (enc, s) = encode(&pf, backend).unwrap();
            assert_eq!(s.escapes, 1, "{backend:?}");
            assert_eq!(s.wired_cells, 2, "{backend:?}");
            let dec = decode(&enc).unwrap();
            assert_eq!(dec.outer_header, pf.outer_header);
            assert_eq!(dec.raw, pf.raw, "{backend:?}");
        }
    }

    /// Builds a stream by hand so the decoder can be fed headers an encoder would never emit.
    fn pack(cols: (u64, u64), k: u64, hdr_len: u64, sections: [&[u8]; 4]) -> Vec<u8> {
        let mut out = MAGIC.to_vec();
        out.push(Backend::Zstd as u8);
        for v in [cols.0, cols.1, k, hdr_len] {
            put_varint(&mut out, v);
        }
        for s in sections {
            put_section(&mut out, s, Backend::Zstd).unwrap();
        }
        out
    }

    #[test]
    fn decode_rejects_hostile_headers() {
        let ok_prefix: &[u8] = b"tag:\0\x04";
        let cases: [(&str, Vec<u8>); 5] = [
            (
                "k too large",
                pack((0, 0), 200, 0, [ok_prefix, b"", b"", b""]),
            ),
            (
                "hdr_len past prefix",
                pack((0, 0), K.into(), 99, [ok_prefix, b"", b"", b""]),
            ),
            (
                "σ table too large",
                pack((0, 1 << 20), 30, 4, [ok_prefix, b"", b"", b""]),
            ),
            (
                "fixed idx trailing bytes",
                pack((0, 0), K.into(), 4, [ok_prefix, b"", b"\0", b""]),
            ),
            (
                "σ trailing bytes",
                pack((0, 0), K.into(), 4, [ok_prefix, b"", b"", b"\x01"]),
            ),
        ];
        for (what, buf) in cases {
            assert!(decode(&buf).is_err(), "{what}: decoder accepted it");
        }
    }

    #[test]
    fn decode_rejects_section_bomb() {
        let mut buf = MAGIC.to_vec();
        buf.push(Backend::Zstd as u8);
        for v in [0, 0, u64::from(K), 0] {
            put_varint(&mut buf, v);
        }
        put_varint(&mut buf, 1 << 40); // claims a 1 TB section
        put_varint(&mut buf, 1);
        buf.push(0);
        assert!(decode(&buf).is_err());
    }
}
