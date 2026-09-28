# pk-codec

Spike: a lossless, structure-aware encoding for Midnight prover keys.

A prover key is mostly two tables of 32-byte field elements that look random
to gzip but are not:

- **Permutation `σ`** - each entry is `δ^c·ω^r`, i.e. just a cell position.
  Stored as `position - own position` (0 for the ~90% of unwired cells).
- **Fixed columns** - a few thousand distinct constants repeated across
  hundreds of thousands of cells. Stored as a dictionary plus indices.

Everything else (ledger header, IR, verifier key) is kept verbatim. Decoding
reproduces the original `.prover` file byte for byte.

## Results

Built-in keys, ledger v9/v10 (`midnight-proofs` 0.7 layout):

| Key          | Today (gzip) | New + zstd | Smaller | Decode |
| ------------ | ------------ | ---------- | ------- | ------ |
| dust/spend   | 2.18 MB      | 0.028 MB   | 77x     | 3 ms   |
| zswap/sign   | 2.81 MB      | 0.25 MB    | 11x     | 4 ms   |
| zswap/output | 5.73 MB      | 0.26 MB    | 22x     | 10 ms  |
| zswap/spend  | 11.02 MB     | 0.26 MB    | 42x     | 16 ms  |

zstd on the raw key gains only 2-4% over gzip. The transform is what matters;
the outer compressor is interchangeable (gzip-6 lands within ~10%).

## Usage

```sh
cargo run --release -- ~/.cache/midnight/zk-params/zswap/9/*.prover
PKC_BACKEND=gzip|store  # inner section compressor (default zstd)
PKC_STATS=1             # trivial columns, gunzip vs decode, load-FFT cost
```

Each run encodes, decodes and checks the round trip is byte-exact.

## Limits

- Spike, not a library. Only the `midnight-proofs` 0.7 layout; ledger-v6-era
  keys are rejected.
- Untested on large (90-570 MB) contract keys.
- Decoder bounds every declared size, but is not fuzzed yet, and builds the
  full `δ^c·ω^r` table (a streaming decoder needs O(√n) memory).
