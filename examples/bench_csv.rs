//! Benchmark data exporter for whitepaper figures.
//!
//! Measures inclusion proof generation time and emits CSV data to
//! `docs/paper/figures/data/` for pgfplots consumption.
//!
//! # Usage
//!
//! ```text
//! cargo run --example bench_csv --release
//! ```
//!
//! Produces:
//! - `docs/paper/figures/data/inclusion_proof.csv`

use std::fs;
use std::io::Write;
use std::sync::Arc;

use cpu_time::ThreadTime;
use eml::{Hasher, Log, MemoryStorage};
use sha2::{Digest, Sha256};

// ---------------------------------------------------------------------------
// Test hasher — identical to tests/complexity.rs
// ---------------------------------------------------------------------------

#[derive(Debug)]
struct Sha256Hasher;

impl Hasher for Sha256Hasher {
    fn leaf(&self, data: &[u8]) -> Vec<u8> {
        let mut h = Sha256::new();
        h.update([0x00]);
        h.update(data);
        h.finalize().to_vec()
    }

    fn node(&self, left: &[u8], right: &[u8]) -> Vec<u8> {
        let mut h = Sha256::new();
        h.update([0x01]);
        h.update(left);
        h.update(right);
        h.finalize().to_vec()
    }

    fn empty(&self) -> Vec<u8> {
        Sha256::digest(b"").to_vec()
    }

    fn null(&self) -> Vec<u8> {
        Sha256::digest([0x02]).to_vec()
    }

    fn hash(&self, data: &[u8]) -> Vec<u8> {
        Sha256::digest(data).to_vec()
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn percentile(sorted: &[u128], pct: f64) -> u128 {
    let idx = ((sorted.len() as f64 - 1.0) * pct / 100.0).round() as usize;
    sorted[idx.min(sorted.len() - 1)]
}

/// Build a log with one algorithm (id 0) and `n` appended leaves.
async fn make_log(n: usize) -> Arc<Log<MemoryStorage>> {
    let mut log = Log::new(MemoryStorage::new());
    log.add_algorithm(0, Box::new(Sha256Hasher)).await.unwrap();
    for i in 0..n {
        log.append(&(i as u64).to_le_bytes()).await.unwrap();
    }
    Arc::new(log)
}

// ---------------------------------------------------------------------------
// Benchmark runner
// ---------------------------------------------------------------------------

const TRIALS: usize = 31; // odd for clean median
const WARMUP: usize = 5; // discarded warmup iterations

/// Measure inclusion proof generation time across tree sizes.
fn bench_inclusion(sizes: &[usize]) -> Vec<(usize, u128, u128, u128)> {
    let mut data = Vec::with_capacity(sizes.len());
    for &n in sizes {
        smol::block_on(async {
            let log = make_log(n).await;
            let ts = log.tree_size(0).await.unwrap();
            let leaf = ts / 2; // midpoint for maximal depth

            // Warmup
            for _ in 0..WARMUP {
                let _ = log.inclusion_proof(0, leaf).await.unwrap();
            }

            let mut times = Vec::with_capacity(TRIALS);
            for _ in 0..TRIALS {
                let start = ThreadTime::now();
                let _ = log.inclusion_proof(0, leaf).await.unwrap();
                times.push(start.elapsed().as_nanos());
            }
            times.sort_unstable();

            let p25 = percentile(&times, 25.0);
            let p50 = percentile(&times, 50.0);
            let p75 = percentile(&times, 75.0);

            data.push((n, p25, p50, p75));
            eprintln!("  inclusion  n={n:>8}  p25={p25}  p50={p50}  p75={p75} ns");
        });
    }
    data
}

/// Write data to CSV with error bar columns.
fn write_csv(path: &str, data: &[(usize, u128, u128, u128)]) {
    let mut f = fs::File::create(path).expect("failed to create CSV");
    writeln!(f, "n,p25_ns,median_ns,p75_ns").unwrap();
    for &(n, p25, p50, p75) in data {
        writeln!(f, "{n},{p25},{p50},{p75}").unwrap();
    }
    eprintln!("  wrote {path}");
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

fn main() {
    // Tree sizes: powers of 2 from 2^4 to 2^24
    let sizes: Vec<usize> = (4..=24).map(|e| 1 << e).collect();

    let out_dir = "docs/paper/figures/data";
    fs::create_dir_all(out_dir).expect("failed to create output directory");

    eprintln!("Benchmarking inclusion proofs ({TRIALS} trials, {WARMUP} warmup)...");
    let inclusion = bench_inclusion(&sizes);
    write_csv(&format!("{out_dir}/inclusion_proof.csv"), &inclusion);

    eprintln!("Done.");
}
