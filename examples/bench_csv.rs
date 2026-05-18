//! Benchmark data exporter for whitepaper figures.
//!
//! Runs the same measurement loops as `tests/complexity.rs` but emits
//! CSV data to `docs/paper/figures/data/` for pgfplots consumption.
//!
//! # Usage
//!
//! ```text
//! cargo run --example bench_csv --release
//! ```
//!
//! Produces:
//! - `docs/paper/figures/data/inclusion_proof.csv`
//! - `docs/paper/figures/data/consistency_proof.csv`

use std::fs;
use std::io::Write;
use std::sync::Arc;

use cpu_time::ThreadTime;
use sha2::{Digest, Sha256};
use tsml::{Hasher, Log, MemoryStorage};

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

    fn digest_len(&self) -> usize {
        32
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
fn make_log(n: usize) -> Arc<Log<MemoryStorage>> {
    let mut log = Log::new(MemoryStorage::new());
    log.add_algorithm(0, Box::new(Sha256Hasher)).unwrap();
    for i in 0..n {
        log.append(&(i as u64).to_le_bytes()).unwrap();
    }
    Arc::new(log)
}

// ---------------------------------------------------------------------------
// Benchmark runners
// ---------------------------------------------------------------------------

const TRIALS: usize = 31; // odd for clean median
const WARMUP: usize = 5; // discarded warmup iterations

/// Measure inclusion proof generation time across tree sizes.
fn bench_inclusion(sizes: &[usize]) -> Vec<(usize, u128, u128, u128)> {
    let mut data = Vec::with_capacity(sizes.len());
    for &n in sizes {
        let log = make_log(n);
        let ts = log.tree_size(0).unwrap();
        let leaf = ts / 2; // midpoint for maximal depth

        // Warmup
        for _ in 0..WARMUP {
            let _ = log.inclusion_proof(0, leaf).unwrap();
        }

        let mut times = Vec::with_capacity(TRIALS);
        for _ in 0..TRIALS {
            let start = ThreadTime::now();
            let _ = log.inclusion_proof(0, leaf).unwrap();
            times.push(start.elapsed().as_nanos());
        }
        times.sort_unstable();

        let p25 = percentile(&times, 25.0);
        let p50 = percentile(&times, 50.0);
        let p75 = percentile(&times, 75.0);

        data.push((n, p25, p50, p75));
        eprintln!("  inclusion  n={n:>8}  p25={p25}  p50={p50}  p75={p75} ns");
    }
    data
}

/// Measure consistency proof generation time across tree sizes.
///
/// For each tree size, samples `old_size` from five split points
/// {n/4, n/3, n/2, 2n/3, 3n/4} to avoid biasing toward the easiest
/// (power-of-two bisection) case. Reports the median across all
/// split points and trials.
fn bench_consistency(sizes: &[usize]) -> Vec<(usize, u128, u128, u128)> {
    let mut data = Vec::with_capacity(sizes.len());
    for &n in sizes {
        let log = make_log(n);
        let ts = log.tree_size(0).unwrap();

        // Diversified split points.
        let splits: Vec<u64> = [4, 3, 2, 3, 4]
            .iter()
            .zip([1, 1, 1, 2, 3].iter())
            .map(|(&denom, &numer)| (ts * numer) / denom)
            .filter(|&s| s > 0 && s < ts)
            .collect();

        // Warmup across all splits.
        for &old in &splits {
            for _ in 0..WARMUP {
                let _ = log.consistency_proof(0, old).unwrap();
            }
        }

        // Measure: TRIALS per split point, collect all timings.
        let mut times = Vec::with_capacity(TRIALS * splits.len());
        for &old in &splits {
            for _ in 0..TRIALS {
                let start = ThreadTime::now();
                let _ = log.consistency_proof(0, old).unwrap();
                times.push(start.elapsed().as_nanos());
            }
        }
        times.sort_unstable();

        let p25 = percentile(&times, 25.0);
        let p50 = percentile(&times, 50.0);
        let p75 = percentile(&times, 75.0);

        data.push((n, p25, p50, p75));
        eprintln!(
            "  consistency  n={n:>8}  splits={}  p25={p25}  p50={p50}  p75={p75} ns",
            splits.len()
        );
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

    eprintln!("Benchmarking consistency proofs ({TRIALS} trials, {WARMUP} warmup)...");
    let consistency = bench_consistency(&sizes);
    write_csv(&format!("{out_dir}/consistency_proof.csv"), &consistency);

    eprintln!("Done.");
}
