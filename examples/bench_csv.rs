//! Benchmark data exporter for whitepaper figures.
//!
//! Measures append, inclusion-proof, consistency-proof, root-extraction,
//! and proof-size across tree sizes and emits CSV files to
//! `docs/paper/figures/data/` for pgfplots consumption.
//!
//! # Usage
//!
//! ```text
//! cargo run -p eml-examples --bin bench_csv --release
//! ```
//!
//! Produces:
//! - `docs/paper/figures/data/append.csv`
//! - `docs/paper/figures/data/inclusion_proof.csv`
//! - `docs/paper/figures/data/consistency_proof.csv`
//! - `docs/paper/figures/data/root.csv`
//! - `docs/paper/figures/data/proof_sizes.csv`

use std::fs;
use std::io::Write;

use cpu_time::ThreadTime;
use eml::{Hasher, MemoryStorage, NaryMerkleLog, TreeConfig};
use sha2::{Digest, Sha256};

// ---------------------------------------------------------------------------
// Test hasher — matches tests/complexity.rs
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
struct Sha256Hasher;

impl Hasher for Sha256Hasher {
    fn leaf(&self, data: &[u8]) -> Vec<u8> {
        Sha256::digest(data).to_vec()
    }

    fn node(&self, children: &[&[u8]]) -> Vec<u8> {
        let mut h = Sha256::new();
        for c in children {
            h.update(c);
        }
        h.finalize().to_vec()
    }

    fn empty(&self) -> Vec<u8> {
        Sha256::digest(b"").to_vec()
    }

    fn hash(&self, data: &[u8]) -> Vec<u8> {
        Sha256::digest(data).to_vec()
    }

    fn clone_box(&self) -> Box<dyn Hasher> {
        Box::new(self.clone())
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn percentile(sorted: &[u128], pct: f64) -> u128 {
    let idx = ((sorted.len() as f64 - 1.0) * pct / 100.0).round() as usize;
    sorted[idx.min(sorted.len() - 1)]
}

fn make_log(n: usize) -> NaryMerkleLog<MemoryStorage> {
    smol::block_on(async {
        let mut log = NaryMerkleLog::new(
            MemoryStorage::new(),
            Box::new(Sha256Hasher),
            TreeConfig { arity: 2 },
        )
        .await
        .unwrap();
        for i in 0..n {
            log.append_leaf(&(i as u64).to_le_bytes()).await.unwrap();
        }
        log
    })
}

fn write_csv(path: &str, header: &str, rows: &str) {
    let mut f = fs::File::create(path).expect("failed to create CSV");
    writeln!(f, "{header}").unwrap();
    f.write_all(rows.as_bytes()).unwrap();
    eprintln!("  wrote {path}");
}

// ---------------------------------------------------------------------------
// Benchmark runner
// ---------------------------------------------------------------------------

const TRIALS: usize = 31; // odd for clean median
const WARMUP: usize = 5; // discarded

/// Measure a repeated closure `f`, returning (p25, p50, p75) in ns.
fn bench<F: Fn()>(f: F) -> (u128, u128, u128) {
    for _ in 0..WARMUP {
        f();
    }
    let mut times = Vec::with_capacity(TRIALS);
    for _ in 0..TRIALS {
        let start = ThreadTime::now();
        f();
        times.push(start.elapsed().as_nanos());
    }
    times.sort_unstable();
    (
        percentile(&times, 25.0),
        percentile(&times, 50.0),
        percentile(&times, 75.0),
    )
}

// ---------------------------------------------------------------------------
// Per-operation benchmarks
// ---------------------------------------------------------------------------

/// Amortized append: build a log of size `n`, then time a batch of 100
/// additional appends, reporting per-append ns.
fn bench_append(sizes: &[usize]) -> String {
    const BATCH: usize = 100;
    let mut out = String::new();
    for &n in sizes {
        // Trials measured over independent fresh logs so memory state is
        // representative of a real log at that size.
        let mut raw: Vec<u128> = Vec::with_capacity(TRIALS + WARMUP);
        for _ in 0..(TRIALS + WARMUP) {
            smol::block_on(async {
                let mut log = NaryMerkleLog::new(
                    MemoryStorage::new(),
                    Box::new(Sha256Hasher),
                    TreeConfig { arity: 2 },
                )
                .await
                .unwrap();
                for i in 0..n {
                    log.append_leaf(&(i as u64).to_le_bytes()).await.unwrap();
                }
                let start = ThreadTime::now();
                for i in n..(n + BATCH) {
                    log.append_leaf(&(i as u64).to_le_bytes()).await.unwrap();
                }
                raw.push(start.elapsed().as_nanos());
            });
        }
        raw.drain(0..WARMUP);
        raw.sort_unstable();
        let p25 = percentile(&raw, 25.0) / BATCH as u128;
        let p50 = percentile(&raw, 50.0) / BATCH as u128;
        let p75 = percentile(&raw, 75.0) / BATCH as u128;
        eprintln!("  append  n={n:>8}  p25={p25}  p50={p50}  p75={p75} ns/op");
        out.push_str(&format!("{n},{p25},{p50},{p75}\n"));
    }
    out
}

/// Inclusion-proof generation time across tree sizes.
fn bench_inclusion(sizes: &[usize]) -> String {
    let mut out = String::new();
    for &n in sizes {
        let log = make_log(n);
        let mid = (n / 2) as u64;
        let (p25, p50, p75) = bench(|| {
            smol::block_on(async {
                let _ = log.inclusion_proof(mid, n as u64).await.unwrap();
            });
        });
        eprintln!("  inclusion  n={n:>8}  p25={p25}  p50={p50}  p75={p75} ns");
        out.push_str(&format!("{n},{p25},{p50},{p75}\n"));
    }
    out
}

/// Consistency-proof generation time (from n/2 to n).
fn bench_consistency(sizes: &[usize]) -> String {
    let mut out = String::new();
    for &n in sizes {
        let log = make_log(n);
        let half = (n / 2) as u64;
        let full = n as u64;
        let (p25, p50, p75) = bench(|| {
            smol::block_on(async {
                let _ = log.consistency_proof(half, full).await.unwrap();
            });
        });
        eprintln!("  consistency  n={n:>8}  p25={p25}  p50={p50}  p75={p75} ns");
        out.push_str(&format!("{n},{p25},{p50},{p75}\n"));
    }
    out
}

/// Root-extraction time.
fn bench_root(sizes: &[usize]) -> String {
    let mut out = String::new();
    for &n in sizes {
        let log = make_log(n);
        let (p25, p50, p75) = bench(|| {
            let _ = log.root();
        });
        eprintln!("  root  n={n:>8}  p25={p25}  p50={p50}  p75={p75} ns");
        out.push_str(&format!("{n},{p25},{p50},{p75}\n"));
    }
    out
}

/// Proof path lengths (number of proof steps) at each tree size.
fn measure_proof_sizes(sizes: &[usize]) -> String {
    let mut out = String::new();
    for &n in sizes {
        let log = make_log(n);
        let mid = (n / 2) as u64;
        let half = mid;
        let full = n as u64;

        let inc_steps = smol::block_on(async {
            log.inclusion_proof(mid, full)
                .await
                .unwrap()
                .map_or(0, |p| p.path.len())
        });
        let con_steps = smol::block_on(async {
            log.consistency_proof(half, full)
                .await
                .unwrap()
                .map_or(0, |p| p.path.len())
        });
        eprintln!("  proof_sizes  n={n:>8}  inclusion={inc_steps}  consistency={con_steps}");
        out.push_str(&format!("{n},{inc_steps},{con_steps}\n"));
    }
    out
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

fn main() {
    // Powers of 2 from 2^4 (16) to 2^20 (~1M leaves).
    // 2^24 would take many minutes; 2^20 is sufficient to establish slopes.
    let sizes: Vec<usize> = (4..=20).map(|e| 1usize << e).collect();

    let out_dir = "docs/paper/figures/data";
    fs::create_dir_all(out_dir).expect("failed to create output directory");

    let hdr3 = "n,p25_ns,median_ns,p75_ns";

    eprintln!("Benchmarking append ({TRIALS} trials, {WARMUP} warmup)...");
    let data = bench_append(&sizes);
    write_csv(&format!("{out_dir}/append.csv"), hdr3, &data);

    eprintln!("Benchmarking inclusion proofs...");
    let data = bench_inclusion(&sizes);
    write_csv(&format!("{out_dir}/inclusion_proof.csv"), hdr3, &data);

    eprintln!("Benchmarking consistency proofs...");
    let data = bench_consistency(&sizes);
    write_csv(&format!("{out_dir}/consistency_proof.csv"), hdr3, &data);

    eprintln!("Benchmarking root extraction...");
    let data = bench_root(&sizes);
    write_csv(&format!("{out_dir}/root.csv"), hdr3, &data);

    eprintln!("Measuring proof sizes...");
    let data = measure_proof_sizes(&sizes);
    write_csv(
        &format!("{out_dir}/proof_sizes.csv"),
        "n,inclusion_steps,consistency_steps",
        &data,
    );

    eprintln!("Done.");
}
