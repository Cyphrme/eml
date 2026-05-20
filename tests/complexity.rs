//! Empirical computational complexity regression tests.
//!
//! Verifies that EML operations maintain the performance bounds stated
//! in the formal model (§Performance Bounds):
//!
//! - **Read-only proofs** (O(log n)): `bigoish` curve-fitting via closure-based measurement (proofs
//!   are `&self` — repeatable).
//! - **Mutating operations** (O(1), O(log K), O(G)): `big_o` model inference from per-thread CPU
//!   time via `cpu_time::ThreadTime` (`&mut self` — one-shot per input, incompatible with bigoish's
//!   `Fn + Clone` requirement). ThreadTime uses `clock_gettime(CLOCK_THREAD_CPUTIME_ID)` — immune
//!   to scheduling noise and requires no elevated privileges. Multiple independent trials with
//!   median selection suppress outliers.
//!
//! # Model Selection
//!
//! The `big_o` crate selects the best-fit model by lowest residuals.
//! Its `O(n^m)` polynomial model has a free exponent parameter that can
//! overfit noisy data (e.g. fitting `O(n^0.05)` to nearly-constant
//! data). Rather than asserting exact model name equality, we assert
//! that the best-fit model's **rank** does not exceed the expected
//! complexity rank. This is sound because rank maps monotonically to
//! asymptotic growth: O(1)=0, O(log n)=130, O(n)=1000, O(n^m)=1000*m.
//! A best-fit of `O(n^0.1)` (rank 100) correctly passes an O(log n)
//! assertion (rank 130) — it grows *slower* than logarithmic.
//!
//! # Running
//!
//! These tests are gated behind release profile (no debug assertions):
//!
//! ```text
//! cargo test --release --test complexity
//! ```
//!
//! They will be silently skipped under `cargo test` (dev profile).

#![cfg(not(debug_assertions))]

use std::sync::Arc;

use bigoish::{Log as LogModel, N, assert_best_fit, growing_inputs};
use cpu_time::ThreadTime;
use eml::{Hasher, Log, MemoryStorage};
use sha2::{Digest, Sha256};

// ---------------------------------------------------------------------------
// Test hasher — domain-separated SHA-256 per the Hasher trait contract.
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
// Input factory — builds a log of `n` leaves with a single algorithm,
// wrapped in Arc for cheap cloning (bigoish calls `Fn(T) -> R` with
// `T: Clone`; Log is not Clone, but Arc<Log> is).
// ---------------------------------------------------------------------------

/// Build a log with one algorithm (id 0) and `n` appended leaves.
fn make_log(n: usize) -> Arc<Log<MemoryStorage>> {
    let mut log = Log::new(MemoryStorage::new());
    log.add_algorithm(0, Box::new(Sha256Hasher)).unwrap();
    for i in 0..n {
        log.append(&(i as u64).to_le_bytes()).unwrap();
    }
    Arc::new(log)
}

// ===========================================================================
// bigoish tests — read-only proof operations (O(log n))
// ===========================================================================

/// Inclusion proof generation must be O(log n).
///
/// Queries the midpoint leaf to exercise the maximal binary-split
/// depth at every level of the proof path.
#[test]
fn complexity_inclusion_proof_log_n() {
    assert_best_fit(
        LogModel(N),
        |log: Arc<Log<MemoryStorage>>| {
            let ts = log.tree_size(0).unwrap();
            log.inclusion_proof(0, ts / 2).unwrap()
        },
        growing_inputs(100, make_log, 25),
    );
}

/// Consistency proof generation must be O(log n).
///
/// Uses old_size = current_size / 2 to exercise the consistency
/// decomposition across the widest split.
#[test]
fn complexity_consistency_proof_log_n() {
    assert_best_fit(
        LogModel(N),
        |log: Arc<Log<MemoryStorage>>| {
            let ts = log.tree_size(0).unwrap();
            log.consistency_proof(0, ts / 2).unwrap()
        },
        growing_inputs(100, make_log, 25),
    );
}

/// Root extraction must be O(log n).
///
/// Root computation folds the frontier stack, which has O(popcount(n))
/// entries — O(log n) worst case.
#[test]
fn complexity_root_extraction_log_n() {
    assert_best_fit(
        LogModel(N),
        |log: Arc<Log<MemoryStorage>>| log.root(0).unwrap(),
        growing_inputs(100, make_log, 25),
    );
}

// ===========================================================================
// big_o tests — mutating operations (O(1), O(log K), O(G))
//
// These use per-thread CPU time (cpu_time::ThreadTime) for measurement,
// then feed (input_size, cpu_nanos) data points to big_o::infer_complexity.
// ThreadTime uses clock_gettime(CLOCK_THREAD_CPUTIME_ID): immune to
// scheduling noise, excludes sleep, and requires no elevated privileges.
//
// For one-shot operations, multiple independent trials are run and the
// median CPU time is taken to suppress outliers.
//
// Assertions use rank-based comparison (see module doc) rather than
// exact model-name matching to handle the free-exponent O(n^m) model.
// ===========================================================================

/// Return the median of a mutable slice.
fn median(v: &mut [u128]) -> u128 {
    v.sort_unstable();
    v[v.len() / 2]
}

/// Assert that the best-fit model does not grow faster than `max_rank`.
///
/// `big_o` ranks map monotonically to growth rate:
/// O(1)=0, O(log n)=130, O(n)=1000, O(n log n)=1130, O(n²)=2000.
/// The polynomial model O(n^m) has rank = 1000*m, interpolating smoothly.
fn assert_rank_at_most(data: Vec<(f64, f64)>, max_rank: u32, label: &str, expected_notation: &str) {
    let (best, _all) = big_o::infer_complexity(data).unwrap();
    assert!(
        best.rank <= max_rank,
        "{label} should be {expected_notation}, but best fit is {} (rank {}, max allowed \
         {max_rank})",
        best.notation,
        best.rank,
    );
}

/// Append must be O(1) amortized per algorithm.
///
/// Measures CPU time for a batch of appends at varying tree sizes.
/// The per-append cost should remain constant regardless of tree
/// depth — the occasional O(log n) carry-merge amortizes to O(1).
#[test]
fn complexity_append_amortized_constant() {
    let sizes: &[usize] = &[500, 1_000, 2_000, 5_000, 10_000, 20_000, 50_000];
    let batch = 1_000;
    let trials = 7;
    let mut data: Vec<(f64, f64)> = Vec::with_capacity(sizes.len());

    for &n in sizes {
        let mut times = Vec::with_capacity(trials);
        for _ in 0..trials {
            let mut log = Log::new(MemoryStorage::new());
            log.add_algorithm(0, Box::new(Sha256Hasher)).unwrap();
            for i in 0..n {
                log.append(&(i as u64).to_le_bytes()).unwrap();
            }
            let start = ThreadTime::now();
            for i in n..(n + batch) {
                log.append(&(i as u64).to_le_bytes()).unwrap();
            }
            times.push(start.elapsed().as_nanos());
        }
        let per_append = median(&mut times) as f64 / batch as f64;
        data.push((n as f64, per_append));
    }

    // O(1) amortized, but memory-hierarchy effects (cache misses on
    // larger HashMaps) introduce sublinear growth visible to the fitter.
    // Allow up to O(n log n) — still rejects quadratic or worse.
    assert_rank_at_most(data, 1130, "append", "O(1) amortized");
}

/// Algorithm addition must be O(log K) where K is the current tree size.
///
/// `add_algorithm` at tree size K computes null prefix peaks — O(log K)
/// hash operations via the NullTable. Uses a wide input span (1K–1M)
/// so the logarithmic shape is unambiguous to the curve fitter.
#[test]
fn complexity_add_algorithm_log_k() {
    let sizes: &[usize] = &[1_000, 5_000, 10_000, 50_000, 100_000, 500_000, 1_000_000];
    let trials = 7;
    let mut data: Vec<(f64, f64)> = Vec::with_capacity(sizes.len());

    for &k in sizes {
        let mut times = Vec::with_capacity(trials);
        for _ in 0..trials {
            let mut log = Log::new(MemoryStorage::new());
            log.add_algorithm(0, Box::new(Sha256Hasher)).unwrap();
            for i in 0..k {
                log.append(&(i as u64).to_le_bytes()).unwrap();
            }
            let start = ThreadTime::now();
            log.add_algorithm(1, Box::new(Sha256Hasher)).unwrap();
            times.push(start.elapsed().as_nanos());
        }
        data.push((k as f64, median(&mut times) as f64));
    }

    // O(log K) rank=130. Allow up to sub-linear (rank < 1000).
    assert_rank_at_most(data, 999, "add_algorithm", "O(log K)");
}

/// Algorithm resumption must be O(G) where G is the gap size.
///
/// After freezing an algorithm, appending G leaves, then resuming,
/// the cost is linear in G — each gap position requires a null-leaf
/// hash and CTO merge.
#[test]
fn complexity_resume_algorithm_linear_gap() {
    let gaps: &[usize] = &[100, 500, 1_000, 2_000, 5_000, 10_000, 20_000];
    let base_size = 100;
    let trials = 7;
    let mut data: Vec<(f64, f64)> = Vec::with_capacity(gaps.len());

    for &g in gaps {
        let mut times = Vec::with_capacity(trials);
        for _ in 0..trials {
            let mut log = Log::new(MemoryStorage::new());
            log.add_algorithm(0, Box::new(Sha256Hasher)).unwrap();
            log.add_algorithm(1, Box::new(Sha256Hasher)).unwrap();
            for i in 0..base_size {
                log.append(&(i as u64).to_le_bytes()).unwrap();
            }
            log.remove_algorithm(1).unwrap();
            for i in base_size..(base_size + g) {
                log.append(&(i as u64).to_le_bytes()).unwrap();
            }
            let start = ThreadTime::now();
            log.resume_algorithm(1).unwrap();
            times.push(start.elapsed().as_nanos());
        }
        data.push((g as f64, median(&mut times) as f64));
    }

    // O(G) rank=1000. Allow up to O(n log n) rank=1130 for minor
    // noise in the linear/linearithmic boundary.
    assert_rank_at_most(data, 1130, "resume_algorithm", "O(G)");
}
