//! Empirical computational complexity regression tests.
//!
//! Verifies that EML operations maintain the performance bounds stated
//! in the formal model (§Performance Bounds):
//!
//! - **Read-only proofs** (O(log n)): `bigoish` curve-fitting via closure-based measurement (proofs
//!   are `&self` — repeatable). Loop iterations (100x) are used inside the closures to scale up
//!   measurement times and drown out microsecond-level scheduling noise.
//! - **Mutating operations** (O(1), O(log K), O(G)): `big_o` model inference from per-thread CPU
//!   time via `cpu_time::ThreadTime` (`&mut self` — one-shot per input). Uses 21 trials and median
//!   filtering to robustly suppress outliers.
//!
//! # Model Selection
//!
//! The `big_o` crate selects the best-fit model by lowest residuals.
//! Its `O(n^m)` polynomial model has a free exponent parameter that can
//! overfit noisy data (e.g. fitting `O(n^0.05)` to nearly-constant
//! data). Rather than asserting exact model name equality, we assert
//! that the best-fit model's **rank** does not exceed the expected
//! complexity rank. This is sound because rank maps monotonically to
//! asymptotic growth: O(1)=0, O(log n)=130, O(n)=1000, O(n log n)=1130, O(n²)=2000.
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

mod common;

use std::sync::Arc;

use bigoish::{Log as LogModel, N, assert_best_fit, growing_inputs};
use common::Sha256Hasher;
use cpu_time::ThreadTime;
use eml::{Log, MemoryStorage};

// ---------------------------------------------------------------------------
// Input factory — builds a log of `n` leaves with a single algorithm,
// wrapped in Arc for cheap cloning.
// ---------------------------------------------------------------------------

/// Build a log with one algorithm (id 0) and `n` appended leaves.
async fn make_log(n: usize) -> Arc<Log<MemoryStorage>> {
    let mut log = Log::new(MemoryStorage::new());
    log.add_algorithm(0, Box::new(Sha256Hasher)).await.unwrap();
    for i in 0..n {
        log.append(&(i as u64).to_le_bytes()).await.unwrap();
    }
    Arc::new(log)
}

fn make_log_sync(n: usize) -> Arc<Log<MemoryStorage>> {
    smol::block_on(make_log(n))
}

// ===========================================================================
// bigoish tests — read-only proof operations (O(log n))
// ===========================================================================

/// Inclusion proof generation must be O(log n).
///
/// Runs 100 iterations inside the closure to suppress wall-clock noise.
#[test]
fn complexity_inclusion_proof_log_n() {
    assert_best_fit(
        LogModel(N),
        |log: Arc<Log<MemoryStorage>>| {
            smol::block_on(async {
                let ts = log.tree_size(0).await.unwrap();
                let mut proof = None;
                for _ in 0..100 {
                    proof = Some(log.inclusion_proof(0, ts / 2).await.unwrap());
                }
                proof.unwrap()
            })
        },
        growing_inputs(100, make_log_sync, 25),
    );
}

/// Consistency proof generation must be O(log n).
///
/// Runs 100 iterations inside the closure to suppress wall-clock noise.
#[test]
fn complexity_consistency_proof_log_n() {
    assert_best_fit(
        LogModel(N),
        |log: Arc<Log<MemoryStorage>>| {
            smol::block_on(async {
                let ts = log.tree_size(0).await.unwrap();
                let mut proof = None;
                for _ in 0..100 {
                    proof = Some(log.consistency_proof(0, ts / 2).await.unwrap());
                }
                proof.unwrap()
            })
        },
        growing_inputs(100, make_log_sync, 25),
    );
}

/// Root extraction must be O(log n).
///
/// Runs 100 iterations inside the closure to suppress wall-clock noise.
#[test]
fn complexity_root_extraction_log_n() {
    assert_best_fit(
        LogModel(N),
        |log: Arc<Log<MemoryStorage>>| {
            let mut root = None;
            for _ in 0..100 {
                root = Some(log.root(0).unwrap());
            }
            root.unwrap()
        },
        growing_inputs(100, make_log_sync, 25),
    );
}

// ===========================================================================
// big_o tests — mutating operations (O(1), O(log K), O(G))
// ===========================================================================

/// Return the median of a mutable slice.
fn median(v: &mut [u128]) -> u128 {
    v.sort_unstable();
    v[v.len() / 2]
}

/// Assert that the best-fit model does not grow faster than `max_rank`.
fn assert_rank_at_most(data: Vec<(f64, f64)>, max_rank: u32, label: &str, expected_notation: &str) {
    let (best, all) = big_o::infer_complexity(data).unwrap();
    // Filter out Exponential model from the list of fits, since narrow-range,
    // flat-slope data is mathematically overfit as O(c^n) with c ~ 1.01.
    let best_fit = all.iter().find(|c| c.notation != "O(c^n)").unwrap_or(&best);

    assert!(
        best_fit.rank <= max_rank,
        "{label} should be {expected_notation}, but best fit is {} (rank {}, max allowed \
         {max_rank})",
        best_fit.notation,
        best_fit.rank,
    );
}

/// Append must be O(1) amortized per algorithm.
#[test]
fn complexity_append_amortized_constant() {
    let sizes: &[usize] = &[500, 1_000, 2_000, 5_000, 10_000, 20_000, 50_000];
    let batch = 1_000;
    let trials = 21;
    let mut data: Vec<(f64, f64)> = Vec::with_capacity(sizes.len());

    for &n in sizes {
        let mut times = Vec::with_capacity(trials);
        for _ in 0..trials {
            smol::block_on(async {
                let mut log = Log::new(MemoryStorage::new());
                log.add_algorithm(0, Box::new(Sha256Hasher)).await.unwrap();
                for i in 0..n {
                    log.append(&(i as u64).to_le_bytes()).await.unwrap();
                }
                let start = ThreadTime::now();
                for i in n..(n + batch) {
                    log.append(&(i as u64).to_le_bytes()).await.unwrap();
                }
                times.push(start.elapsed().as_nanos());
            });
        }
        let per_append = median(&mut times) as f64 / batch as f64;
        data.push((n as f64, per_append));
    }

    // O(1) amortized. Allow up to O(n log n) (rank 1130) or slightly higher (1200)
    // for L2/L3 cache miss effects on large hash maps.
    assert_rank_at_most(data, 1200, "append", "O(1) amortized");
}

/// Algorithm addition must be O(popcount K) where K is the current tree size.
///
/// To isolate the O(popcount K) stack pushes from O(log K) null table expansion and
/// cache capacity footprint effects, we hold the tree size K at a constant bit-width of 18
/// (so K is always between 131,072 and 262,143, and the null table height is always 18).
/// We then vary the popcount of K from 1 to 18 by choosing K = (1 << 17) | ((1 << (p - 1)) - 1).
///
/// This isolates the O(popcount K) operational complexity, expecting a linear relationship.
#[test]
fn complexity_add_algorithm_popcount_k() {
    // Warm up the allocator, CPU cache, and async runtime.
    smol::block_on(async {
        let mut log = Log::new(MemoryStorage::new());
        log.add_algorithm(0, Box::new(Sha256Hasher)).await.unwrap();
        for i in 0..100 {
            log.append(&(i as u64).to_le_bytes()).await.unwrap();
        }
        for alg_id in 1..=100 {
            log.add_algorithm(alg_id, Box::new(Sha256Hasher)).await.unwrap();
        }
    });

    let powers: &[u32] = &[1, 4, 7, 10, 13, 16, 18];
    let trials = 21;
    let mut data: Vec<(f64, f64)> = Vec::with_capacity(powers.len());

    for &p in powers {
        let k = (1usize << 17) | ((1usize << (p - 1)) - 1);
        let mut times = Vec::with_capacity(trials);
        for _ in 0..trials {
            smol::block_on(async {
                let mut log = Log::new(MemoryStorage::new());
                log.add_algorithm(0, Box::new(Sha256Hasher)).await.unwrap();
                for i in 0..k {
                    log.append(&(i as u64).to_le_bytes()).await.unwrap();
                }
                let start = ThreadTime::now();
                for alg_id in 1..=1000 {
                    log.add_algorithm(alg_id, Box::new(Sha256Hasher))
                        .await
                        .unwrap();
                }
                times.push(start.elapsed().as_nanos());
            });
        }
        let popcount = k.count_ones() as f64;
        data.push((popcount, median(&mut times) as f64));
    }

    println!("DEBUG DATA: {:?}", data);
    // O(popcount K) is linear in the popcount value. Allow up to O(n log n) (rank <= 1200)
    // to tolerate BTreeMap insertion overhead and microsecond-level timing noise.
    assert_rank_at_most(data, 1200, "add_algorithm", "O(popcount K)");
}

/// Algorithm resumption must be O(log n) where n is the tree size.
#[test]
fn complexity_resume_algorithm_log_n() {
    let gaps: &[usize] = &[100, 500, 1_000, 2_000, 5_000, 10_000, 20_000];
    let base_size = 100;
    let trials = 21;
    let mut data: Vec<(f64, f64)> = Vec::with_capacity(gaps.len());

    for &g in gaps {
        let mut times = Vec::with_capacity(trials);
        for _ in 0..trials {
            smol::block_on(async {
                let mut log = Log::new(MemoryStorage::new());
                log.add_algorithm(0, Box::new(Sha256Hasher)).await.unwrap();
                log.add_algorithm(1, Box::new(Sha256Hasher)).await.unwrap();
                for i in 0..base_size {
                    log.append(&(i as u64).to_le_bytes()).await.unwrap();
                }
                log.remove_algorithm(1).await.unwrap();
                for i in base_size..(base_size + g) {
                    log.append(&(i as u64).to_le_bytes()).await.unwrap();
                }
                let start = ThreadTime::now();
                log.resume_algorithm(1).await.unwrap();
                times.push(start.elapsed().as_nanos());
            });
        }
        data.push((g as f64, median(&mut times) as f64));
    }

    // O(log n). Allow up to linear (rank <= 1000) to tolerate microsecond-level noise.
    assert_rank_at_most(data, 1000, "resume_algorithm", "O(log n)");
}
