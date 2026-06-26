//! Complexity-scaling regression tests.
//!
//! These tests infer asymptotic complexity from measured runtimes, so they
//! REQUIRE true serial execution:
//!
//! ```text
//! cargo test --release -p eml --test complexity -- --test-threads=1
//! ```
//!
//! (See `eml/tests/check_complexity.sh`.) Without it, `cargo test`'s default
//! parallelism runs sibling tests concurrently: even while one test holds its
//! timing loop, another test's `make_log` *setup* runs on a sibling thread and
//! contends for CPU, inflating the measured growth of the larger inputs enough
//! to flip an O(log n) fit to O(n log n). A mutex around the timing loops alone
//! does NOT fix this — the contending work is the setup outside any timed
//! section — so the whole suite must run one test at a time.
//!
//! The release profile is also required: the tests are gated on
//! `not(debug_assertions)`, so a debug `cargo test` compiles them to nothing.

#![cfg(not(debug_assertions))]

use std::sync::Arc;

use cpu_time::ThreadTime;
use eml::{Hasher, MemoryStorage, NaryMerkleLog, TreeConfig};
use sha2::{Digest, Sha256};

#[derive(Debug)]
struct Sha256Hasher;

impl Hasher for Sha256Hasher {
    fn leaf(&self, data: &[u8]) -> Vec<u8> {
        Sha256::digest(data).to_vec()
    }

    fn node(&self, children: &[&[u8]]) -> Vec<u8> {
        let mut h = Sha256::new();
        for child in children {
            h.update(child);
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
        Box::new(Sha256Hasher)
    }
}

fn make_log(n: usize) -> Arc<NaryMerkleLog<MemoryStorage>> {
    smol::block_on(async {
        let storage = MemoryStorage::new();
        let config = TreeConfig { arity: 2 };
        let mut log = NaryMerkleLog::new(storage, Box::new(Sha256Hasher), config)
            .await
            .unwrap();
        for i in 0..n {
            log.append_leaf(&(i as u64).to_le_bytes()).await.unwrap();
        }
        Arc::new(log)
    })
}

// Log-size scaling tests share one robust harness: the minimum `ThreadTime`
// over trials at each size (see `measure_log_scaling`), bounded by the measured
// growth ratio across the size range (`assert_growth_bounded`). `assert_best_
// fit` was abandoned here: its CPU-instruction-count backend times out on these
// fast (µs-scale) operations, and on a near-flat O(log n) curve its single best-
// fit verdict lands arbitrarily among the low-rank models — intermittently
// calling a near-zero-slope Linear the "best fit" even single-threaded. The
// growth ratio sidesteps the classifier: it asserts the one property that
// actually separates sub-linear from linear.
//
// The size range spans three orders of magnitude on purpose. An O(log n)
// operation grows only ~2x across it (the measured ratios are 1.4–1.9x), so its
// curve is nearly flat — distinguishable from linear *only* when n ranges
// widely enough that a true O(n) regression would blow up by ~1000x. Over a
// narrow range the flat log curve is within timing noise of a shallow linear
// fit; the wide range gives the growth ratio the leverage to keep the real
// O(log n) impls flat while still catching any linear regression.
const LOG_SIZES: &[usize] = &[1_000, 10_000, 50_000, 100_000, 500_000, 1_000_000];
const LOG_TRIALS: usize = 21;
/// Inner repetitions per timed sample, so a sub-µs op (`root()`) clears
/// `ThreadTime`'s clock granularity instead of rounding to zero.
const LOG_REPS: u128 = 100;
/// Max allowed slowest/fastest time ratio across the (1000x) size range. The
/// real O(log n) impls measure 1.4–1.9x; a linear regression would be ~1000x.
/// 4x leaves generous headroom for timing noise yet catches linear by ~250x.
const SUBLINEAR_GROWTH: f64 = 4.0;

/// Measure `op` over a `make_log`-built log at each `LOG_SIZES`, returning
/// `(size, minimum per-iteration ThreadTime ns)` pairs. `op` runs the timed
/// operation `LOG_REPS` times per sample so a single sub-µs call does not vanish
/// into clock granularity.
///
/// The estimator is the **minimum** across trials, not the median: timing noise
/// is one-sided — scheduler preemption and cache effects only ever *add* time —
/// so the fastest trial is the closest estimate of the true compute cost and
/// the most robust to transient machine load. A median still rides background
/// load up and occasionally fits a higher-rank model even single-threaded; the
/// minimum does not.
fn measure_log_scaling<F>(op: F) -> Vec<(f64, f64)>
where
    F: Fn(&NaryMerkleLog<MemoryStorage>),
{
    let mut data: Vec<(f64, f64)> = Vec::with_capacity(LOG_SIZES.len());
    for &n in LOG_SIZES {
        let log = make_log(n);
        let mut best = u128::MAX;
        for _ in 0..LOG_TRIALS {
            let start = ThreadTime::now();
            for _ in 0..LOG_REPS {
                op(&log);
            }
            best = best.min(start.elapsed().as_nanos() / LOG_REPS);
        }
        data.push((n as f64, best as f64));
    }
    data
}

#[test]
fn complexity_inclusion_proof_log_n() {
    let data = measure_log_scaling(|log| {
        let ts = log.size();
        let _ = smol::block_on(log.inclusion_proof(0, ts / 2)).unwrap();
    });
    assert_growth_bounded(&data, SUBLINEAR_GROWTH, "inclusion_proof");
}

#[test]
fn complexity_consistency_proof_log_n() {
    let data = measure_log_scaling(|log| {
        let ts = log.size();
        let _ = smol::block_on(log.consistency_proof(ts / 2, ts)).unwrap();
    });
    assert_growth_bounded(&data, SUBLINEAR_GROWTH, "consistency_proof");
}

#[test]
fn complexity_root_extraction_log_n() {
    let data = measure_log_scaling(|log| {
        let _ = log.root();
    });
    assert_growth_bounded(&data, SUBLINEAR_GROWTH, "root_extraction");
}

fn median(v: &mut [u128]) -> u128 {
    v.sort_unstable();
    v[v.len() / 2]
}

fn assert_rank_at_most(data: Vec<(f64, f64)>, max_rank: u32, label: &str, expected_notation: &str) {
    let (best, all) = big_o::infer_complexity(data).unwrap();
    let best_fit = all.iter().find(|c| c.notation != "O(c^n)").unwrap_or(&best);

    assert!(
        best_fit.rank <= max_rank,
        "{label} should be {expected_notation}, but best fit is {} (rank {}, max allowed \
         {max_rank})",
        best_fit.notation,
        best_fit.rank,
    );
}

/// Assert measured times grow by at most `max_factor` across the whole size
/// range (slowest / fastest). For an operation whose true growth is so shallow
/// it sits below the timing-noise floor, the measured curve is flat and model-
/// fitting (`assert_rank_at_most`) is unreliable — but bounded growth across a
/// 1000x size increase is exactly the property that separates sub-linear from
/// linear: a linear regression would grow ~1000x and fail, an O(log n) impl
/// grows by a small constant.
fn assert_growth_bounded(data: &[(f64, f64)], max_factor: f64, label: &str) {
    let times: Vec<f64> = data.iter().map(|&(_, t)| t).collect();
    let min = times.iter().copied().fold(f64::INFINITY, f64::min);
    let max = times.iter().copied().fold(0.0_f64, f64::max);
    assert!(
        min > 0.0,
        "{label}: measured a zero time (clock too coarse)"
    );
    let factor = max / min;
    assert!(
        factor <= max_factor,
        "{label} should be sub-linear, but slowest/fastest = {factor:.1}x across the size range \
         (max allowed {max_factor:.1}x); data = {data:?}",
    );
}

#[test]
fn complexity_append_amortized_constant() {
    let sizes: &[usize] = &[500, 1_000, 2_000, 5_000, 10_000, 20_000, 50_000];
    let batch = 1000;
    let trials = 21;
    let mut data: Vec<(f64, f64)> = Vec::with_capacity(sizes.len());

    for &n in sizes {
        let mut times = Vec::with_capacity(trials);
        for _ in 0..trials {
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
                for i in n..(n + batch) {
                    log.append_leaf(&(i as u64).to_le_bytes()).await.unwrap();
                }
                times.push(start.elapsed().as_nanos());
            });
        }
        let per_append = median(&mut times) as f64 / batch as f64;
        data.push((n as f64, per_append));
    }

    assert_rank_at_most(data, 1200, "append", "O(1) amortized");
}

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
                let mut log = NaryMerkleLog::new(
                    MemoryStorage::new(),
                    Box::new(Sha256Hasher),
                    TreeConfig { arity: 2 },
                )
                .await
                .unwrap();
                log.add_algorithm(1, Box::new(Sha256Hasher)).await.unwrap();
                for i in 0..base_size {
                    log.append_leaf(&(i as u64).to_le_bytes()).await.unwrap();
                }
                log.remove_algorithm(1).await.unwrap();
                for i in base_size..(base_size + g) {
                    log.append_leaf(&(i as u64).to_le_bytes()).await.unwrap();
                }
                let start = ThreadTime::now();
                log.resume_algorithm(1).await.unwrap();
                times.push(start.elapsed().as_nanos());
            });
        }
        data.push((g as f64, median(&mut times) as f64));
    }

    assert_rank_at_most(data, 1000, "resume_algorithm", "O(log n)");
}

// ============================================================================
// Subtree complexity tests
//
// The tests above only exercise flat leaf appends. The following tests verify
// the complexity of the operations that are specific to EML's novel
// structure: appending recursive subtrees and generating inclusion proofs
// through them.
// ============================================================================

use eml::Subtree;

/// Build a balanced binary subtree of the given depth.
///
/// Depth 0 → a single Leaf.
/// Depth d → a Node with 2 children, each of depth d-1.
///
/// Total nodes = 2^(d+1) - 1.  Total leaves = 2^d.
fn balanced_subtree(depth: usize, seed: &mut u64) -> Subtree {
    if depth == 0 {
        let data = seed.to_le_bytes().to_vec();
        *seed += 1;
        Subtree::Leaf(data)
    } else {
        Subtree::Node(vec![
            balanced_subtree(depth - 1, seed),
            balanced_subtree(depth - 1, seed),
        ])
    }
}

/// `append_subtree` should scale linearly in the number of subtree nodes,
/// since it must evaluate the entire subtree to compute its root hash.
#[test]
fn complexity_append_subtree_linear_in_nodes() {
    let depths: &[usize] = &[4, 6, 8, 10, 12, 14];
    let trials = 15;
    let mut data: Vec<(f64, f64)> = Vec::with_capacity(depths.len());

    for &d in depths {
        let mut seed = 0u64;
        let subtree = balanced_subtree(d, &mut seed);
        let total_nodes = (1u64 << (d + 1)) - 1;
        let mut times = Vec::with_capacity(trials);

        for _ in 0..trials {
            smol::block_on(async {
                let mut log = NaryMerkleLog::new(
                    MemoryStorage::new(),
                    Box::new(Sha256Hasher),
                    TreeConfig { arity: 2 },
                )
                .await
                .unwrap();

                let start = ThreadTime::now();
                log.append_subtree(&subtree).await.unwrap();
                times.push(start.elapsed().as_nanos());
            });
        }
        data.push((total_nodes as f64, median(&mut times) as f64));
    }

    assert_rank_at_most(data, 1200, "append_subtree", "O(n) in subtree nodes");
}

/// `within_subtree_path` should scale linearly in the number of subtree nodes,
/// because at each level it evaluates all sibling subtrees to collect their
/// hashes for the proof.
#[test]
fn complexity_within_subtree_path_linear_in_nodes() {
    let depths: &[usize] = &[4, 6, 8, 10, 12, 14];
    let trials = 15;
    let mut data: Vec<(f64, f64)> = Vec::with_capacity(depths.len());

    for &d in depths {
        let mut seed = 0u64;
        let subtree = balanced_subtree(d, &mut seed);
        let total_nodes = (1u64 << (d + 1)) - 1;
        let mut times = Vec::with_capacity(trials);

        for _ in 0..trials {
            let start = ThreadTime::now();
            for _ in 0..50 {
                let _ = eml::within_subtree_path(&Sha256Hasher, &subtree, 0);
            }
            times.push(start.elapsed().as_nanos() / 50);
        }
        data.push((total_nodes as f64, median(&mut times) as f64));
    }

    assert_rank_at_most(data, 1200, "within_subtree_path", "O(n) in subtree nodes");
}

/// End-to-end inclusion proof generation through subtrees, varying the log
/// size while keeping subtree structure fixed.  The subtree-internal cost is
/// constant, so the growth should be O(log n) in the number of appended
/// subtrees.
#[test]
fn complexity_e2e_inclusion_subtree_log_n() {
    let subtree_depth = 4; // Fixed: 16 leaves, 31 nodes per subtree.

    let make_subtree_log = |n: usize| -> Arc<(NaryMerkleLog<MemoryStorage>, Subtree)> {
        smol::block_on(async {
            let mut log = NaryMerkleLog::new(
                MemoryStorage::new(),
                Box::new(Sha256Hasher),
                TreeConfig { arity: 2 },
            )
            .await
            .unwrap();

            let mut last_subtree = None;
            for i in 0..n {
                let mut seed = (i as u64) * 1000;
                let st = balanced_subtree(subtree_depth, &mut seed);
                log.append_subtree(&st).await.unwrap();
                if i == 0 {
                    last_subtree = Some(st);
                }
            }
            Arc::new((log, last_subtree.unwrap()))
        })
    };

    let sizes: &[usize] = &[100, 500, 1_000, 2_000, 5_000, 10_000];
    let trials = 15;
    let mut data: Vec<(f64, f64)> = Vec::with_capacity(sizes.len());

    for &n in sizes {
        let setup = make_subtree_log(n);
        let mut times = Vec::with_capacity(trials);

        for _ in 0..trials {
            let (ref log, ref first_subtree) = *setup;
            let start = ThreadTime::now();
            for _ in 0..50 {
                // Within-subtree path for leaf 0 in subtree 0.
                let mut path = eml::within_subtree_path(&Sha256Hasher, first_subtree, 0).unwrap();

                // Log-level proof for subtree 0.
                let log_proof = smol::block_on(log.inclusion_proof(0, n as u64))
                    .unwrap()
                    .unwrap();

                path.extend(log_proof.path);
            }
            times.push(start.elapsed().as_nanos() / 50);
        }
        data.push((n as f64, median(&mut times) as f64));
    }

    assert_rank_at_most(
        data,
        1200,
        "e2e inclusion through subtree",
        "O(log n) in log size",
    );
}
