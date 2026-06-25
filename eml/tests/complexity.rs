#![cfg(not(debug_assertions))]

use std::sync::Arc;

use bigoish::{Log as LogModel, N, assert_best_fit, growing_inputs};
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

#[test]
fn complexity_inclusion_proof_log_n() {
    assert_best_fit(
        LogModel(N),
        |log: Arc<NaryMerkleLog<MemoryStorage>>| {
            smol::block_on(async {
                let mut proof = None;
                let ts = log.size();
                for _ in 0..100 {
                    proof = Some(log.inclusion_proof(0, ts / 2).await.unwrap());
                }
                proof.unwrap()
            })
        },
        growing_inputs(100, make_log, 25),
    );
}

#[test]
fn complexity_consistency_proof_log_n() {
    assert_best_fit(
        LogModel(N),
        |log: Arc<NaryMerkleLog<MemoryStorage>>| {
            smol::block_on(async {
                let mut proof = None;
                let ts = log.size();
                for _ in 0..100 {
                    proof = Some(log.consistency_proof(ts / 2, ts).await.unwrap());
                }
                proof.unwrap()
            })
        },
        growing_inputs(100, make_log, 25),
    );
}

#[test]
fn complexity_root_extraction_log_n() {
    assert_best_fit(
        LogModel(N),
        |log: Arc<NaryMerkleLog<MemoryStorage>>| {
            let mut root = None;
            for _ in 0..100 {
                root = Some(log.root());
            }
            root.unwrap()
        },
        growing_inputs(100, make_log, 25),
    );
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
