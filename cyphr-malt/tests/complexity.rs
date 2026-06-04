#![cfg(not(debug_assertions))]

use std::sync::Arc;

use bigoish::{Log as LogModel, N, assert_best_fit, growing_inputs};
use cpu_time::ThreadTime;
use cyphr_malt::{Hasher, MemoryStorage, NaryMerkleLog, TreeConfig};
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

    fn null(&self) -> Vec<u8> {
        Sha256::digest([0x02]).to_vec()
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
        let config = TreeConfig { log_arity: 2 };
        let mut log = NaryMerkleLog::new(storage, Box::new(Sha256Hasher), config).await;
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
                    TreeConfig { log_arity: 2 },
                )
                .await;
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
                    TreeConfig { log_arity: 2 },
                )
                .await;
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
