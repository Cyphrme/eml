//! A seal carries every registered algorithm's frontier, and a resume
//! restores it: an algorithm closed before the seal must come back from
//! `resume_algorithm` on the resumed log with exactly the roots the same
//! operations give an unsealed log.
//!
//! The control is the unsealed log run through the identical operation
//! schedule, so the property is "seal + resume is invisible to every later
//! operation", checked over every placement of the dormant algorithm's
//! lifecycle rather than a hand-picked example.

use polydigest::{Hasher, MemoryStorage, NaryMerkleLog, Subtree, TreeConfig};

#[derive(Debug, Clone)]
struct FixtureHasher;

impl Hasher for FixtureHasher {
    fn leaf(&self, data: &[u8]) -> Vec<u8> {
        use sha2::{Digest, Sha256};
        Sha256::digest(data).to_vec()
    }

    fn node(&self, children: &[&[u8]]) -> Vec<u8> {
        use sha2::{Digest, Sha256};
        let mut h = Sha256::new();
        for c in children {
            h.update(c);
        }
        h.finalize().to_vec()
    }

    fn empty(&self) -> Vec<u8> {
        use sha2::{Digest, Sha256};
        Sha256::digest(b"").to_vec()
    }

    fn hash(&self, data: &[u8]) -> Vec<u8> {
        use sha2::{Digest, Sha256};
        Sha256::digest(data).to_vec()
    }

    fn clone_box(&self) -> Box<dyn Hasher> {
        Box::new(self.clone())
    }
}

type Log = NaryMerkleLog<MemoryStorage>;

#[derive(Debug, Clone, Copy)]
enum Ev {
    Close,
    Resume,
}

async fn new_log(k: u64) -> Log {
    NaryMerkleLog::new(
        MemoryStorage::new(),
        Box::new(FixtureHasher),
        TreeConfig { arity: k },
    )
    .await
    .unwrap()
}

/// Append leaf `i`, flat on a fresh log and as a single-leaf subtree on a
/// resumed one (byte-identical digests by construction).
async fn push(log: &mut Log, i: u64, subtree: bool) {
    let data = format!("leaf-{i}").into_bytes();
    if subtree {
        log.append_subtree(&Subtree::Leaf(data)).await.unwrap();
    } else {
        log.append_leaf(&data).await.unwrap();
    }
}

/// Build alg 0 (always active) and alg 1 (added at `add`), applying `evs`
/// to alg 1 at the given sizes, up to `n` leaves.
async fn build(k: u64, add: u64, evs: &[(u64, Ev)], n: u64) -> Log {
    let mut log = new_log(k).await;
    for s in 0..=n {
        if s == add {
            log.add_algorithm(1, Box::new(FixtureHasher)).await.unwrap();
        }
        for &(at, ev) in evs {
            if at == s {
                match ev {
                    Ev::Close => log.remove_algorithm(1).await.unwrap(),
                    Ev::Resume => log.resume_algorithm(1).await.unwrap(),
                }
            }
        }
        if s < n {
            push(&mut log, s, false).await;
        }
    }
    log
}

/// Continue a log (sealed-and-resumed or not): append to size `r`, resume
/// alg 1 if it is dormant, append to size `m`, and return the roots.
async fn tail(mut log: Log, subtree: bool, r: u64, m: u64) -> Vec<Vec<u8>> {
    let n = log.count();
    for i in n..r {
        push(&mut log, i, subtree).await;
    }
    log.resume_algorithm(1).await.unwrap();
    for i in r..m {
        push(&mut log, i, subtree).await;
    }
    let mut roots = Vec::new();
    for alg in [0, 1] {
        roots.push(log.combined_root_for(alg).await.unwrap());
        roots.push(log.root_for_at(alg, m).await.unwrap());
    }
    roots
}

async fn sealed_then_resumed(log: Log) -> Log {
    let sealed = log.seal().await.unwrap();
    NaryMerkleLog::resume(
        &sealed,
        MemoryStorage::new(),
        vec![
            (0, Box::new(FixtureHasher) as Box<dyn Hasher>),
            (1, Box::new(FixtureHasher) as Box<dyn Hasher>),
        ],
    )
    .await
    .unwrap()
}

async fn assert_seal_invisible(k: u64, add: u64, evs: &[(u64, Ev)], n: u64, r: u64, m: u64) {
    let direct = tail(build(k, add, evs, n).await, false, r, m).await;
    let resumed = tail(
        sealed_then_resumed(build(k, add, evs, n).await).await,
        true,
        r,
        m,
    )
    .await;
    assert_eq!(
        direct, resumed,
        "k={k} add={add} evs={evs:?} seal at n={n}, resume_algorithm at r={r}, end m={m}"
    );
}

/// The reported case: close, append, seal, resume, `resume_algorithm`,
/// append.
#[test]
fn closed_algorithm_resumes_after_seal_and_resume() {
    smol::block_on(async {
        assert_seal_invisible(2, 1, &[(3, Ev::Close)], 5, 6, 8).await;
    });
}

/// Every placement of one close, for arities 2..=4.
#[test]
fn every_close_and_resume_position_single_epoch() {
    smol::block_on(async {
        for k in 2..=4u64 {
            for add in 0..=4u64 {
                for c in (add + 1)..=7u64 {
                    for n in c..=8u64 {
                        for r in n..=9u64 {
                            assert_seal_invisible(k, add, &[(c, Ev::Close)], n, r, r + 3).await;
                        }
                    }
                }
            }
        }
    });
}

/// A dormant gap inside the algorithm's history (close, resume, close)
/// before the seal: the carried frontier spans the gap.
#[test]
fn every_position_with_an_earlier_dormant_gap() {
    smol::block_on(async {
        for k in 2..=3u64 {
            for add in 0..=2u64 {
                for c1 in (add + 1)..=5u64 {
                    for c2 in (c1 + 1)..=6u64 {
                        for c3 in (c2 + 1)..=7u64 {
                            let evs = [(c1, Ev::Close), (c2, Ev::Resume), (c3, Ev::Close)];
                            for n in c3..=8u64 {
                                for r in [n, n + 1, n + 4] {
                                    assert_seal_invisible(k, add, &evs, n, r, r + 2).await;
                                }
                            }
                        }
                    }
                }
            }
        }
    });
}
