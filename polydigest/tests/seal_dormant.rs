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
async fn build_as(k: u64, add: u64, evs: &[(u64, Ev)], n: u64, subtree: bool) -> Log {
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
            push(&mut log, s, subtree).await;
        }
    }
    log
}

async fn build(k: u64, add: u64, evs: &[(u64, Ev)], n: u64) -> Log {
    build_as(k, add, evs, n, false).await
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

/// The dormant frontier is O(log n) peaks at the close size, survives
/// `with_meta`, and a mismatched peak count is refused.
#[test]
fn dormant_frontier_is_logarithmic_and_validated() {
    smol::block_on(async {
        let sealed = build(2, 1, &[(5, Ev::Close)], 40)
            .await
            .seal_with_meta(polydigest::Meta::new(b"m".to_vec()))
            .await
            .unwrap();
        let dormant = sealed.dormant_frontiers();
        assert_eq!(dormant.len(), 1);
        assert_eq!(dormant[0].0, 1);
        // Close size 5 = 0b101: two peaks, not 40 leaves' worth.
        assert_eq!(dormant[0].1.len(), 2);
        assert!(sealed.peaks(1).is_none(), "closed alg has no active peaks");

        assert!(
            sealed
                .clone()
                .with_dormant_frontiers(vec![(1, vec![vec![0; 32]])])
                .is_err(),
            "wrong peak count for close size 5"
        );
        assert!(
            sealed.with_dormant_frontiers(vec![(0, vec![])]).is_err(),
            "alg 0 is still open"
        );
    });
}

/// A caller that supplies no hasher for a closed algorithm still resumes (as
/// resume always has); the algorithm is then unknown to the resumed log. A
/// missing hasher for an active algorithm stays an error.
#[test]
fn closed_algorithm_hasher_is_optional_on_resume() {
    smol::block_on(async {
        let sealed = build(2, 1, &[(3, Ev::Close)], 5)
            .await
            .seal()
            .await
            .unwrap();
        let hashers = |ids: &[u64]| -> Vec<(u64, Box<dyn Hasher>)> {
            ids.iter()
                .map(|&id| (id, Box::new(FixtureHasher) as Box<dyn Hasher>))
                .collect()
        };
        let mut log = NaryMerkleLog::resume(&sealed, MemoryStorage::new(), hashers(&[0]))
            .await
            .unwrap();
        assert!(log.resume_algorithm(1).await.is_err());
        assert!(
            NaryMerkleLog::resume(&sealed, MemoryStorage::new(), hashers(&[1]))
                .await
                .is_err()
        );
    });
}

/// A natively subtree-kind log (subtree appends from genesis, never resumed)
/// with an algorithm partially active across the appended subtrees must root
/// exactly as the flat log of the same leaves does, including after the
/// algorithm is resumed: pins the stored-node read path outside `resume`.
#[test]
fn native_subtree_log_matches_flat_with_a_partially_active_algorithm() {
    smol::block_on(async {
        for k in 2..=3u64 {
            for add in 0..=3u64 {
                for c in (add + 1)..=6u64 {
                    for r in c..=8u64 {
                        let evs = [(c, Ev::Close)];
                        let flat =
                            tail(build_as(k, add, &evs, c, false).await, false, r, r + 3).await;
                        let sub = tail(build_as(k, add, &evs, c, true).await, true, r, r + 3).await;
                        assert_eq!(flat, sub, "k={k} add={add} close={c} resume={r}");
                    }
                }
            }
        }
    });
}

fn hashers_for(ids: &[u64]) -> Vec<(u64, Box<dyn Hasher>)> {
    ids.iter()
        .map(|&id| (id, Box::new(FixtureHasher) as Box<dyn Hasher>))
        .collect()
}

/// Resuming without a closed algorithm's hasher must leave a record of its
/// id: re-adding it would register it fresh over nulls and root differently
/// from the original log. It stays unresumable and un-re-addable, and the
/// record survives a reopen. A re-seal still carries it.
#[test]
fn hasherless_closed_algorithm_cannot_be_re_added() {
    smol::block_on(async {
        let sealed = build(2, 1, &[(3, Ev::Close)], 5)
            .await
            .seal()
            .await
            .unwrap();
        let mut log = NaryMerkleLog::resume(&sealed, MemoryStorage::new(), hashers_for(&[0]))
            .await
            .unwrap();
        assert!(matches!(
            log.add_algorithm(1, Box::new(FixtureHasher)).await,
            Err(polydigest::LogError::DuplicateAlgorithm(1))
        ));
        assert!(matches!(
            log.resume_algorithm(1).await,
            Err(polydigest::LogError::UnknownAlgorithm(1))
        ));
        assert!(
            log.stage()
                .add_algorithm(1, Box::new(FixtureHasher))
                .is_err()
        );

        // Sealing again still freezes it: same dormant frontier and timeline.
        let resealed = NaryMerkleLog::resume(&sealed, MemoryStorage::new(), hashers_for(&[0]))
            .await
            .unwrap()
            .seal()
            .await
            .unwrap();
        assert_eq!(resealed, sealed);

        // Reopening with the hasher keeps the id taken.
        let storage = log.into_storage();
        let mut reopened = NaryMerkleLog::from_storage(storage, hashers_for(&[0, 1]))
            .await
            .unwrap();
        assert!(matches!(
            reopened.add_algorithm(1, Box::new(FixtureHasher)).await,
            Err(polydigest::LogError::DuplicateAlgorithm(1))
        ));
        let storage = reopened.into_storage();
        // An open algorithm's hasher is still required.
        assert!(matches!(
            NaryMerkleLog::from_storage(storage, hashers_for(&[1])).await,
            Err(polydigest::LogError::OrphanedMetadata(0))
        ));
    });
}

/// Roots a log reports after `extra` more appends: both algorithms'
/// combined roots where alg 1 is registered, else alg 0's alone.
async fn live_roots(log: &mut Log, from: u64, extra: u64, subtree: bool) -> Vec<Vec<u8>> {
    for i in from..from + extra {
        push(log, i, subtree).await;
    }
    vec![log.combined_root_for(0).await.unwrap()]
}

/// A hasherless resumed log must report the same combined roots as the
/// original: the coverage child binds every algorithm's timeline, the closed
/// one included, with no hasher needed for it.
#[test]
fn hasherless_resumed_log_has_the_original_combined_root() {
    smol::block_on(async {
        for k in 2..=3u64 {
            for add in 0..=3u64 {
                for c in (add + 1)..=6u64 {
                    // n > c: at n == c the closed algorithm still holds the tip
                    // position, so its member root enters the fold and the
                    // hasherless log must fail closed there instead.
                    for n in (c + 1)..=8u64 {
                        let evs = [(c, Ev::Close)];
                        let mut original = build(k, add, &evs, n).await;
                        let sealed = build(k, add, &evs, n).await.seal().await.unwrap();
                        let mut resumed =
                            NaryMerkleLog::resume(&sealed, MemoryStorage::new(), hashers_for(&[0]))
                                .await
                                .unwrap();
                        assert_eq!(
                            original.combined_root_for(0).await.unwrap(),
                            resumed.combined_root_for(0).await.unwrap(),
                            "k={k} add={add} close={c} at sealed size {n}"
                        );
                        assert_eq!(
                            live_roots(&mut original, n, 3, false).await,
                            live_roots(&mut resumed, n, 3, true).await,
                            "k={k} add={add} close={c} sealed at {n}, after appends"
                        );
                    }
                }
            }
        }
    });
}

/// A closed algorithm's hasher is optional on `from_storage` too, as on
/// `resume`: reopening with active hashers only keeps the id taken and the
/// roots equal.
#[test]
fn from_storage_loads_a_closed_algorithm_without_its_hasher() {
    smol::block_on(async {
        let mut original = build(2, 1, &[(3, Ev::Close)], 5).await;
        let sealed = build(2, 1, &[(3, Ev::Close)], 5)
            .await
            .seal()
            .await
            .unwrap();
        let log = NaryMerkleLog::resume(&sealed, MemoryStorage::new(), hashers_for(&[0]))
            .await
            .unwrap();
        let mut reopened = NaryMerkleLog::from_storage(log.into_storage(), hashers_for(&[0]))
            .await
            .unwrap();
        assert!(matches!(
            reopened.add_algorithm(1, Box::new(FixtureHasher)).await,
            Err(polydigest::LogError::DuplicateAlgorithm(1))
        ));
        assert_eq!(
            original.combined_root_for(0).await.unwrap(),
            reopened.combined_root_for(0).await.unwrap()
        );
        assert_eq!(
            live_roots(&mut original, 5, 3, false).await,
            live_roots(&mut reopened, 5, 3, true).await
        );
    });
}

/// Closed exactly at the sealed size, the algorithm still holds the tip
/// position, so its member root belongs in the combined root and a hasherless
/// log cannot produce it: it fails closed rather than report a wrong root.
#[test]
fn hasherless_log_fails_closed_where_the_missing_member_root_is_needed() {
    smol::block_on(async {
        let sealed = build(2, 1, &[(3, Ev::Close)], 3)
            .await
            .seal()
            .await
            .unwrap();
        let log = NaryMerkleLog::resume(&sealed, MemoryStorage::new(), hashers_for(&[0]))
            .await
            .unwrap();
        assert!(matches!(
            log.combined_root_for(0).await,
            Err(polydigest::LogError::UnknownAlgorithm(1))
        ));
    });
}
