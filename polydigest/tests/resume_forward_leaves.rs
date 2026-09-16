//! Pins the ruling (2026-09-16) that a **resumed** log appends *ordinary*
//! leaves going forward, storing their real bytes exactly as a flat log
//! does -- never a same-digest, no-bytes subtree shortcut. `resume`'s own
//! doc comment (`polydigest/src/tree.rs:110-122`) already describes the
//! result as "a committed frontier you append real leaves onto", with
//! "forward appends add real leaves"; these tests hold `append_leaf` to
//! that description directly, against the `MemoryStorage` reference
//! backend.
//!
//! Today every test below fails for the same one reason: `append_leaf`
//! (`tree.rs:769`) refuses outright once a resumed (`LogKind::Subtree`)
//! log has `count > 0` (`tree.rs:772`), so a resumed log with any sealed
//! history at all can never call it. A malformed fix would flip that guard
//! without also making the forward leaf's bytes recoverable (`get_leaf`)
//! and its digest identical to today's subtree-shortcut digest -- each
//! test below isolates one such guarantee so a partial fix cannot pass by
//! accident.

use polydigest::{Hasher, MemoryStorage, NaryMerkleLog, Sealed, Storage, Subtree, TreeConfig};
use sha2::{Digest, Sha256};

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

/// Seal a fresh `n`-leaf, arity-`k` log and return its `Sealed`.
async fn sealed_log(n: u64, k: u64) -> Sealed {
    let mut log = NaryMerkleLog::new(
        MemoryStorage::new(),
        Box::new(Sha256Hasher),
        TreeConfig { arity: k },
    )
    .await
    .unwrap();
    for i in 0..n {
        log.append_leaf(format!("orig-{i}").as_bytes())
            .await
            .unwrap();
    }
    log.seal().await.unwrap()
}

/// Resume `sealed` onto a fresh `MemoryStorage`. `resume` itself "has no
/// failure conditions" for a well-formed `Sealed` (`tree.rs:126`), so this
/// step is never expected to fail.
async fn resume_onto_fresh(sealed: &Sealed) -> NaryMerkleLog<MemoryStorage> {
    NaryMerkleLog::resume(
        sealed,
        MemoryStorage::new(),
        vec![(0, Box::new(Sha256Hasher) as Box<dyn Hasher>)],
    )
    .await
    .expect("resume never fails for a well-formed Sealed")
}

// A resume from a size whose frontier is a single peak (n=4, k=2:
// frontier_for_size(4,2) has exactly one coordinate) -- the simplest case a
// naive fix could special-case away from the multi-peak one below.
#[test]
fn append_leaf_succeeds_after_resume_from_single_peak_seal() {
    smol::block_on(async {
        let n = 4u64;
        let k = 2u64;
        assert_eq!(
            polydigest::frontier_for_size(n, k).len(),
            1,
            "fixture sanity: n=4,k=2 must resume to a single peak"
        );
        let sealed = sealed_log(n, k).await;
        let mut resumed = resume_onto_fresh(&sealed).await;

        resumed
            .append_leaf(b"fwd-0")
            .await
            .expect("append_leaf must succeed on a resumed log (single-peak seal)");
        resumed
            .append_leaf(b"fwd-1")
            .await
            .expect("append_leaf must keep succeeding after the first forward append");
        assert_eq!(resumed.count(), n + 2);
    });
}

// A resume from a size whose frontier has more than one peak (n=5, k=2:
// frontier_for_size(5,2) has two coordinates), so the merge across peaks a
// single-peak fixture cannot exercise is covered too.
#[test]
fn append_leaf_succeeds_after_resume_from_multi_peak_seal() {
    smol::block_on(async {
        let n = 5u64;
        let k = 2u64;
        assert_eq!(
            polydigest::frontier_for_size(n, k).len(),
            2,
            "fixture sanity: n=5,k=2 must resume to two peaks"
        );
        let sealed = sealed_log(n, k).await;
        let mut resumed = resume_onto_fresh(&sealed).await;

        resumed
            .append_leaf(b"fwd-0")
            .await
            .expect("append_leaf must succeed on a resumed log (multi-peak seal)");
        resumed
            .append_leaf(b"fwd-1")
            .await
            .expect("append_leaf must keep succeeding across the peak merge it triggers");
        resumed
            .append_leaf(b"fwd-2")
            .await
            .expect("append_leaf must keep succeeding after the merge");
        assert_eq!(resumed.count(), n + 3);
    });
}

// `count()` must advance by exactly one per forward `append_leaf`, the same
// way a fresh flat log's does -- a malformed fix that silently drops or
// double-counts a forward append would still "succeed" per-call but drift
// here.
#[test]
fn count_advances_normally_across_forward_leaf_appends() {
    smol::block_on(async {
        let n = 3u64;
        let k = 2u64;
        let sealed = sealed_log(n, k).await;
        let mut resumed = resume_onto_fresh(&sealed).await;

        for i in 0..5u64 {
            resumed
                .append_leaf(format!("fwd-{i}").as_bytes())
                .await
                .expect("append_leaf must succeed");
            assert_eq!(
                resumed.count(),
                n + i + 1,
                "count must advance by one (i={i})"
            );
        }
    });
}

// The one digest guarantee `resume`'s own doc comment already promises: a
// forward `append_leaf`'s root must be byte-identical to appending the same
// bytes as a single-leaf subtree does today
// (`append_subtree(&Subtree::Leaf(bytes))`), swept across single- and
// multi-peak seeds and both an even and an odd number of forward entries (to
// cross a peak merge). A malformed fix that stores real bytes but changes
// the resulting digest would fail only this test.
#[test]
fn forward_leaf_digest_matches_subtree_equivalent() {
    smol::block_on(async {
        let k = 2u64;
        for n in [4u64, 5u64] {
            let sealed = sealed_log(n, k).await;
            let mut via_leaf = resume_onto_fresh(&sealed).await;
            let mut via_subtree = resume_onto_fresh(&sealed).await;

            let forward: Vec<Vec<u8>> =
                (0..3u64).map(|i| format!("fwd-{i}").into_bytes()).collect();

            for bytes in &forward {
                via_leaf
                    .append_leaf(bytes)
                    .await
                    .expect("append_leaf must succeed on the resumed log");
                via_subtree
                    .append_subtree(&Subtree::Leaf(bytes.clone()))
                    .await
                    .unwrap();
                assert_eq!(
                    via_leaf.root_for(0).unwrap(),
                    via_subtree.root_for(0).unwrap(),
                    "root_for(0) must match the subtree-equivalent digest (n={n})"
                );
            }
        }
    });
}

// `get_leaf` must return each forward entry's real bytes -- the load-bearing
// difference from today's subtree shortcut, which stores no bytes at all
// (only a digest). A malformed fix that makes `append_leaf` succeed and
// preserve the digest but still skips `store_leaf` would fail only this
// test.
#[test]
fn get_leaf_returns_forward_entries_bytes_after_resume() {
    smol::block_on(async {
        let n = 5u64;
        let k = 2u64;
        let sealed = sealed_log(n, k).await;
        let mut resumed = resume_onto_fresh(&sealed).await;

        let forward: Vec<Vec<u8>> = (0..4u64).map(|i| format!("fwd-{i}").into_bytes()).collect();
        for bytes in &forward {
            resumed
                .append_leaf(bytes)
                .await
                .expect("append_leaf must succeed");
        }

        for (i, bytes) in forward.iter().enumerate() {
            let idx = n + i as u64;
            let got =
                resumed.storage().get_leaf(idx).await.unwrap_or_else(|e| {
                    panic!("get_leaf({idx}) must return the forward entry: {e:?}")
                });
            assert_eq!(&got, bytes, "get_leaf({idx}) returned the wrong bytes");
        }

        // The inherited genesis frontier, and only it, stays opaque: every
        // index strictly below the sealed size must still be unreadable
        // (the resumed log's storage never received those bytes).
        for idx in 0..n {
            assert!(
                resumed.storage().get_leaf(idx).await.is_err(),
                "get_leaf({idx}) for an inherited (pre-resume) index must stay opaque"
            );
        }
    });
}

// An inclusion proof for a forward leaf must verify against the resumed
// log's own root -- the proof surface a consumer actually reaches through
// `leaf_proof`/`inclusion_proof`, not just the raw digest equality the
// digest-parity test above checks.
#[test]
fn inclusion_proof_verifies_for_forward_leaf_after_resume() {
    smol::block_on(async {
        let n = 5u64;
        let k = 2u64;
        let sealed = sealed_log(n, k).await;
        let mut resumed = resume_onto_fresh(&sealed).await;

        let forward: Vec<Vec<u8>> = (0..4u64).map(|i| format!("fwd-{i}").into_bytes()).collect();
        for bytes in &forward {
            resumed
                .append_leaf(bytes)
                .await
                .expect("append_leaf must succeed");
        }

        let size = resumed.count();
        let root = resumed.root_for_at(0, size).await.unwrap();
        let h = Sha256Hasher;

        for (i, bytes) in forward.iter().enumerate() {
            let idx = n + i as u64;
            let proof = resumed
                .leaf_proof(idx, size)
                .await
                .unwrap()
                .unwrap_or_else(|| panic!("leaf_proof({idx}, {size}) must exist"));
            let sk = polydigest::mountain_skeleton(k, size, idx).expect("valid position");
            assert!(
                proof.verify(&h, &sk, &root),
                "inclusion proof for forward leaf at index {idx} must verify"
            );
            assert_eq!(proof.leaf_hash, h.leaf(bytes));
        }
    });
}

// A consistency proof must bridge from the sealed size across the forward
// leaf appends, exactly as the existing `append_subtree`-based resume test
// (`log_behavior.rs::resume_from_eml_origin_reproduces_root_and_appends`)
// already establishes for the subtree shortcut -- ordinary leaf appends must
// not lose this.
#[test]
fn consistency_proof_verifies_across_resume_and_forward_leaf_appends() {
    smol::block_on(async {
        let n = 5u64;
        let k = 2u64;
        let sealed = sealed_log(n, k).await;
        let mut resumed = resume_onto_fresh(&sealed).await;
        let old_root = resumed.root_for_at(0, n).await.unwrap();

        resumed
            .append_leaf(b"fwd-0")
            .await
            .expect("append_leaf must succeed");
        resumed
            .append_leaf(b"fwd-1")
            .await
            .expect("append_leaf must succeed");
        let new_size = resumed.count();
        assert_eq!(new_size, n + 2);

        let proof = resumed
            .consistency_proof(n, new_size)
            .await
            .unwrap()
            .expect("consistency proof must bridge the resume boundary");
        let new_root = resumed.root_for_at(0, new_size).await.unwrap();
        let h = Sha256Hasher;
        assert!(
            polydigest::verify_consistency(
                &h,
                n,
                new_size,
                k,
                &proof.boundary_hash,
                &proof.peak_path,
                &proof.new_peaks,
                proof.split_index,
                &old_root,
                &new_root,
            ),
            "consistency proof across resume + forward leaf appends must verify"
        );
    });
}
