//! Acceptance tests for §2.2's per-node digests (SG3) and §2.5's purity
//! (SG9), from `docs/specs/storage-git.md` alone.

#[path = "acceptance_support/mod.rs"]
mod support;

use spine::{Hasher, nary_mr};
use support::{FixtureHasher, bare_repo, hex, new_log};

/// Recompute `T(left, height)`'s digest under `hasher` directly from raw
/// leaves, independent of any log/storage machinery — the ground truth SG3
/// checks the stored `digest/hex(alg_id,16)` blob against.
fn expected_digest(
    hasher: &dyn Hasher,
    leaves: &[Vec<u8>],
    left: usize,
    height: u32,
    k: usize,
) -> Vec<u8> {
    if height == 0 {
        return hasher.leaf(&leaves[left]);
    }
    let child_span = k.pow(height - 1);
    let children: Vec<Vec<u8>> = (0..k)
        .map(|c| expected_digest(hasher, leaves, left + c * child_span, height - 1, k))
        .collect();
    let child_refs: Vec<&[u8]> = children.iter().map(Vec::as_slice).collect();
    nary_mr(hasher, &child_refs)
}

/// [SG3] `T(left, h)` MUST carry, for every algorithm active over
/// `[left, left + k^h)`, a `digest/hex(alg_id,16)` blob equal to that
/// algorithm's fold; no entry MUST exist for an algorithm whose active
/// range there is empty.
#[test]
fn sg3_digest_entries_present_iff_active_and_match_the_fold() {
    smol::block_on(async {
        let dir = tempfile::tempdir().unwrap();
        let repo = bare_repo(dir.path(), gix::hash::Kind::Sha256);
        let staging = "refs/eml/storage/sg3/staging";
        let alg0 = FixtureHasher::new(32);
        let alg1 = FixtureHasher::new(20);
        let mut log = new_log(&repo, staging, 2, alg0.clone()).await;

        let leaves: Vec<Vec<u8>> = (0..8u32)
            .map(|i| format!("leaf-{i}").into_bytes())
            .collect();

        // alg1 is registered only after the first 4 leaves, so it is
        // inactive over [0,4) and fully active over [4,8).
        for leaf in &leaves[0..4] {
            log.append_leaf(leaf).await.unwrap();
        }
        log.add_algorithm(1, Box::new(alg1.clone())).await.unwrap();
        for leaf in &leaves[4..8] {
            log.append_leaf(leaf).await.unwrap();
        }

        let local = repo.to_thread_local();
        let tip = support::ref_target(&local, staging).unwrap();

        // T(0,3) (the only frontier peak at n=8, k=2) -> children T(0,2),
        // T(4,2), both real materialized descendants of a flat log.
        let root_path = format!("peaks/{}/{}", hex(3, 2), hex(0, 2));
        let root = support::resolve_path(&local, tip, &root_path).unwrap().oid;
        let t02 = support::find_entry(&local, root, &hex(0, 2)).unwrap().oid;
        let t42 = support::find_entry(&local, root, &hex(1, 2)).unwrap().oid;

        // T(0,2) covers [0,4): alg0 active, alg1 inactive (its epoch starts
        // at 4).
        let digest02 = support::find_entry(&local, t02, "digest").unwrap().oid;
        let alg0_at_t02 = support::find_entry(&local, digest02, &hex(0, 16))
            .unwrap_or_else(|| panic!("alg0 must be active over [0,4)"));
        assert_eq!(
            support::read_blob(&local, alg0_at_t02.oid),
            expected_digest(&alg0, &leaves, 0, 2, 2),
            "T(0,2)'s alg0 digest must equal H_0's fold over leaves[0..4)"
        );
        assert!(
            support::find_entry(&local, digest02, &hex(1, 16)).is_none(),
            "alg1's active range over [0,4) is empty; T(0,2) must carry no digest/{} entry",
            hex(1, 16)
        );

        // T(4,2) covers [4,8): both alg0 and alg1 are fully active, with no
        // null-substitution in play, so both digests are a clean fold.
        let digest42 = support::find_entry(&local, t42, "digest").unwrap().oid;
        let alg0_at_t42 = support::find_entry(&local, digest42, &hex(0, 16))
            .unwrap_or_else(|| panic!("alg0 must be active over [4,8)"));
        assert_eq!(
            support::read_blob(&local, alg0_at_t42.oid),
            expected_digest(&alg0, &leaves, 4, 2, 2),
            "T(4,2)'s alg0 digest must equal H_0's fold over leaves[4..8)"
        );
        let alg1_at_t42 = support::find_entry(&local, digest42, &hex(1, 16))
            .unwrap_or_else(|| panic!("alg1 must be active over [4,8)"));
        assert_eq!(
            support::read_blob(&local, alg1_at_t42.oid),
            expected_digest(&alg1, &leaves, 4, 2, 2),
            "T(4,2)'s alg1 digest must equal H_1's fold over leaves[4..8)"
        );
    });
}

/// [SG9] `C(n)`'s object id MUST be a pure function of `k`, the item
/// sequence, and the currently-known epoch history — it MUST NOT depend on
/// insertion order among operations that do not change `n`. Two algorithm
/// registrations at the same size, in either order, must yield the same
/// `C(n)` once both are known.
#[test]
fn sg9_purity_under_reordered_equivalent_operations() {
    smol::block_on(async {
        let dir_a = tempfile::tempdir().unwrap();
        let dir_b = tempfile::tempdir().unwrap();
        let repo_a = bare_repo(dir_a.path(), gix::hash::Kind::Sha256);
        let repo_b = bare_repo(dir_b.path(), gix::hash::Kind::Sha256);

        let staging = "refs/eml/storage/sg9/staging";
        let mut log_a = new_log(&repo_a, staging, 3, FixtureHasher::new(32)).await;
        let mut log_b = new_log(&repo_b, staging, 3, FixtureHasher::new(32)).await;

        // Order A: register 1 then 2. Order B: register 2 then 1. Both at
        // n=0, before any append -- a reordering of operations that do not
        // change n.
        log_a
            .add_algorithm(1, Box::new(FixtureHasher::new(20)))
            .await
            .unwrap();
        log_a
            .add_algorithm(2, Box::new(FixtureHasher::new(16)))
            .await
            .unwrap();

        log_b
            .add_algorithm(2, Box::new(FixtureHasher::new(16)))
            .await
            .unwrap();
        log_b
            .add_algorithm(1, Box::new(FixtureHasher::new(20)))
            .await
            .unwrap();

        for i in 0..6u32 {
            let leaf = format!("leaf-{i}").into_bytes();
            log_a.append_leaf(&leaf).await.unwrap();
            log_b.append_leaf(&leaf).await.unwrap();
        }

        let local_a = repo_a.to_thread_local();
        let local_b = repo_b.to_thread_local();
        let tip_a = support::ref_target(&local_a, staging).unwrap();
        let tip_b = support::ref_target(&local_b, staging).unwrap();
        assert_eq!(
            tip_a, tip_b,
            "C(n) must not depend on the insertion order of two algorithm registrations that both \
             happened at the same size"
        );
    });
}
