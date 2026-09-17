//! Acceptance tests for §2.5's purity (SG9), from `docs/specs/storage-git.md`
//! alone.
//!
//! Retired from this file: `sg3_digest_entries_present_iff_active_and_match_the_fold` navigated
//! `peaks/hex(height,2)/hex(q,2)/digest/hex(alg_id,16)` to check that a
//! second algorithm's digest never leaks into a range where it is inactive.
//! The ratified key-derived layout ("THE DESIGN", `spike-report.md` and its
//! prototype `storage-git-keyed/`) makes this structurally trivial rather
//! than something to verify by inspection: each algorithm's digest for a
//! coordinate lives at its own top-level-alg-id-prefixed path
//! (`n/hex16(alg_id)/hex2(height)/trimmed(left)`), so a different algorithm
//! is a wholly different path, never a sibling entry inside a shared
//! `digest/` subtree that a purity bug could pollute. The completeness
//! property (`completeness_property.rs`) already checks every
//! `(alg, left, height)` key `MemoryStorage` holds -- including across
//! exactly this kind of add/remove/resume sequence -- against `GitStorage`,
//! which subsumes SG3's active-range claim without needing a `peaks/`-
//! specific oracle. `sg9_purity_under_reordered_equivalent_operations`
//! (below) is kept: it never navigates `peaks/`, comparing only the two
//! runs' tip tree ids directly (duplicated, deliberately, by
//! `structural.rs::sg9_purity_under_reordering`'s own independent fixture).

#[path = "acceptance_support/mod.rs"]
mod support;

use support::{FixtureHasher, bare_repo, new_log};

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
