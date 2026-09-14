//! Acceptance tests for §2.6's materialized-vs-opaque distinction:
//! SG10 (a subtree-kind or resumed node MUST be opaque) and SG11 (opacity is
//! a property of the node's own provenance, never inferred from the log's
//! `meta.kind` byte), from `docs/specs/storage-git.md` alone.
//!
//! A seal resumption's own contract (`polydigest::NaryMerkleLog::resume`'s
//! doc comment: "storage is a fresh backend the resumed log writes forward
//! into") already excludes reopening a ref that still holds a log's own
//! committed objects -- that is not a way to continue a log, it is a
//! contract violation. So that case is refused outright, before anything is
//! written, rather than reconciled into an opaque tree: this file used to
//! assert the latter, and the tests below replace that assertion with the
//! refusal, while keeping SG10/SG11's opacity guarantee for the case the
//! contract actually supports -- resuming onto a genuinely fresh, empty
//! ref.

#[path = "acceptance_support/mod.rs"]
mod support;

use polydigest::{NaryMerkleLog, verify_consistency};
use spine::Subtree;
use storage_git::GitStorage;
use support::{FixtureHasher, bare_repo, hex, new_log};

/// [SG10] A `T(left, 0)` node built from `Storage::store_node` with no
/// corresponding `store_leaf` call -- exactly what happens for every
/// subtree-kind append -- MUST be opaque: `digest/` only, no `leaf`.
#[test]
fn sg10_subtree_kind_append_is_opaque() {
    smol::block_on(async {
        let dir = tempfile::tempdir().unwrap();
        let repo = bare_repo(dir.path(), gix::hash::Kind::Sha256);
        let staging = "refs/eml/storage/sg10-subtree/staging";
        // High arity: every append stays an isolated height-0 peak, so its
        // ordinal under peaks/00/ is just its index.
        let mut log = new_log(&repo, staging, 50, FixtureHasher::new(32)).await;

        for i in 0..3u32 {
            log.append_subtree(&Subtree::Leaf(format!("subtree-leaf-{i}").into_bytes()))
                .await
                .unwrap();
        }

        let local = repo.to_thread_local();
        let tip = support::ref_target(&local, staging).unwrap();
        for i in 0..3u64 {
            let path = format!("peaks/{}/{}", hex(0, 2), hex(i, 2));
            let node = support::resolve_path(&local, tip, &path)
                .unwrap_or_else(|| panic!("no peak at {path}"))
                .oid;
            let entries = support::read_tree(&local, node);
            assert!(
                !entries.iter().any(|e| e.name == "leaf"),
                "T({i},0) built via append_subtree must not carry a materialized leaf blob"
            );
            assert!(
                entries.iter().any(|e| e.name == "digest"),
                "T({i},0) must still carry digest/"
            );
        }
    });
}

/// A resumption's `storage` must be a fresh backend: a ref that still holds
/// a log's own committed objects -- e.g. the very ref a source log was just
/// sealed from -- MUST be refused, not silently folded into a new tree, and
/// nothing must be written when it is. This replaces this file's prior
/// assertion that a peak resumed onto such a stale ref still comes back
/// opaque: that case has moved from "supported, but must stay opaque" to
/// "refused before anything is written" -- the stale ref never was a
/// resumable target, so reconciling it into a well-formed tree was the
/// wrong fix for the corruption that reconciliation itself introduced.
#[test]
fn resume_onto_a_ref_that_already_holds_a_log_is_refused() {
    smol::block_on(async {
        let dir = tempfile::tempdir().unwrap();
        let staging = "refs/eml/storage/resume-refusal/staging";
        let repo = bare_repo(dir.path(), gix::hash::Kind::Sha256);
        let k = 2u64;
        let real = FixtureHasher::new(32);

        let mut log = new_log(&repo, staging, k, real.clone()).await;
        for i in 0..4u32 {
            log.append_leaf(format!("leaf-{i}").as_bytes())
                .await
                .unwrap();
        }
        let sealed = log.seal().await.unwrap();

        let local = repo.to_thread_local();
        let before = support::ref_target(&local, staging).unwrap();

        // A plain, ordinary constructor over the SAME ref the source log
        // just sealed from: it still holds every one of that log's
        // committed objects. Handed straight to `resume` -- the path any
        // caller actually uses -- this must be refused, whatever
        // constructor produced it.
        let stale_storage = GitStorage::new(support::reopen_repo(dir.path()), staging, k)
            .expect("open GitStorage over the stale ref");
        let result =
            NaryMerkleLog::resume(&sealed, stale_storage, vec![(0, Box::new(real.clone()))]).await;

        assert!(
            result.is_err(),
            "resume onto a ref that already holds a log's committed objects must be refused; it \
             was silently accepted instead"
        );

        let after = support::ref_target(&local, staging).unwrap();
        assert_eq!(
            before, after,
            "a refused resume must leave the stale ref exactly as it was before the attempt -- \
             nothing written"
        );
    });
}

/// However the fresh storage handed to `resume` was constructed, resuming
/// the same seal onto an equally fresh (empty) ref must reach one identical
/// tip -- the result must never depend on which constructor produced the
/// storage.
///
/// Setup change: this test used to compare `GitStorage::new` against a
/// since-removed, explicit resume-open constructor that carried a
/// per-instance resume flag. Opacity is now
/// decided purely by what is stored plus what the write supplies, and a
/// resume onto non-fresh storage is refused outright by
/// `polydigest::NaryMerkleLog::resume` itself, so no backend-side flag is
/// needed to tell a resuming caller from a continuing one. `GitStorage::new`
/// is now the only constructor, which would make a direct comparison
/// against it hold by construction. Rewritten instead to compare the two
/// constructors that remain: `GitStorage::new`, handed an
/// already-open repository handle, against `GitStorage::open`, which opens
/// the repository from a path itself -- still a genuine
/// construction-independence check, just not the one this file's original
/// setup exercised.
#[test]
fn resume_onto_a_fresh_ref_is_independent_of_how_the_storage_was_constructed() {
    smol::block_on(async {
        let dir_src = tempfile::tempdir().unwrap();
        let staging_src = "refs/eml/storage/resume-fresh-src/staging";
        let repo_src = bare_repo(dir_src.path(), gix::hash::Kind::Sha256);
        let k = 2u64;
        let real = FixtureHasher::new(32);
        let mut log = new_log(&repo_src, staging_src, k, real.clone()).await;
        for i in 0..3u32 {
            log.append_leaf(format!("leaf-{i}").as_bytes())
                .await
                .unwrap();
        }
        let sealed = log.seal().await.unwrap();

        let dir_a = tempfile::tempdir().unwrap();
        let staging_a = "refs/eml/storage/resume-fresh-a/staging";
        let repo_a = bare_repo(dir_a.path(), gix::hash::Kind::Sha256);
        let storage_a = GitStorage::new(repo_a.clone(), staging_a, k)
            .expect("the plain constructor must open an empty ref");
        let resumed_a =
            NaryMerkleLog::resume(&sealed, storage_a, vec![(0, Box::new(real.clone()))])
                .await
                .expect("resume onto a fresh ref via GitStorage::new");

        let dir_b = tempfile::tempdir().unwrap();
        let staging_b = "refs/eml/storage/resume-fresh-b/staging";
        // Establish an empty repository at `dir_b` first (`bare_repo`, same
        // as every other fixture), then reopen it by path through
        // `GitStorage::open` -- a distinct construction path from `new`'s
        // already-open repository handle above.
        let _ = bare_repo(dir_b.path(), gix::hash::Kind::Sha256);
        let storage_b = GitStorage::open(dir_b.path(), staging_b, k)
            .expect("GitStorage::open must open the same empty repository by path");
        let resumed_b =
            NaryMerkleLog::resume(&sealed, storage_b, vec![(0, Box::new(real.clone()))])
                .await
                .expect("resume onto a fresh ref via GitStorage::open");

        let repo_b = support::reopen_repo(dir_b.path());
        let tip_a = support::ref_target(&repo_a.to_thread_local(), staging_a).unwrap();
        let tip_b = support::ref_target(&repo_b.to_thread_local(), staging_b).unwrap();
        assert_eq!(
            tip_a, tip_b,
            "resuming the same seal onto an equally fresh ref must reach the same tip regardless \
             of which constructor produced the storage handed to resume"
        );
        assert_eq!(
            resumed_a.count(),
            resumed_b.count(),
            "both resumptions must report the same size"
        );
    });
}

/// [SG10]/[SG11] Resuming onto a genuinely fresh (empty) ref must still
/// yield opaque peaks -- digest only, no leaf, no children -- and so must
/// every forward `append_subtree` on the resumed log.
#[test]
fn resume_onto_an_empty_ref_still_yields_opaque_peaks() {
    smol::block_on(async {
        let dir_src = tempfile::tempdir().unwrap();
        let staging_src = "refs/eml/storage/resume-empty-src/staging";
        let repo_src = bare_repo(dir_src.path(), gix::hash::Kind::Sha256);
        let k = 2u64;
        let real = FixtureHasher::new(32);

        let mut log = new_log(&repo_src, staging_src, k, real.clone()).await;
        for i in 0..4u32 {
            log.append_leaf(format!("leaf-{i}").as_bytes())
                .await
                .unwrap();
        }
        let sealed = log.seal().await.unwrap();

        let dir_dst = tempfile::tempdir().unwrap();
        let staging_dst = "refs/eml/storage/resume-empty-dst/staging";
        let repo_dst = bare_repo(dir_dst.path(), gix::hash::Kind::Sha256);
        let storage_dst = GitStorage::new(repo_dst.clone(), staging_dst, k)
            .expect("the plain constructor must open an empty ref");
        let mut resumed =
            NaryMerkleLog::resume(&sealed, storage_dst, vec![(0, Box::new(real.clone()))])
                .await
                .expect("resume onto an empty ref");

        let local_dst = repo_dst.to_thread_local();
        let tip = support::ref_target(&local_dst, staging_dst).unwrap();
        // n=4, arity 2: one peak, T(0,2).
        let peak_path = format!("peaks/{}/{}", hex(2, 2), hex(0, 2));
        let peak = support::resolve_path(&local_dst, tip, &peak_path)
            .unwrap_or_else(|| panic!("no peak at {peak_path}"));
        let entries = support::read_tree(&local_dst, peak.oid);
        assert!(
            !entries.iter().any(|e| e.name == "leaf"),
            "T(0,2) resumed onto an empty ref must carry no leaf"
        );
        assert!(
            !entries.iter().any(|e| e.name == hex(0, 2))
                && !entries.iter().any(|e| e.name == hex(1, 2)),
            "T(0,2) resumed onto an empty ref must be opaque: no hex(c,2) children"
        );
        assert!(
            entries.iter().any(|e| e.name == "digest"),
            "T(0,2) resumed onto an empty ref must still carry digest/"
        );

        // Forward appends on a resumed (Subtree-kind) log go through
        // append_subtree and must themselves be opaque too (SG10 again, on
        // the same instance that just inherited an opaque peak).
        resumed
            .append_subtree(&Subtree::Leaf(b"forward-1".to_vec()))
            .await
            .unwrap();
        let after_forward_tip = support::ref_target(&local_dst, staging_dst).unwrap();
        let forward_path = format!("peaks/{}/{}", hex(0, 2), hex(0, 2));
        let forward_node = support::resolve_path(&local_dst, after_forward_tip, &forward_path)
            .unwrap_or_else(|| panic!("no peak at {forward_path}"));
        let forward_entries = support::read_tree(&local_dst, forward_node.oid);
        assert!(
            !forward_entries.iter().any(|e| e.name == "leaf"),
            "a forward subtree append on a resumed log must be opaque too"
        );
    });
}

/// A fork: sealing a log under one ref and resuming into a brand-new ref in
/// the SAME repository is a fresh-target resume like any other. Freshness
/// is scoped to the target ref's own committed state, never to the
/// repository as a whole, so the two logs share one object store but never
/// each other's committed history: ref A stays byte-for-byte untouched by
/// the fork and by every subsequent append to ref B, B's inherited peak is
/// opaque, a consistency proof bridges A's sealed commitment to B's first
/// forward commitment, and resuming the same seal back onto ref A -- which
/// still holds the source log -- is still refused.
#[test]
fn resume_forks_into_a_new_ref_within_the_same_repository() {
    smol::block_on(async {
        let dir = tempfile::tempdir().unwrap();
        let repo = bare_repo(dir.path(), gix::hash::Kind::Sha256);
        let k = 2u64;
        let real = FixtureHasher::new(32);
        let staging_a = "refs/eml/storage/fork-a/staging";
        let staging_b = "refs/eml/storage/fork-b/staging";

        let mut log_a = new_log(&repo, staging_a, k, real.clone()).await;
        for i in 0..4u32 {
            log_a
                .append_leaf(format!("leaf-{i}").as_bytes())
                .await
                .unwrap();
        }
        let n = log_a.count();
        let sealed_member = log_a.root_for_at(0, n).await.unwrap();
        let sealed = log_a.seal().await.unwrap();

        let local = repo.to_thread_local();
        let ref_a_before = support::ref_target(&local, staging_a).unwrap();

        // Fork: resume the same seal into a brand-new ref, staging_b, in
        // the SAME repository -- a distinct key over the same underlying
        // object store.
        let storage_b = GitStorage::new(repo.clone(), staging_b, k)
            .expect("staging_b has never been written; GitStorage::new must open it fresh");
        let mut resumed_b =
            NaryMerkleLog::resume(&sealed, storage_b, vec![(0, Box::new(real.clone()))])
                .await
                .expect("resuming into a fresh ref in the same repository must succeed");

        let ref_a_after_fork = support::ref_target(&local, staging_a).unwrap();
        assert_eq!(
            ref_a_before, ref_a_after_fork,
            "forking into ref B must leave ref A's log byte-for-byte untouched"
        );

        // B's inherited peak is opaque (n=4, arity 2: one peak, T(0,2)).
        let tip_b = support::ref_target(&local, staging_b).unwrap();
        let peak_path = format!("peaks/{}/{}", hex(2, 2), hex(0, 2));
        let peak = support::resolve_path(&local, tip_b, &peak_path)
            .unwrap_or_else(|| panic!("no peak at {peak_path}"));
        let entries = support::read_tree(&local, peak.oid);
        assert!(
            !entries.iter().any(|e| e.name == "leaf"),
            "B's inherited peak must carry no leaf"
        );
        assert!(
            !entries.iter().any(|e| e.name == hex(0, 2))
                && !entries.iter().any(|e| e.name == hex(1, 2)),
            "B's inherited peak must be opaque: no hex(c,2) children"
        );
        assert!(
            entries.iter().any(|e| e.name == "digest"),
            "B's inherited peak must still carry digest/"
        );

        // Appends to B work.
        resumed_b
            .append_subtree(&Subtree::Leaf(b"fork-forward-0".to_vec()))
            .await
            .unwrap();
        resumed_b
            .append_subtree(&Subtree::Leaf(b"fork-forward-1".to_vec()))
            .await
            .unwrap();
        assert_eq!(resumed_b.count(), n + 2);

        // Ref A is still untouched after appends to B.
        let ref_a_after_appends = support::ref_target(&local, staging_a).unwrap();
        assert_eq!(
            ref_a_before, ref_a_after_appends,
            "appends to the forked ref B must never touch ref A"
        );

        // A consistency proof bridges A's sealed commitment to B's first
        // (forward) commitment.
        let proof = resumed_b
            .consistency_proof(n, n + 2)
            .await
            .unwrap()
            .expect("consistency must bridge the fork's resume boundary");
        let new_root = resumed_b.root_for_at(0, n + 2).await.unwrap();
        assert!(
            verify_consistency(
                &real,
                n,
                n + 2,
                k,
                &proof.boundary_hash,
                &proof.peak_path,
                &proof.new_peaks,
                proof.split_index,
                &sealed_member,
                &new_root,
            ),
            "consistency proof from A's sealed commitment to B's first commitment must verify"
        );

        // Resuming the SAME seal back onto ref A -- which still holds the
        // source log's own committed objects -- is still refused.
        let stale_storage =
            GitStorage::new(repo.clone(), staging_a, k).expect("open GitStorage over ref A");
        let result =
            NaryMerkleLog::resume(&sealed, stale_storage, vec![(0, Box::new(real.clone()))]).await;
        assert!(
            result.is_err(),
            "resuming the seal back onto ref A, which still holds the source log, must be refused"
        );
        let ref_a_final = support::ref_target(&local, staging_a).unwrap();
        assert_eq!(
            ref_a_before, ref_a_final,
            "the refused resume back onto ref A must leave it untouched"
        );
    });
}
