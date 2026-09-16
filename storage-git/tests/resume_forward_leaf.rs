//! Storage-git-specific coverage for a resumed log's forward appends under
//! eml's own, restored contract: a resumed log is [`polydigest::LogKind::Subtree`]
//! for its whole forward life (`polydigest::NaryMerkleLog::resume`'s own doc,
//! `polydigest/src/tree.rs:110-122`), appending real leaf values only through
//! `append_subtree(&Subtree::Leaf(bytes))` -- whose digest is byte-identical
//! to a flat leaf append, but which stores no raw leaf bytes at all.
//! `append_leaf` on a resumed log is refused outright by a pure in-memory
//! guard (`self.kind == LogKind::Subtree && self.count > 0`, `tree.rs:778`)
//! identical for every `Storage` backend and checked before any storage call
//! is made, so it carries no storage-git-specific behavior and needs no test
//! here (its refusal is exercised at the `polydigest` level instead).
//!
//! 1. GB71: a node created and folded away within one write -- a chained, double resume triggers it
//!    -- must not be lost by `storage-git`, unlike the old `inherited/`-archive design. `086c181`
//!    (`fix(storage-git): decompose children per slot`) fixed the general case this pins; kept here
//!    as a regression guard, not as new coverage.
//! 2. `verify_audit_payload` and `verify_non_divergence` on a resumed log with forward subtree
//!    appends: pinned for parity between `storage-git` and `MemoryStorage`, covering a from-genesis
//!    replay, a payload-based replay, and a checkpoint-start replay.

mod common;

use common::{WideHasher, init_repo};
use gix::hash::Kind as HashKind;
use polydigest::{MemoryStorage, NaryMerkleLog, Storage, Subtree, TreeConfig, frontier_for_size};
use storage_git::GitStorage;

/// Seal a fresh `n`-leaf, arity-`k` `GitStorage` log and return `(sealed,
/// tmpdir)` -- the tmpdir must outlive every read from the sealed log's own
/// repository, so the caller holds it until done.
async fn seal_git(n: u64, k: u64, ref_name: &str) -> polydigest::Sealed {
    let (_dir, repo) = init_repo(HashKind::Sha1);
    let git = GitStorage::new(repo, ref_name, k).unwrap();
    let mut log = NaryMerkleLog::new(git, Box::new(WideHasher), TreeConfig { arity: k })
        .await
        .unwrap();
    for i in 0..n {
        log.append_leaf(format!("orig-{i}").as_bytes())
            .await
            .unwrap();
    }
    log.seal().await.unwrap()
}

/// Same as [`seal_git`], over `MemoryStorage`, so both backends seal the
/// identical entry sequence.
async fn seal_mem(n: u64, k: u64) -> polydigest::Sealed {
    let mut log = NaryMerkleLog::new(
        MemoryStorage::new(),
        Box::new(WideHasher),
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

// ============================================================================
// 1. GB71: a node created and folded away within one write -- reproduced with `append_subtree`
//    alone (a resumed log's only forward-append path), via a *double* resume: seal, resume, append
//    to size 3, reseal from that live frontier, resume a second instance, append once more to size
//    4. `MemoryStorage` never drops a node it was given, so it is the parity oracle this test's
//    every assertion is checked against.
// ============================================================================

/// The double-resume GB71 sequence, applied identically to a git-backed and
/// a memory-backed log; returns `(git_log, mem_log)` for the caller to
/// assert against. `_dirs` must be named (not `_`) by the caller so the
/// temporary repositories outlive the reads.
async fn run_gb71_sequence() -> (
    NaryMerkleLog<GitStorage>,
    NaryMerkleLog<MemoryStorage>,
    Vec<tempfile::TempDir>,
) {
    let mut dirs = Vec::new();
    let k = 2u64;

    // Stage 0: a two-leaf log, sealed (one peak).
    let (dir0, repo0) = init_repo(HashKind::Sha1);
    dirs.push(dir0);
    let git0 = GitStorage::new(repo0, "refs/eml/storage/gb71/0", k).unwrap();
    let mut git_log0 = NaryMerkleLog::new(git0, Box::new(WideHasher), TreeConfig { arity: k })
        .await
        .unwrap();
    let mut mem_log0 = NaryMerkleLog::new(
        MemoryStorage::new(),
        Box::new(WideHasher),
        TreeConfig { arity: k },
    )
    .await
    .unwrap();
    for data in [b"a".as_slice(), b"b".as_slice()] {
        git_log0.append_leaf(data).await.unwrap();
        mem_log0.append_leaf(data).await.unwrap();
    }
    let git_sealed0 = git_log0.seal().await.unwrap();
    let mem_sealed0 = mem_log0.seal().await.unwrap();

    // Stage 1: resume, append a subtree to size 3 (two peaks: (0,1) and
    // (2,0)), reseal from that live frontier.
    let (dir1, repo1) = init_repo(HashKind::Sha1);
    dirs.push(dir1);
    let git1 = GitStorage::new(repo1, "refs/eml/storage/gb71/1", k).unwrap();
    let mut git_log1 = NaryMerkleLog::resume(&git_sealed0, git1, vec![(0, Box::new(WideHasher))])
        .await
        .unwrap();
    let mut mem_log1 = NaryMerkleLog::resume(
        &mem_sealed0,
        MemoryStorage::new(),
        vec![(0, Box::new(WideHasher))],
    )
    .await
    .unwrap();
    git_log1
        .append_subtree(&Subtree::Leaf(b"c".to_vec()))
        .await
        .unwrap();
    mem_log1
        .append_subtree(&Subtree::Leaf(b"c".to_vec()))
        .await
        .unwrap();
    assert_eq!(
        frontier_for_size(3, k).len(),
        2,
        "fixture sanity: size 3 has two peaks"
    );
    let git_sealed1 = git_log1.seal().await.unwrap();
    let mem_sealed1 = mem_log1.seal().await.unwrap();

    // Stage 2: resume a SECOND instance, append once more to size 4 (merges
    // both peaks into one; the newly appended leaf's own node at
    // (left=3, height=0) is created and folded away within this one write).
    let (dir2, repo2) = init_repo(HashKind::Sha1);
    dirs.push(dir2);
    let git2 = GitStorage::new(repo2, "refs/eml/storage/gb71/2", k).unwrap();
    let mut git_log2 = NaryMerkleLog::resume(&git_sealed1, git2, vec![(0, Box::new(WideHasher))])
        .await
        .unwrap();
    let mut mem_log2 = NaryMerkleLog::resume(
        &mem_sealed1,
        MemoryStorage::new(),
        vec![(0, Box::new(WideHasher))],
    )
    .await
    .unwrap();
    git_log2
        .append_subtree(&Subtree::Leaf(b"d".to_vec()))
        .await
        .unwrap();
    mem_log2
        .append_subtree(&Subtree::Leaf(b"d".to_vec()))
        .await
        .unwrap();
    assert_eq!(git_log2.count(), 4);
    assert_eq!(mem_log2.count(), 4);

    (git_log2, mem_log2, dirs)
}

/// GB71: `get_node(0, 3, 0)` -- the just-appended leaf's own coordinate --
/// must read back identically on both backends.
#[test]
fn gb71_new_leaf_node_folded_away_within_one_write_matches_memory() {
    smol::block_on(async {
        let (git_log, mem_log, _dirs) = run_gb71_sequence().await;
        let g = git_log.storage().get_node(0, 3, 0).await.unwrap();
        let m = mem_log.storage().get_node(0, 3, 0).await.unwrap();
        assert_eq!(
            g, m,
            "get_node(alg=0, left=3, height=0) diverged: git={g:?} mem={m:?}"
        );
    });
}

/// GB71: a consistency proof from the pre-merge size (3) to the post-merge
/// size (4) must succeed on both backends alike.
#[test]
fn gb71_consistency_proof_across_the_merge_matches_memory() {
    smol::block_on(async {
        let (git_log, mem_log, _dirs) = run_gb71_sequence().await;
        let g = git_log.consistency_proof_for(0, 3, 4).await;
        let m = mem_log.consistency_proof_for(0, 3, 4).await;
        match (&g, &m) {
            (Ok(gv), Ok(mv)) => assert_eq!(
                gv.is_some(),
                mv.is_some(),
                "consistency_proof_for(0,3,4) presence diverged"
            ),
            _ => panic!("consistency_proof_for(0,3,4) success diverged: git={g:?} mem={m:?}"),
        }
    });
}

// ============================================================================
// 2. `verify_audit_payload` and `verify_non_divergence` on a resumed log with forward subtree
//    appends: pinned for parity between `storage-git` and `MemoryStorage`. Under the fork's
//    (reverted) contract, forward appends went through `append_leaf`, driving the log's `kind` to
//    `Flat` and routing verification through the `is_flat` streaming branch (`get_leaf(i)` from
//    index 0), which produced an honest `Err` once it hit the opaque inherited prefix. Under eml's
//    restored contract, forward appends go through `append_subtree` and `kind` stays `Subtree` for
//    the resumed log's whole life, so verification instead takes the subtree branch
//    (`get_node(alg_id, i, 0)`). That branch's behavior on the two replay entry points differs by
//    exactly how it fails, not whether it fails:
//    - a from-genesis or payload-based replay still returns `Err` (a missing internal node in the
//      opaque inherited prefix is a storage-level `CorruptedMetadata`, not a `None` the subtree
//      branch's active-set check can turn into `Ok(false)`) for `verify_non_divergence`, but
//      `verify_audit_payload`'s own subtree branch treats that same missing coordinate as `None if
//      active_set.contains(&alg_id) => return Ok(false)` -- a false "diverged" verdict, not an
//      honest failure. This is a `polydigest`-level behavior, identical on both backends, pinned
//      here as today's actual result rather than the fork's (reverted) `Err` expectation; it is not
//      a `storage-git` defect, but is flagged in this dispatch's report as a discrepancy worth the
//      head's attention.
//    - a checkpoint-start replay still returns `Err(MissingTrustedRoot)`, never the misleading
//      `UnknownAlgorithm`, exactly as before.
// ============================================================================

/// Resume `n`-leaf, arity-`k` seals identically onto fresh `GitStorage` and
/// `MemoryStorage`, then append `m` forward leaves as single-leaf subtrees
/// (`Subtree::Leaf`) -- the only forward-append path a resumed log has under
/// eml's restored contract. Returns both logs and the git backend's
/// `TempDir` (which the caller must keep alive for every read from the git
/// log).
async fn resumed_with_forward_leaves(
    n: u64,
    k: u64,
    m: u64,
    ref_name: &str,
) -> (
    NaryMerkleLog<GitStorage>,
    NaryMerkleLog<MemoryStorage>,
    tempfile::TempDir,
) {
    let git_sealed = seal_git(n, k, &format!("{ref_name}/src")).await;
    let mem_sealed = seal_mem(n, k).await;

    let (dir, repo) = init_repo(HashKind::Sha1);
    let mut git_log = NaryMerkleLog::resume(
        &git_sealed,
        GitStorage::new(repo, format!("{ref_name}/dst"), k).unwrap(),
        vec![(0, Box::new(WideHasher))],
    )
    .await
    .expect("resume onto fresh git storage never fails for a well-formed Sealed");
    let mut mem_log = NaryMerkleLog::resume(
        &mem_sealed,
        MemoryStorage::new(),
        vec![(0, Box::new(WideHasher))],
    )
    .await
    .expect("resume onto fresh memory storage never fails for a well-formed Sealed");

    for i in 0..m {
        let bytes = format!("fwd-{i}").into_bytes();
        git_log
            .append_subtree(&Subtree::Leaf(bytes.clone()))
            .await
            .expect("append_subtree must succeed on the resumed git log");
        mem_log
            .append_subtree(&Subtree::Leaf(bytes))
            .await
            .expect("append_subtree must succeed on the resumed memory log");
    }
    (git_log, mem_log, dir)
}

/// `verify_non_divergence(None, &[])` -- a from-genesis replay -- must
/// return `Err` on a resumed log with forward subtree appends, on both
/// backends, never `Ok(false)` (a false "diverged" verdict) or `Ok(true)`
/// (a false "not diverged" verdict): the replay's subtree branch needs a
/// height-0 node for every position, and the opaque inherited prefix has
/// none, so the very first position streamed surfaces a storage-level
/// `CorruptedMetadata`.
#[test]
fn verify_non_divergence_from_genesis_errors_on_resumed_log_with_forward_leaves() {
    smol::block_on(async {
        let (git_log, mem_log, _dir) =
            resumed_with_forward_leaves(29, 2, 3, "refs/eml/storage/verify-resumed/from-genesis")
                .await;

        let git_result = git_log.verify_non_divergence(None, &[]).await;
        assert!(
            git_result.is_err(),
            "verify_non_divergence(None) on git must return Err for a resumed log with forward \
             leaves, not {git_result:?}"
        );

        let mem_result = mem_log.verify_non_divergence(None, &[]).await;
        assert!(
            mem_result.is_err(),
            "verify_non_divergence(None) on memory must return Err for a resumed log with forward \
             leaves, not {mem_result:?}"
        );
    });
}

/// `verify_audit_payload` on a resumed log with forward subtree appends
/// reports `Ok(false)` -- a false "diverged" verdict -- identically on both
/// backends, not the `Err` the fork's (reverted) flat-append contract used
/// to produce here. The payload itself builds successfully (it only reads
/// combined roots at a size, not individual leaves or nodes); the false
/// verdict comes from the streaming cell check's subtree branch treating the
/// opaque inherited prefix's missing height-0 nodes as a divergence rather
/// than surfacing the storage error `verify_non_divergence` does. Pinned as
/// today's actual, parity-checked behavior -- not endorsed as correct; see
/// this file's module doc and the dispatch report for the discrepancy this
/// surfaces.
#[test]
fn verify_audit_payload_reports_false_verdict_on_resumed_log_with_forward_leaves() {
    smol::block_on(async {
        let (git_log, mem_log, _dir) =
            resumed_with_forward_leaves(29, 2, 3, "refs/eml/storage/verify-resumed/audit-payload")
                .await;

        let git_payload = git_log
            .audit_payload([0u8; 32])
            .await
            .expect("audit_payload only reads combined roots, not individual leaves");
        let git_result = git_log.verify_audit_payload(&git_payload).await;
        assert!(
            matches!(git_result, Ok(false)),
            "verify_audit_payload on git must report a false-diverged verdict for a resumed log \
             with forward leaves, not {git_result:?}"
        );

        let mem_payload = mem_log
            .audit_payload([0u8; 32])
            .await
            .expect("audit_payload only reads combined roots, not individual leaves");
        let mem_result = mem_log.verify_audit_payload(&mem_payload).await;
        assert!(
            matches!(mem_result, Ok(false)),
            "verify_audit_payload on memory must report a false-diverged verdict for a resumed \
             log with forward leaves, not {mem_result:?}"
        );
    });
}

/// `verify_non_divergence(Some(resume_size), &[])` -- a
/// checkpoint-start replay from exactly where the log was resumed -- must
/// also return `Err`, never a verdict, on both backends: the error is
/// `MissingTrustedRoot`, not the misleading `UnknownAlgorithm`, since
/// algorithm 0 is in fact registered on this log (it is the only algorithm,
/// and every forward leaf above was appended through it).
#[test]
fn verify_non_divergence_from_checkpoint_error_is_not_unknown_algorithm() {
    smol::block_on(async {
        let n = 29u64;
        let (git_log, mem_log, _dir) =
            resumed_with_forward_leaves(n, 2, 3, "refs/eml/storage/verify-resumed/from-checkpoint")
                .await;

        let git_result = git_log.verify_non_divergence(Some(n), &[]).await;
        assert!(
            git_result.is_err(),
            "verify_non_divergence(Some({n})) on git must return Err for a resumed log with \
             forward leaves, not {git_result:?}"
        );
        assert!(
            !matches!(git_result, Err(polydigest::LogError::UnknownAlgorithm(_))),
            "verify_non_divergence(Some({n})) on git must not fail with UnknownAlgorithm: \
             algorithm 0 is registered and is the only algorithm on this log -- got {git_result:?}"
        );

        let mem_result = mem_log.verify_non_divergence(Some(n), &[]).await;
        assert!(
            mem_result.is_err(),
            "verify_non_divergence(Some({n})) on memory must return Err for a resumed log with \
             forward leaves, not {mem_result:?}"
        );
        assert!(
            !matches!(mem_result, Err(polydigest::LogError::UnknownAlgorithm(_))),
            "verify_non_divergence(Some({n})) on memory must not fail with UnknownAlgorithm: \
             algorithm 0 is registered and is the only algorithm on this log -- got {mem_result:?}"
        );
    });
}
