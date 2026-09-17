//! Kind derivation and non-optional log metadata (head's ruling,
//! 2026-09-17, requirements A and B), on [`GitStorage`]. `polydigest`'s own
//! `tests/kind_and_meta.rs` carries the identical claim over `MemoryStorage`;
//! `storage-fjall`'s own copy carries it over `FjallStorage`. See that
//! file's doc comment for the full derivation this pins.

mod common;

use std::path::Path;
use std::process::Command;

use common::{WideHasher, init_repo};
use gix::hash::Kind as HashKind;
use polydigest::{Hasher, LogError, LogKind, NaryMerkleLog, Storage, Subtree, TreeConfig};
use storage_git::{GitStorage, LogMetadata};

fn hashers(ids: impl IntoIterator<Item = u64>) -> Vec<(u64, Box<dyn Hasher>)> {
    ids.into_iter()
        .map(|id| (id, Box::new(WideHasher) as Box<dyn Hasher>))
        .collect()
}

/// [KIND DERIVATION] A flat log reopens as `LogKind::Flat` from a `GitStorage`
/// alone -- `len() > 0` is the flat signal, never a stored byte.
#[test]
fn flat_log_reopens_as_flat() {
    smol::block_on(async {
        let (dir, repo) = init_repo(HashKind::Sha1);
        let staging = "refs/eml/storage/kind-meta/flat/staging";
        let mut log = NaryMerkleLog::new(
            GitStorage::new(repo, staging, 2).unwrap(),
            Box::new(WideHasher),
            TreeConfig { arity: 2 },
        )
        .await
        .unwrap();
        for i in 0..5u32 {
            log.append_leaf(format!("leaf-{i}").as_bytes())
                .await
                .unwrap();
        }
        let expected_count = log.count();
        let expected_root = log.root();
        drop(log);

        let storage = GitStorage::open(dir.path(), staging, 2).unwrap();
        assert!(storage.len().await.unwrap() > 0);
        let mut reopened = NaryMerkleLog::from_storage(storage, hashers([0]))
            .await
            .unwrap();
        assert_eq!(reopened.kind(), LogKind::Flat);
        assert_eq!(reopened.count(), expected_count);
        assert_eq!(reopened.root(), expected_root);

        let err = reopened
            .append_subtree(&Subtree::Leaf(b"x".to_vec()))
            .await
            .unwrap_err();
        assert!(matches!(err, LogError::CorruptedMetadata { .. }));
    });
}

/// [KIND DERIVATION] A subtree-appended-from-genesis log reopens as
/// `LogKind::Subtree` -- a nonzero append count with `len() == 0`.
#[test]
fn subtree_from_genesis_log_reopens_as_subtree() {
    smol::block_on(async {
        let (dir, repo) = init_repo(HashKind::Sha1);
        let staging = "refs/eml/storage/kind-meta/subtree/staging";
        let mut log = NaryMerkleLog::new(
            GitStorage::new(repo, staging, 2).unwrap(),
            Box::new(WideHasher),
            TreeConfig { arity: 2 },
        )
        .await
        .unwrap();
        for i in 0..4u32 {
            log.append_subtree(&Subtree::Leaf(format!("s-{i}").into_bytes()))
                .await
                .unwrap();
        }
        let expected_count = log.count();
        let expected_root = log.root();
        drop(log);

        let storage = GitStorage::open(dir.path(), staging, 2).unwrap();
        assert_eq!(storage.len().await.unwrap(), 0);
        assert!(storage.append_count().await.unwrap() > 0);
        let mut reopened = NaryMerkleLog::from_storage(storage, hashers([0]))
            .await
            .unwrap();
        assert_eq!(reopened.kind(), LogKind::Subtree);
        assert_eq!(reopened.count(), expected_count);
        assert_eq!(reopened.root(), expected_root);

        let err = reopened.append_leaf(b"x").await.unwrap_err();
        assert!(matches!(err, LogError::CorruptedMetadata { .. }));
    });
}

/// [KIND DERIVATION] A log resumed onto fresh `GitStorage` reopens as
/// `LogKind::Subtree`: the inherited prefix and any forward subtree appends
/// never populate the leaf keyspace.
#[test]
fn resumed_log_reopens_as_subtree() {
    smol::block_on(async {
        let (_dir_src, repo_src) = init_repo(HashKind::Sha1);
        let mut src = NaryMerkleLog::new(
            GitStorage::new(repo_src, "refs/eml/storage/kind-meta/src/staging", 2).unwrap(),
            Box::new(WideHasher),
            TreeConfig { arity: 2 },
        )
        .await
        .unwrap();
        for i in 0..3u32 {
            src.append_leaf(format!("leaf-{i}").as_bytes())
                .await
                .unwrap();
        }
        let sealed = src.seal().await.unwrap();

        let (dir_dst, repo_dst) = init_repo(HashKind::Sha1);
        let staging_dst = "refs/eml/storage/kind-meta/resumed/staging";
        let mut resumed = NaryMerkleLog::resume(
            &sealed,
            GitStorage::new(repo_dst, staging_dst, 2).unwrap(),
            hashers([0]),
        )
        .await
        .unwrap();
        for i in 0..2u32 {
            resumed
                .append_subtree(&Subtree::Leaf(format!("fwd-{i}").into_bytes()))
                .await
                .unwrap();
        }
        let expected_count = resumed.count();
        let expected_root = resumed.root();
        drop(resumed);

        let storage = GitStorage::open(dir_dst.path(), staging_dst, 2).unwrap();
        assert_eq!(storage.len().await.unwrap(), 0);
        let reopened = NaryMerkleLog::from_storage(storage, hashers([0]))
            .await
            .unwrap();
        assert_eq!(reopened.kind(), LogKind::Subtree);
        assert_eq!(reopened.count(), expected_count);
        assert_eq!(reopened.root(), expected_root);
    });
}

/// [KIND DERIVATION] An empty log (`append_count == 0`) accepts either
/// append kind on reopen, same as a freshly constructed one.
///
/// Re-expressed against two INDEPENDENTLY INITIALIZED staging refs, never
/// two `open` calls against the same ref: `GitStorage` is deliberately
/// `!Clone` for single-writer ownership, and `observed_tip` is captured
/// once, in `Self::new`, from a lookup of `staging_ref` alone (`lib.rs`'s
/// own doc comment on that field, `lib.rs:100-111`, states the isolation
/// this relies on -- "a repository that hosts several logs side by side,
/// each under its own staging ref ... reports freshness correctly per
/// ref -- one ref's committed log is never visible through another"). Two
/// opens on ONE shared ref cannot fork independent empty handles that each
/// accept a different kind: whichever leg writes first moves that ref, and
/// the second leg's own `apply` then hits a genuine CAS conflict
/// (`TipMoved`) before it ever gets to observe which kind was rejected --
/// there is no ordering of two opens on one ref that reaches the intended
/// outcome. Two distinct refs in the same repository, each independently
/// carried genesis -> drop -> reopen -> first append, is what actually
/// exercises the property, and nothing else in this crate reopens a
/// still-empty ref through `open`/`from_storage` before the first append.
#[test]
fn empty_log_reopens_accepting_either_append() {
    smol::block_on(async {
        let (dir, repo) = init_repo(HashKind::Sha1);

        // Leg 1: its own ref, genesis -> drop -> reopen -> first append is
        // a LEAF.
        let staging_leaf = "refs/eml/storage/kind-meta/empty/leaf/staging";
        let src_leaf = NaryMerkleLog::new(
            GitStorage::new(repo.clone(), staging_leaf, 2).unwrap(),
            Box::new(WideHasher),
            TreeConfig { arity: 2 },
        )
        .await
        .unwrap();
        drop(src_leaf);

        let storage_leaf = GitStorage::open(dir.path(), staging_leaf, 2).unwrap();
        assert_eq!(storage_leaf.append_count().await.unwrap(), 0);
        let mut flat_leg = NaryMerkleLog::from_storage(storage_leaf, hashers([0]))
            .await
            .unwrap();
        let genesis_tip_leaf = flat_leg.storage().tip_tree();
        flat_leg.append_leaf(b"a").await.unwrap();
        assert_eq!(flat_leg.kind(), LogKind::Flat);

        // Leg 2: a SEPARATE, independently initialized ref in the same
        // repository, genesis -> drop -> reopen -> first append is a
        // SUBTREE.
        let staging_subtree = "refs/eml/storage/kind-meta/empty/subtree/staging";
        let src_subtree = NaryMerkleLog::new(
            GitStorage::new(repo.clone(), staging_subtree, 2).unwrap(),
            Box::new(WideHasher),
            TreeConfig { arity: 2 },
        )
        .await
        .unwrap();
        drop(src_subtree);

        let storage_subtree = GitStorage::open(dir.path(), staging_subtree, 2).unwrap();
        assert_eq!(storage_subtree.append_count().await.unwrap(), 0);
        let mut subtree_leg = NaryMerkleLog::from_storage(storage_subtree, hashers([0]))
            .await
            .unwrap();
        let genesis_tip_subtree = subtree_leg.storage().tip_tree();

        // [EITHER] The word "either" in this test's own name means the two
        // legs' empty states are the SAME state, not merely two states that
        // each separately accept one kind -- so the two genesis tips must be
        // byte-identical before either leg's first append. Restores a
        // property fd6955c's two-ref re-expression asserted implicitly in
        // its name but never actually checked (found at this branch's merge
        // gate, AC17).
        assert_eq!(
            genesis_tip_leaf, genesis_tip_subtree,
            "the two independently-initialized empty logs must be the identical genesis state, \
             not merely two separate states that happen to each accept one kind"
        );

        subtree_leg
            .append_subtree(&Subtree::Leaf(b"b".to_vec()))
            .await
            .unwrap();
        assert_eq!(subtree_leg.kind(), LogKind::Subtree);
    });
}

/// [NON-OPTIONAL META] `append_count` is authoritative after every one of
/// the five operations and after a reopen from disk.
#[test]
fn append_count_is_authoritative_after_every_operation_and_reopen() {
    smol::block_on(async {
        let (dir, repo) = init_repo(HashKind::Sha1);
        let staging = "refs/eml/storage/kind-meta/append-count/staging";
        let mut log = NaryMerkleLog::new(
            GitStorage::new(repo, staging, 2).unwrap(),
            Box::new(WideHasher),
            TreeConfig { arity: 2 },
        )
        .await
        .unwrap();
        assert_eq!(log.storage().append_count().await.unwrap(), 0);

        log.append_leaf(b"a").await.unwrap();
        assert_eq!(log.storage().append_count().await.unwrap(), 1);

        log.add_algorithm(1, Box::new(WideHasher)).await.unwrap();
        assert_eq!(log.storage().append_count().await.unwrap(), 1);

        log.append_leaf(b"b").await.unwrap();
        assert_eq!(log.storage().append_count().await.unwrap(), 2);

        log.remove_algorithm(1).await.unwrap();
        log.append_leaf(b"c").await.unwrap();
        log.resume_algorithm(1).await.unwrap();
        assert_eq!(log.storage().append_count().await.unwrap(), 3);
        drop(log);

        let reopened_storage = GitStorage::open(dir.path(), staging, 2).unwrap();
        assert_eq!(reopened_storage.append_count().await.unwrap(), 3);
        let reopened = NaryMerkleLog::from_storage(reopened_storage, hashers([0, 1]))
            .await
            .unwrap();
        assert_eq!(reopened.count(), 3);
    });
}

/// [METADATA ACCESSOR] `GitStorage::metadata()` reports the live instance's
/// own `(count, kind)`, matching the polydigest-level `NaryMerkleLog`
/// accessors driving it -- so a caller (e.g. the checkpoint layer) never
/// needs to decode `meta`'s bytes or re-derive kind itself.
#[test]
fn git_storage_metadata_accessor_matches_the_live_log() {
    smol::block_on(async {
        let (_dir, repo) = init_repo(HashKind::Sha1);
        let staging = "refs/eml/storage/kind-meta/accessor/staging";
        let mut log = NaryMerkleLog::new(
            GitStorage::new(repo, staging, 2).unwrap(),
            Box::new(WideHasher),
            TreeConfig { arity: 2 },
        )
        .await
        .unwrap();
        for i in 0..3u32 {
            log.append_leaf(format!("leaf-{i}").as_bytes())
                .await
                .unwrap();
        }

        let meta = log.storage().metadata();
        assert_eq!(meta.count, log.count());
        assert_eq!(meta.kind, log.kind());
    });
}

/// [METADATA ACCESSOR] `GitReadOnlyView::metadata()` reports the checkpoint
/// tree's own `(count, kind)` -- the read-only-view peer of
/// `GitStorage::metadata`, independent of the live instance that produced
/// the tree.
#[test]
fn git_read_only_view_metadata_accessor_matches_the_checkpoint() {
    smol::block_on(async {
        let (_dir, repo) = init_repo(HashKind::Sha1);
        let staging = "refs/eml/storage/kind-meta/accessor-view/staging";
        let mut log = NaryMerkleLog::new(
            GitStorage::new(repo, staging, 2).unwrap(),
            Box::new(WideHasher),
            TreeConfig { arity: 2 },
        )
        .await
        .unwrap();
        for i in 0..3u32 {
            log.append_subtree(&Subtree::Leaf(format!("s-{i}").into_bytes()))
                .await
                .unwrap();
        }
        let expected_count = log.count();
        let expected_kind = log.kind();
        let tip = log.storage().tip_tree().unwrap();

        let view = log.storage().open_at(tip).unwrap();
        let meta = view.metadata();
        assert_eq!(meta.count, expected_count);
        assert_eq!(meta.kind, expected_kind);
    });
}

// ============================================================================
// [DERIVATION SURFACE] Merge-gate condition AC30
// (`.ledger/deposits/git-backend/lead-maintainer/storage-git-apply-contract-gate.md`):
// `derive_log_metadata`'s `count == 0 || has_leaves` condition -- this
// branch's headline contract -- was found to redden exactly one test when
// mutated to `count == 0` alone
// (`git_storage_metadata_accessor_matches_the_live_log` above), because
// `NaryMerkleLog::from_storage`/`::kind()` compute their own kind
// independently and never consult `GitStorage::metadata()` at all. Every
// test below asserts on `.metadata()`/`GitReadOnlyView::metadata()`
// directly -- never on `log.kind()` -- across genesis, both append kinds,
// reopen, gc, and resume, so a wrong derivation is caught at each of those
// points rather than through a single accessor-parity check.
// ============================================================================

fn gc(dir: &Path) {
    let out = Command::new("git")
        .arg("--git-dir")
        .arg(dir)
        .args(["gc", "--prune=now", "--aggressive", "-q"])
        .output()
        .expect("run git gc");
    assert!(
        out.status.success(),
        "git gc failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
}

/// [DERIVATION SURFACE] A fresh instance's own `.metadata()`, before any
/// write, is `{count: 0, kind: Flat}` -- read directly, never through a log.
#[test]
fn git_storage_metadata_is_flat_at_genesis_before_any_write() {
    let (_dir, repo) = init_repo(HashKind::Sha1);
    let storage = GitStorage::new(
        repo,
        "refs/eml/storage/kind-meta/derivation/genesis/staging",
        2,
    )
    .unwrap();
    assert_eq!(
        storage.metadata(),
        LogMetadata {
            count: 0,
            kind: LogKind::Flat
        }
    );
}

/// [DERIVATION SURFACE] Reopening a flat log through `GitStorage::open`
/// alone (never through `NaryMerkleLog`) reports `.metadata().kind ==
/// Flat` directly.
#[test]
fn git_storage_metadata_is_flat_directly_after_reopen_of_a_flat_log() {
    smol::block_on(async {
        let (dir, repo) = init_repo(HashKind::Sha1);
        let staging = "refs/eml/storage/kind-meta/derivation/flat-reopen/staging";
        let mut log = NaryMerkleLog::new(
            GitStorage::new(repo, staging, 2).unwrap(),
            Box::new(WideHasher),
            TreeConfig { arity: 2 },
        )
        .await
        .unwrap();
        for i in 0..3u32 {
            log.append_leaf(format!("leaf-{i}").as_bytes())
                .await
                .unwrap();
        }
        drop(log);

        let reopened = GitStorage::open(dir.path(), staging, 2).unwrap();
        assert_eq!(
            reopened.metadata(),
            LogMetadata {
                count: 3,
                kind: LogKind::Flat
            }
        );
    });
}

/// [DERIVATION SURFACE] Reopening a subtree-from-genesis log through
/// `GitStorage::open` alone reports `.metadata().kind == Subtree` directly.
#[test]
fn git_storage_metadata_is_subtree_directly_after_reopen_of_a_subtree_log() {
    smol::block_on(async {
        let (dir, repo) = init_repo(HashKind::Sha1);
        let staging = "refs/eml/storage/kind-meta/derivation/subtree-reopen/staging";
        let mut log = NaryMerkleLog::new(
            GitStorage::new(repo, staging, 2).unwrap(),
            Box::new(WideHasher),
            TreeConfig { arity: 2 },
        )
        .await
        .unwrap();
        for i in 0..3u32 {
            log.append_subtree(&Subtree::Leaf(format!("s-{i}").into_bytes()))
                .await
                .unwrap();
        }
        drop(log);

        let reopened = GitStorage::open(dir.path(), staging, 2).unwrap();
        assert_eq!(
            reopened.metadata(),
            LogMetadata {
                count: 3,
                kind: LogKind::Subtree
            }
        );
    });
}

/// [DERIVATION SURFACE] Reopening a resumed log through `GitStorage::open`
/// alone reports `.metadata().kind == Subtree` directly -- the inherited
/// prefix never populates the leaf keyspace.
#[test]
fn git_storage_metadata_is_subtree_directly_after_reopen_of_a_resumed_log() {
    smol::block_on(async {
        let (_dir_src, repo_src) = init_repo(HashKind::Sha1);
        let mut src = NaryMerkleLog::new(
            GitStorage::new(
                repo_src,
                "refs/eml/storage/kind-meta/derivation/resume-src/staging",
                2,
            )
            .unwrap(),
            Box::new(WideHasher),
            TreeConfig { arity: 2 },
        )
        .await
        .unwrap();
        for i in 0..3u32 {
            src.append_leaf(format!("leaf-{i}").as_bytes())
                .await
                .unwrap();
        }
        let sealed = src.seal().await.unwrap();

        let (dir_dst, repo_dst) = init_repo(HashKind::Sha1);
        let staging_dst = "refs/eml/storage/kind-meta/derivation/resume-dst/staging";
        let resumed = NaryMerkleLog::resume(
            &sealed,
            GitStorage::new(repo_dst, staging_dst, 2).unwrap(),
            hashers([0]),
        )
        .await
        .unwrap();
        drop(resumed);

        let reopened = GitStorage::open(dir_dst.path(), staging_dst, 2).unwrap();
        assert_eq!(
            reopened.metadata(),
            LogMetadata {
                count: 3,
                kind: LogKind::Subtree
            }
        );
    });
}

/// [DERIVATION SURFACE] A flat log's derived kind survives a `git gc
/// --prune=now`: gc only reclaims unreachable objects, and every leaf/node
/// this layer ever wrote stays reachable from the staging ref (the
/// tip-tree model), so `.metadata()` read after gc must agree with the one
/// read before it.
#[test]
fn git_storage_metadata_is_flat_directly_after_gc() {
    smol::block_on(async {
        let (dir, repo) = init_repo(HashKind::Sha1);
        let staging = "refs/eml/storage/kind-meta/derivation/gc/staging";
        let mut log = NaryMerkleLog::new(
            GitStorage::new(repo, staging, 2).unwrap(),
            Box::new(WideHasher),
            TreeConfig { arity: 2 },
        )
        .await
        .unwrap();
        for i in 0..3u32 {
            log.append_leaf(format!("leaf-{i}").as_bytes())
                .await
                .unwrap();
        }
        drop(log);

        gc(dir.path());

        let reopened = GitStorage::open(dir.path(), staging, 2).unwrap();
        assert_eq!(
            reopened.metadata(),
            LogMetadata {
                count: 3,
                kind: LogKind::Flat
            }
        );
    });
}

/// [DERIVATION SURFACE] `GitReadOnlyView::metadata()` reports `Flat` for a
/// flat checkpoint, read directly -- the existing
/// `git_read_only_view_metadata_accessor_matches_the_checkpoint` test above
/// only exercises the subtree case.
#[test]
fn git_read_only_view_metadata_is_flat_for_a_flat_checkpoint() {
    smol::block_on(async {
        let (_dir, repo) = init_repo(HashKind::Sha1);
        let staging = "refs/eml/storage/kind-meta/derivation/view-flat/staging";
        let mut log = NaryMerkleLog::new(
            GitStorage::new(repo, staging, 2).unwrap(),
            Box::new(WideHasher),
            TreeConfig { arity: 2 },
        )
        .await
        .unwrap();
        for i in 0..3u32 {
            log.append_leaf(format!("leaf-{i}").as_bytes())
                .await
                .unwrap();
        }
        let tip = log.storage().tip_tree().unwrap();

        let view = log.storage().open_at(tip).unwrap();
        assert_eq!(
            view.metadata(),
            LogMetadata {
                count: 3,
                kind: LogKind::Flat
            }
        );
    });
}
