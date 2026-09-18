//! Pins the head's ruling, 2026-09-17, verbatim: "the index exists on top
//! at the application layer, not at this layer." A per-algorithm root
//! digest is an index over this layer's own data (the frontier this layer
//! already stores under `nodes/`), and this layer's own spec already says
//! as much for the historical case (`docs/specs/storage-git.md:568-578`:
//! producing such a root "is not this layer's to produce ... A consumer
//! that needs that historical root ... reconstructs it itself, outside
//! this layer"). This file generalizes that rule to the live case: a
//! checkpoint tree this layer commits MUST NOT carry a `roots` top-level
//! entry at all, at any point in a log's life -- not only for a size this
//! layer no longer serves as its tip.
//!
//! This is written against the CURRENT `storage-git`/`polydigest` API
//! (`WriteOp::{AppendLeaf,AppendSubtree,RemoveAlgorithm,ResumeAlgorithm}`'s
//! `checkpoint_roots`/`frozen_root`/`resumed_root` fields, and
//! `Storage::load_checkpoint_roots`), which an implementer follows this
//! dispatch into the same worktree to remove; every assertion here reads
//! the committed git tree directly, never the storage-level API this
//! removal deletes, so nothing here goes stale when that API surface
//! changes shape.
//!
//! `docs/specs/storage-git.md` itself is not amended by this dispatch
//! (out of scope, per the dispatch); this file's header cites the spec's
//! own existing §4.3 argument only to show the removal generalizes a rule
//! this layer already adopted, not to claim the spec text already states
//! the live-case rule under test.

#[path = "acceptance_support/mod.rs"]
mod support;

use polydigest::{Storage, WriteOp};
use storage_git::GitStorage;
use support::{FixtureHasher, bare_repo, new_log};

/// No top-level `roots` entry MUST exist in `C(n)`, for any tree this
/// layer committed -- read directly off the git tree, never through
/// `Storage::load_checkpoint_roots` or any other API this removal deletes.
fn assert_no_roots_entry(repo: &gix::Repository, tip: gix::ObjectId, when: &str) {
    assert!(
        support::find_entry(repo, tip, "roots").is_none(),
        "APPLICATION INDEX: C(n) must never carry a top-level `roots` entry ({when}) -- an index \
         over this layer's own data belongs at the application layer, not here (head's ruling, \
         2026-09-17)"
    );
}

/// Life point 1: genesis, one algorithm registered, no append yet (`n ==
/// 0`). SG14 already withholds `roots/` at `n == 0` under current code, so
/// this checkpoint is not expected to be red today -- it is here so the
/// walked sequence covers every life point the dispatch names, not just
/// the ones that currently fail.
#[test]
fn no_roots_entry_at_genesis_before_any_append() {
    smol::block_on(async {
        let dir = tempfile::tempdir().unwrap();
        let repo = bare_repo(dir.path(), gix::hash::Kind::Sha256);
        let log = new_log(
            &repo,
            "refs/eml/storage/no-index/genesis/staging",
            2,
            FixtureHasher::new(32),
        )
        .await;
        let local = repo.to_thread_local();
        let Some(tip) = support::ref_target(&local, "refs/eml/storage/no-index/genesis/staging")
        else {
            // A truly untouched staging ref never got a tree at all -- the
            // invariant holds vacuously.
            drop(log);
            return;
        };
        assert_no_roots_entry(&local, tip, "genesis, one algorithm registered, n == 0");
    });
}

/// Life point 2: after an append with an active algorithm (`n > 0`).
#[test]
fn no_roots_entry_after_appends() {
    smol::block_on(async {
        let dir = tempfile::tempdir().unwrap();
        let repo = bare_repo(dir.path(), gix::hash::Kind::Sha256);
        let mut log = new_log(
            &repo,
            "refs/eml/storage/no-index/appends/staging",
            2,
            FixtureHasher::new(32),
        )
        .await;
        for i in 0..5u32 {
            log.append_leaf(format!("leaf-{i}").as_bytes())
                .await
                .unwrap();
        }
        let local = repo.to_thread_local();
        let tip = support::ref_target(&local, "refs/eml/storage/no-index/appends/staging")
            .expect("tip must exist after appends");
        assert_no_roots_entry(&local, tip, "after 5 appends, one active algorithm, n == 5");
    });
}

/// Life point 3: after a second algorithm is registered and made to
/// checkpoint a root via a further append.
#[test]
fn no_roots_entry_after_algorithm_registered() {
    smol::block_on(async {
        let dir = tempfile::tempdir().unwrap();
        let repo = bare_repo(dir.path(), gix::hash::Kind::Sha256);
        let mut log = new_log(
            &repo,
            "refs/eml/storage/no-index/registered/staging",
            2,
            FixtureHasher::new(32),
        )
        .await;
        log.append_leaf(b"one").await.unwrap();
        log.add_algorithm(7, Box::new(FixtureHasher::new(20)))
            .await
            .unwrap();
        log.append_leaf(b"two").await.unwrap();
        let local = repo.to_thread_local();
        let tip = support::ref_target(&local, "refs/eml/storage/no-index/registered/staging")
            .expect("tip must exist");
        assert_no_roots_entry(
            &local,
            tip,
            "after registering algorithm 7 and one more append",
        );
    });
}

/// Life point 4: after an algorithm is frozen (`RemoveAlgorithm`) while
/// another stays active.
#[test]
fn no_roots_entry_after_algorithm_frozen() {
    smol::block_on(async {
        let dir = tempfile::tempdir().unwrap();
        let repo = bare_repo(dir.path(), gix::hash::Kind::Sha256);
        let mut log = new_log(
            &repo,
            "refs/eml/storage/no-index/frozen/staging",
            2,
            FixtureHasher::new(32),
        )
        .await;
        log.add_algorithm(1, Box::new(FixtureHasher::new(20)))
            .await
            .unwrap();
        for i in 0..4u32 {
            log.append_leaf(format!("leaf-{i}").as_bytes())
                .await
                .unwrap();
        }
        log.remove_algorithm(1).await.unwrap();
        let local = repo.to_thread_local();
        let tip = support::ref_target(&local, "refs/eml/storage/no-index/frozen/staging")
            .expect("tip must exist");
        assert_no_roots_entry(
            &local,
            tip,
            "after freezing algorithm 1 while algorithm 0 stays active",
        );
    });
}

/// Life point 5: after a resume (`ResumeAlgorithm`) reactivates a
/// previously frozen algorithm.
#[test]
fn no_roots_entry_after_resume() {
    smol::block_on(async {
        let dir = tempfile::tempdir().unwrap();
        let repo = bare_repo(dir.path(), gix::hash::Kind::Sha256);
        let mut log = new_log(
            &repo,
            "refs/eml/storage/no-index/resume/staging",
            2,
            FixtureHasher::new(32),
        )
        .await;
        log.add_algorithm(1, Box::new(FixtureHasher::new(20)))
            .await
            .unwrap();
        for i in 0..4u32 {
            log.append_leaf(format!("leaf-{i}").as_bytes())
                .await
                .unwrap();
        }
        log.remove_algorithm(1).await.unwrap();
        log.append_leaf(b"gap").await.unwrap();
        log.resume_algorithm(1).await.unwrap();
        let local = repo.to_thread_local();
        let tip = support::ref_target(&local, "refs/eml/storage/no-index/resume/staging")
            .expect("tip must exist");
        assert_no_roots_entry(
            &local,
            tip,
            "after resuming algorithm 1 across a one-leaf gap",
        );
    });
}

/// Life point 6: after a plain reopen from disk (`GitStorage::open`)
/// against a ref a prior instance already wrote with an active algorithm
/// and `n > 0` -- the reopen itself performs no write, so this checks that
/// nothing about opening resurrects or depends on a `roots` entry that
/// should never have existed.
#[test]
fn no_roots_entry_after_reopen() {
    smol::block_on(async {
        let dir = tempfile::tempdir().unwrap();
        let repo = bare_repo(dir.path(), gix::hash::Kind::Sha256);
        let staging = "refs/eml/storage/no-index/reopen/staging";
        {
            let mut log = new_log(&repo, staging, 2, FixtureHasher::new(32)).await;
            for i in 0..3u32 {
                log.append_leaf(format!("leaf-{i}").as_bytes())
                    .await
                    .unwrap();
            }
        }
        // Force a real reopen from disk, independent of the dropped
        // instance's in-memory state.
        let reopened = GitStorage::open(dir.path(), staging, 2).expect("reopen");
        // A reopened `GitStorage` has no method that returns an object id
        // for anything but its own tip (`tip_tree`); read the tip straight
        // off the ref, matching every other check in this file.
        drop(reopened);
        let local = repo.to_thread_local();
        let tip = support::ref_target(&local, staging).expect("tip must exist after reopen");
        assert_no_roots_entry(&local, tip, "after a plain reopen from disk");
    });
}

/// The same claim, one level down: a `WriteOp::AppendLeaf` carrying a
/// non-empty `checkpoint_roots` slice is still accepted (this dispatch
/// does not change the trait signature), but the committed tree must not
/// reflect it under the new invariant -- pins the case where the caller
/// hands the layer exactly the input the retired behavior used to persist.
#[test]
fn no_roots_entry_even_when_a_write_op_supplies_one() {
    smol::block_on(async {
        let dir = tempfile::tempdir().unwrap();
        let repo = bare_repo(dir.path(), gix::hash::Kind::Sha256);
        let staging = "refs/eml/storage/no-index/direct-apply/staging";
        let mut storage = GitStorage::new(repo.clone(), staging, 2).expect("open GitStorage");
        storage
            .apply(&[WriteOp::AddAlgorithm {
                alg_id: 0,
                epochs: &[(0, u64::MAX)],
            }])
            .await
            .unwrap();
        let root_bytes = vec![0xABu8; 32];
        storage
            .apply(&[WriteOp::AppendLeaf {
                at: 0,
                data: b"x",
                nodes: &[],
                checkpoint_roots: &[polydigest::AlgorithmRoot {
                    alg_id: 0,
                    root: &root_bytes,
                }],
            }])
            .await
            .unwrap();
        let local = repo.to_thread_local();
        let tip = support::ref_target(&local, staging).expect("tip must exist");
        assert_no_roots_entry(
            &local,
            tip,
            "direct `apply` call whose `AppendLeaf` op supplies a non-empty checkpoint_roots",
        );
    });
}
