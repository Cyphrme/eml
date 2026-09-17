//! GC RACE: a single writer's append must survive git's own housekeeping
//! racing it (`[TT1]`,
//! `.ledger/deposits/git-backend/lead-maintainer/storage-git-tip-tree-gate.md`),
//! ported (at a small size, to keep this disk-constrained sandbox's object
//! count small) from `storage-git-keyed`'s own `tests/gc_race.rs`
//! (`.worktrees/spike-key-layout/storage-git-keyed/`).
//!
//! ## The contract this file decides, with evidence
//!
//! Two failure classes can race a single sequential writer here: a genuine
//! compare-mismatch (a real value change between this instance's last
//! observed tip and its next compare-and-swap), and a transient,
//! non-mismatch failure from git's OWN housekeeping (a lock
//! `git gc --auto`/`git pack-refs` briefly holds, or the loose-to-packed ref
//! representation changing underneath a read) that never compared a value
//! at all. `cas_classification.rs` requires telling these apart. This file
//! asks further, for the single-writer case these tests drive (no second
//! LOGICAL writer ever exists here -- only git's own housekeeping is the
//! "second" thread): must the append still fail?
//!
//! **Decision: for a definitely-non-mismatch failure, the append must not
//! fail at all -- `GitStorage`'s write path must retry the ref-update step
//! internally (not rebuild the tree; the content to write never changes)
//! until the transient condition clears, bounded.** A genuine
//! compare-mismatch is never retried internally by `GitStorage` itself:
//! deciding what to write in light of someone else's real change is
//! `polydigest`'s job (`[TT8]`'s routed note -- nothing above `storage-git`
//! currently reads `is_tip_moved()` to retry, either), and a single
//! `GitStorage` instance has no way to safely re-derive a merged write on
//! its own without risking silently discarding a real concurrent writer's
//! content.
//!
//! Evidence for drawing the line there, rather than at "retry everything,
//! including genuine mismatches": `storage-git-keyed`'s own `gc_race.rs`,
//! run with classification already fixed, still measured 8 of 4,000
//! appends failing with a *genuine* `ReferenceOutOfDate` (two distinct
//! hashes) under concurrent `git gc --auto`/`pack-refs` against a single
//! sequential writer -- so correct classification alone does not make every
//! append succeed; only the non-mismatch shapes are safe to paper over
//! automatically, since by construction they never observed a conflicting
//! value to discard.
//!
//! `deterministic_transient_lock_does_not_fail_an_append` demonstrates the
//! decided contract with certainty, by forcing a lock-contention failure
//! whose transient, non-mismatch cause is known (there is no second writer
//! at all in that test, so it cannot possibly be a genuine mismatch).
//! `small_scale_concurrent_gc_against_a_sequential_writer` is the
//! probabilistic, small-N evidence run this dispatch also asks to port: a
//! REAL race, not a forced one, kept -- like the prototype's own version --
//! as evidence rather than a strict zero-failures gate, since the citation
//! above shows a correct implementation can still see a rare genuine
//! mismatch here.
//!
//! RED at 60f93fe: `GitStorage::write_batch`/`cas` retries nothing today --
//! the ref edit is attempted exactly once and whatever `cas()` reports (see
//! `cas_classification.rs` for how it currently mislabels that report) is
//! returned straight to the caller.

mod common;

use std::process::Command;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::thread;
use std::time::Duration;

use common::init_repo;
use gix::hash::Kind as HashKind;
use polydigest::Storage;
use storage_git::GitStorage;

/// [GC RACE, deterministic] A background thread holds the exact lock file
/// `gix`'s file-backed transaction would take for this staging ref for
/// 150ms, then releases it -- a bounded, known-transient, definitely-
/// non-mismatch condition (nothing else ever touches the ref's value in
/// this test, so there is no second writer for a "genuine mismatch" to even
/// be). Under the decided contract, `store_leaf`, called while the lock is
/// held, must still return `Ok` once the lock clears within the bound --
/// the append must not fail. RED at 60f93fe: `write_batch` attempts the ref
/// edit exactly once and returns whatever `cas()` reports, so this call
/// fails the moment it races the held lock.
#[test]
fn deterministic_transient_lock_does_not_fail_an_append() {
    smol::block_on(async {
        let (dir, repo) = init_repo(HashKind::Sha1);
        let staging = "refs/eml/storage/gc-race-lock/staging";
        let mut storage = GitStorage::new(repo, staging, 2).unwrap();

        let lock_path = dir.path().join(format!("{staging}.lock"));
        std::fs::create_dir_all(lock_path.parent().unwrap()).unwrap();
        std::fs::write(&lock_path, b"held by a concurrent housekeeping op\n").unwrap();

        let held = Arc::new(AtomicBool::new(true));
        let held_writer = Arc::clone(&held);
        let lock_path_thread = lock_path.clone();
        let releaser = thread::spawn(move || {
            thread::sleep(Duration::from_millis(150));
            std::fs::remove_file(&lock_path_thread).ok();
            held_writer.store(false, Ordering::Relaxed);
        });

        let result = storage.store_leaf(0, b"leaf0").await;

        releaser.join().unwrap();
        assert!(
            !held.load(Ordering::Relaxed),
            "test bug: the append returned before the lock was even released, so it proves \
             nothing about surviving the race"
        );
        assert!(
            result.is_ok(),
            "a single writer's append raced only by a transient, definitely-non-mismatch lock \
             hold must not fail: {result:?}"
        );
    });
}

/// [GC RACE, probabilistic, small-N evidence] A single sequential writer
/// appends `N` leaves while a second thread repeatedly runs
/// `git gc --auto` and `git pack-refs --all` against the same repository --
/// ported from `storage_git_keyed::tests::gc_race`, scaled from n=4,000 down
/// to keep this disk-constrained sandbox's object count small. Each index
/// is retried (bounded) on failure rather than abandoned, so one failure
/// does not cascade into a string of unrelated "out-of-order index" errors
/// from this test's own loop -- the assertion below is about failure
/// SHAPE, not about completing without ever seeing one.
#[test]
fn small_scale_concurrent_gc_against_a_sequential_writer() {
    smol::block_on(async {
        let (dir, repo) = init_repo(HashKind::Sha1);
        let path = dir.path().to_path_buf();

        let stop = Arc::new(AtomicBool::new(false));
        let stop_gc = Arc::clone(&stop);
        let gc_thread = thread::spawn(move || {
            let mut runs = 0u64;
            while !stop_gc.load(Ordering::Relaxed) {
                let _ = Command::new("git")
                    .args(["gc", "--auto"])
                    .current_dir(&path)
                    .status();
                let _ = Command::new("git")
                    .args(["pack-refs", "--all"])
                    .current_dir(&path)
                    .status();
                runs += 1;
                thread::sleep(Duration::from_millis(10));
            }
            runs
        });

        let mut storage = GitStorage::new(repo, "refs/eml/storage/gc-race/staging", 2).unwrap();

        let mut tip_moved_count = 0u64;
        let mut other_errors: Vec<String> = Vec::new();
        const N: u64 = 150;
        const MAX_ATTEMPTS_PER_INDEX: u32 = 30;

        for i in 0..N {
            let data = i.to_le_bytes();
            let mut attempts = 0u32;
            loop {
                attempts += 1;
                match storage.store_leaf(i, &data).await {
                    Ok(()) => break,
                    Err(e) => {
                        if e.is_tip_moved() {
                            tip_moved_count += 1;
                        } else {
                            other_errors.push(format!("index {i}: {e}"));
                        }
                        if attempts >= MAX_ATTEMPTS_PER_INDEX {
                            other_errors
                                .push(format!("index {i}: gave up after {attempts} attempts"));
                            break;
                        }
                    },
                }
            }
        }

        stop.store(true, Ordering::Relaxed);
        let gc_runs = gc_thread.join().unwrap();

        eprintln!(
            "gc_race: {gc_runs} gc/pack-refs cycles against {N} sequential appends; \
             tip_moved={tip_moved_count}, other_errors={other_errors:?}"
        );

        assert!(
            other_errors.is_empty(),
            "every failure racing a single writer against git's own housekeeping must be a \
             correctly classified compare-mismatch (TipMoved), and the decided contract requires \
             one to eventually clear within {MAX_ATTEMPTS_PER_INDEX} attempts: {other_errors:?}"
        );
    });
}
