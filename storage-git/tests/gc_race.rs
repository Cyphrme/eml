//! GC RACE: a single writer's append must survive git's own housekeeping
//! racing it, and a ref update that can never succeed must fail
//! observably, within a stated bound, rather than retry forever.
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
//! "second" thread): must the append still fail, and if it does, how
//! quickly?
//!
//! **Decision: for a definitely-non-mismatch failure, the append must not
//! fail at all if the transient condition clears within a stated bound --
//! `GitStorage`'s write path must retry the ref-update step internally (not
//! rebuild the tree; the content to write never changes) until the
//! transient condition clears, bounded. If the condition never clears, the
//! retry must GIVE UP within that same stated bound and return a
//! specifically named transient/retriable error (never `TipMoved`, never
//! `Corruption`), not hang.** A genuine
//! compare-mismatch is never retried internally by `GitStorage` itself:
//! deciding what to write in light of someone else's real change is
//! `polydigest`'s job (nothing above `storage-git`
//! currently reads `is_tip_moved()` to retry, either), and a single
//! `GitStorage` instance has no way to safely re-derive a merged write on
//! its own without risking silently discarding a real concurrent writer's
//! content.
//!
//! **The stated bound this file requires the implementation to honor:
//! [`REQUIRED_RETRY_BOUND`] (2 seconds).** A retry loop may use any backoff
//! shape internally, but must give up and return within that bound once the
//! ref-update failure is not a genuine compare-mismatch. This file enforces
//! its own, more generous [`TEST_CEILING`] (5 seconds) from OUTSIDE the call
//! under test (a background thread plus a channel with `recv_timeout`), so
//! an unbounded or too-loosely-bounded retry loop makes this test FAIL
//! observably instead of hanging the test process forever -- the one
//! failure mode a plain `assert!` inside the same call stack could never
//! catch, since it never gets control back.
//!
//! Evidence for drawing the "give up, don't retry forever" line: a
//! companion prototype's own `gc_race.rs`, run with classification already
//! fixed, still measured 8 of 4,000 appends failing with a *genuine*
//! `ReferenceOutOfDate` (two distinct hashes) under concurrent
//! `git gc --auto`/`pack-refs` against a single sequential writer -- so
//! correct classification alone does not make every append succeed; only
//! the non-mismatch shapes are safe to paper over automatically, since by
//! construction they never observed a conflicting value to discard, and
//! even those must eventually give up rather than retry forever if the
//! condition genuinely never clears (a housekeeping process that crashed
//! mid-lock, for instance).
//!
//! `retry_gives_up_within_the_stated_bound_when_the_lock_never_clears`
//! demonstrates the "give up" half of the contract with certainty (the lock
//! is never released during the test, so there is no race to win).
//! `deterministic_transient_lock_does_not_fail_an_append` demonstrates the
//! "retry succeeds" half, also with certainty: the lock is released only
//! after the append attempt has signaled that it has actually started
//! running on its own thread, never after a fixed delay from `thread::spawn`
//! returning. That distinction is not cosmetic: an earlier version of this
//! test released the lock from a delay timed off `thread::spawn` alone, and
//! it passed 6 of 6 runs in isolation but failed under `cargo test`'s
//! default parallelism, because thread-spawn scheduling jitter under load
//! could by itself exceed the delay -- a flaky test hiding behind a name
//! that claimed to be deterministic. Starting the delay only once the
//! spawned thread has confirmed it is actually running removes that
//! confound entirely, at the cost of one extra channel.
//! `small_scale_concurrent_gc_against_a_sequential_writer` is the
//! probabilistic, small-N evidence run this file also keeps: a REAL race,
//! not a forced one, kept as evidence rather than a strict zero-failures
//! gate, since the citation above shows a correct implementation can still
//! see a rare genuine mismatch here.
//!
//! RED at 60f93fe: `GitStorage::write_batch`/`cas` retries nothing today --
//! the ref edit is attempted exactly once and whatever `cas()` reports (see
//! `cas_classification.rs` for how it currently mislabels that report) is
//! returned straight to the caller.

mod common;

use std::process::Command;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, mpsc};
use std::thread;
use std::time::Duration;

use common::init_repo;
use gix::hash::Kind as HashKind;
use storage_git::GitStorage;

/// The bound the implementation must honor: a ref-update retry loop must
/// give up (and return the distinguished transient error) within this much
/// wall-clock time of a definitely-non-mismatch failure that never clears.
/// Stated here, once, as the single source of truth both tests below check
/// against.
const REQUIRED_RETRY_BOUND: Duration = Duration::from_secs(2);

/// This file's own, more generous external ceiling -- comfortably above
/// [`REQUIRED_RETRY_BOUND`] to absorb ordinary scheduling slack on a loaded
/// machine, but far below "hangs forever" -- enforced by a background
/// thread plus `recv_timeout`, never by letting the call under test run
/// unbounded on the test's own thread.
const TEST_CEILING: Duration = Duration::from_secs(5);

/// A delay comfortably inside [`REQUIRED_RETRY_BOUND`], used to release a
/// held lock while a correct, bounded retry loop must still be retrying.
const RELEASE_WELL_WITHIN_BOUND: Duration = Duration::from_millis(200);

/// Every variant [`storage_git::GitStorageError`] has at 60f93fe -- used
/// below by exhaustive elimination (see `cas_classification.rs` for why:
/// asserting "not TipMoved, not Corruption" alone leaves the door open to
/// reusing the undifferentiated `Git(String)` catch-all, which a caller
/// could never tell apart from a non-retriable I/O failure).
fn is_one_of_the_pre_existing_variants(err: &storage_git::GitStorageError) -> bool {
    matches!(
        err,
        storage_git::GitStorageError::TipMoved { .. }
            | storage_git::GitStorageError::Corruption(_)
            | storage_git::GitStorageError::Git(_)
            | storage_git::GitStorageError::NotFound(_)
            | storage_git::GitStorageError::InvalidRef(_)
            | storage_git::GitStorageError::InvalidArity(_)
    )
}

/// [GC RACE, the "give up" half] The ref lock is held for the entire test
/// (never released -- there is no race to win here, so this is deterministic
/// regardless of scheduling), forcing a definitely-non-mismatch failure that
/// never clears. Under the decided contract, the append must still RETURN
/// within [`TEST_CEILING`], with a new, specifically named transient error
/// (never `TipMoved`, never `Corruption`, never the undifferentiated
/// `Git(String)` catch-all) -- never hang past [`REQUIRED_RETRY_BOUND`].
///
/// The append itself runs on a background thread; this test's own thread
/// enforces the ceiling from OUTSIDE that call via `recv_timeout`, so an
/// unbounded (or too-loosely-bounded) retry loop fails this test
/// observably -- with a clear message naming the missing bound -- instead
/// of hanging the whole test binary. RED at 60f93fe for a different reason
/// than a future unbounded implementation would be: today's single,
/// unretried attempt returns almost immediately, well within
/// [`TEST_CEILING`], but as `TipMoved`, which the exhaustive elimination
/// below still catches.
#[test]
fn retry_gives_up_within_the_stated_bound_when_the_lock_never_clears() {
    smol::block_on(async {
        let (dir, repo) = init_repo(HashKind::Sha1);
        let staging = "refs/eml/storage/gc-race-bound/staging";
        let mut storage = GitStorage::new(repo, staging, 2).unwrap();

        let lock_path = dir.path().join(format!("{staging}.lock"));
        std::fs::create_dir_all(lock_path.parent().unwrap()).unwrap();
        std::fs::write(&lock_path, b"held for the whole test -- never released\n").unwrap();

        let (result_tx, result_rx) = mpsc::channel();
        thread::spawn(move || {
            let result = smol::block_on(common::append_leaf(&mut storage, 0, b"leaf0"));
            // A `send` failure here just means the receiver already gave up
            // after the ceiling elapsed and this thread is now leaking past
            // the end of a failed test -- not a bug in this thread itself.
            let _ = result_tx.send(result);
        });

        let result = match result_rx.recv_timeout(TEST_CEILING) {
            Ok(result) => result,
            Err(mpsc::RecvTimeoutError::Timeout) => {
                std::fs::remove_file(&lock_path).ok();
                panic!(
                    "append did not return within this test's {TEST_CEILING:?} ceiling -- a retry \
                     loop with no bound (or one looser than the required \
                     {REQUIRED_RETRY_BOUND:?}) hangs instead of failing observably once a \
                     ref-update failure is not a genuine compare-mismatch and never clears"
                );
            },
            Err(mpsc::RecvTimeoutError::Disconnected) => {
                std::fs::remove_file(&lock_path).ok();
                panic!("append thread dropped its result sender without sending a result");
            },
        };

        std::fs::remove_file(&lock_path).ok();

        let err = result.expect_err(
            "an append against a ref lock that never clears must eventually fail, not succeed",
        );
        assert!(
            !is_one_of_the_pre_existing_variants(&err),
            "a definitely-non-mismatch failure that never clears must give up within \
             {REQUIRED_RETRY_BOUND:?} and report a new, specifically named transient/retriable \
             variant, distinct from every variant that exists at 60f93fe -- none of \
             TipMoved/Corruption/Git/NotFound/InvalidRef/InvalidArity qualify; got: {err}"
        );
    });
}

/// [GC RACE, the "retry succeeds" half, deterministic] A background thread
/// holds the exact lock file `gix`'s file-backed transaction would take for
/// this staging ref, releasing it only [`RELEASE_WELL_WITHIN_BOUND`] after
/// the append attempt has signaled it has actually started running -- a
/// bounded, known-transient, definitely-non-mismatch condition (nothing else
/// ever touches the ref's value in this test, so there is no second writer
/// for a "genuine mismatch" to even be), released comfortably before
/// [`REQUIRED_RETRY_BOUND`] elapses. Under the decided contract, the append
/// must still return `Ok`. RED at 60f93fe: `write_batch` attempts the ref
/// edit exactly once and returns whatever `cas()` reports, so this call
/// fails the moment it races the held lock -- deterministically, since the
/// lock is confirmed held before the append thread is even started.
#[test]
fn deterministic_transient_lock_does_not_fail_an_append() {
    smol::block_on(async {
        let (dir, repo) = init_repo(HashKind::Sha1);
        let staging = "refs/eml/storage/gc-race-lock/staging";
        let mut storage = GitStorage::new(repo, staging, 2).unwrap();

        let lock_path = dir.path().join(format!("{staging}.lock"));
        std::fs::create_dir_all(lock_path.parent().unwrap()).unwrap();
        std::fs::write(&lock_path, b"held by a concurrent housekeeping op\n").unwrap();

        // The append thread signals that it has started running BEFORE doing
        // anything else, so the release delay below is timed from "the
        // attempt is genuinely underway," never from "the OS got around to
        // scheduling the thread" -- see this file's module doc for why that
        // distinction is load-bearing, not cosmetic.
        let (started_tx, started_rx) = mpsc::channel::<()>();
        let (result_tx, result_rx) = mpsc::channel();
        thread::spawn(move || {
            let _ = started_tx.send(());
            let result = smol::block_on(common::append_leaf(&mut storage, 0, b"leaf0"));
            let _ = result_tx.send(result);
        });

        started_rx
            .recv_timeout(TEST_CEILING)
            .expect("append thread must signal that it has started within the test ceiling");
        thread::sleep(RELEASE_WELL_WITHIN_BOUND);
        std::fs::remove_file(&lock_path).ok();

        let result = result_rx.recv_timeout(TEST_CEILING).unwrap_or_else(|_| {
            panic!(
                "append did not return within this test's {TEST_CEILING:?} ceiling after the lock \
                 was released well within the required {REQUIRED_RETRY_BOUND:?} bound"
            )
        });

        assert!(
            result.is_ok(),
            "a single writer's append raced only by a transient, definitely-non-mismatch lock \
             hold, released after {RELEASE_WELL_WITHIN_BOUND:?} -- well inside the required \
             {REQUIRED_RETRY_BOUND:?} retry bound -- must not fail: {result:?}"
        );
    });
}

/// [GC RACE, probabilistic, small-N evidence] A single sequential writer
/// appends `N` leaves while a second thread repeatedly runs
/// `git gc --auto` and `git pack-refs --all` against the same repository --
/// scaled down from a larger companion measurement to keep this
/// disk-constrained sandbox's object count small. Each index is retried
/// (bounded) on failure rather than abandoned, so one failure does not
/// cascade into a string of unrelated "out-of-order index" errors from this
/// test's own loop -- the assertion below is about failure SHAPE, not about
/// completing without ever seeing one.
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
                match common::append_leaf(&mut storage, i, &data).await {
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
