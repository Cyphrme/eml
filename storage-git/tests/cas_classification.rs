//! Merge-gate dispatch item 4 (CAS CLASSIFICATION):
//! `.ledger/deposits/git-backend/lead-maintainer/storage-git-tip-tree-gate.md`
//! and `spike-report.md` §8.
//!
//! `storage_git::GitStorage::cas` (`src/lib.rs`) is:
//! ```ignore
//! match repo.edit_reference(edit) {
//!     Ok(_) => Ok(()),
//!     Err(_) => { /* always builds a TipMoved, regardless of e */ }
//! }
//! ```
//! `gix::reference::edit::Error` distinguishes a genuine compare-mismatch
//! (`ReferenceOutOfDate`/`MustNotExist`/`MustExist` -- the only variants
//! reached by actually comparing the ref's value against the precondition)
//! from every other failure shape (`Io`, `LockAcquire`,
//! `PackedTransactionAcquire`, a packed-refs preparation failure, ...),
//! none of which ever reach a comparison at all. Collapsing both into
//! `GitStorageError::TipMoved` erases the distinction the variant's own doc
//! comment (`src/error.rs`) says it exists to preserve ("the caller ...
//! knows to reload and retry rather than treat the write as a corruption or
//! I/O failure"), and produces the "textually identical expected and
//! actual" signature spike-report.md §1's original n=100,000 crash showed:
//! a no-op failure re-reads the same untouched value twice.
//!
//! Ported from `storage-git-keyed`'s own `tests/cas_classification.rs`
//! (`.worktrees/spike-key-layout/storage-git-keyed/`), which demonstrates
//! the fix `storage-git` has not received: `is_genuine_cas_mismatch`
//! (`storage-git-keyed/src/lib.rs`) matches only the three real
//! compare-mismatch variants and reports everything else as
//! `KeyedGitStorageError::Git(..)`, never `TipMoved`.
//!
//! RED at 60f93fe: a lock-contention failure that never compared a value at
//! all still comes back as `GitStorageError::TipMoved`.

mod common;

use std::fs;

use common::init_repo;
use gix::hash::Kind as HashKind;
use polydigest::Storage;
use storage_git::GitStorage;

/// [CAS CLASSIFICATION] Forces a `LockAcquire`-shaped failure directly:
/// pre-creates the exact lock file `gix`'s file-backed transaction would
/// take for this staging ref (`<gitdir>/<staging_ref>.lock`) before calling
/// `store_leaf`, so the transaction can never acquire it and therefore
/// never reaches the point of comparing `self.observed_tip` against
/// anything. A mutation reverting `cas()` to its current, unconditional
/// `Err(_) => TipMoved` is exactly what keeps this red; the fix is a `match`
/// on the underlying `gix::reference::edit::Error` naming
/// `ReferenceOutOfDate`/`MustNotExist`/`MustExist` as the only genuine-
/// mismatch variants (`storage-git-keyed::is_genuine_cas_mismatch`).
#[test]
fn lock_contention_before_any_compare_is_not_reported_as_tip_moved() {
    smol::block_on(async {
        let (dir, repo) = init_repo(HashKind::Sha1);
        let staging = "refs/eml/storage/lockrace/staging";
        let mut storage = GitStorage::new(repo, staging, 2).unwrap();

        let lock_path = dir.path().join(format!("{staging}.lock"));
        fs::create_dir_all(lock_path.parent().unwrap()).unwrap();
        fs::write(&lock_path, b"held by this test\n").unwrap();

        let result = storage.store_leaf(0, b"leaf0").await;
        let err = result.expect_err("a held lock must fail the write");

        assert!(
            !err.is_tip_moved(),
            "a lock-contention failure that never reached a value comparison must never be \
             reported as the compare-mismatch variant (TipMoved); got: {err}"
        );

        fs::remove_file(&lock_path).ok();
    });
}

/// [CAS CLASSIFICATION] The other branch, at genesis: `MustNotExist`'s own
/// precondition path must go through the identical classification. A
/// pre-existing lock file starves the transaction before genesis's
/// `MustNotExist` check runs, so this must fail the same non-mismatch way
/// as the populated-ref case above, never as `TipMoved` (there is nothing
/// for a fresh instance's "expected" to even mean yet at true genesis).
#[test]
fn lock_contention_at_genesis_is_not_reported_as_tip_moved() {
    smol::block_on(async {
        let (dir, repo) = init_repo(HashKind::Sha1);
        let staging = "refs/eml/storage/lockrace-genesis/staging";

        let lock_path = dir.path().join(format!("{staging}.lock"));
        fs::create_dir_all(lock_path.parent().unwrap()).unwrap();
        fs::write(&lock_path, b"held by this test\n").unwrap();

        let mut storage = GitStorage::new(repo, staging, 2).unwrap();
        let result = storage.store_leaf(0, b"leaf0").await;
        let err = result.expect_err("a held lock must fail the genesis write");

        assert!(
            !err.is_tip_moved(),
            "a genesis-write lock-contention failure must never be reported as TipMoved; got: \
             {err}"
        );

        fs::remove_file(&lock_path).ok();
    });
}
