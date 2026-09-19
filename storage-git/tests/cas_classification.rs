//! CAS CLASSIFICATION: `storage-git`'s compare-and-swap step must
//! distinguish a genuine ref-value mismatch from every other failure shape
//! (SG19/SG19a, `docs/specs/storage-git.md`).
//!
//! `storage_git::GitStorage::cas` (`src/lib.rs`) classifies an
//! `edit_reference` failure via `is_genuine_cas_mismatch`, which matches
//! only `gix::reference::edit::Error`'s three genuine compare-mismatch
//! variants (`ReferenceOutOfDate`/`MustNotExist`/`MustExist` -- reached only
//! by actually comparing the ref's value against the precondition) and
//! returns `GitStorageError::TipMoved` for those; every other failure shape
//! (`Io`, `LockAcquire`, `PackedTransactionAcquire`, a packed-refs
//! preparation failure, ...) never reaches a comparison at all, and is
//! returned as the distinct `GitStorageError::RefUpdateTransient` this file
//! pins below, not `TipMoved`. Collapsing both into one `TipMoved` outcome
//! (an earlier shape of this function, before the classification fix)
//! erased the distinction the variant's own doc comment (`src/error.rs`)
//! says it exists to preserve ("the caller ... knows to reload and retry
//! rather than treat the write as a corruption or I/O failure"), and
//! produced a "textually identical expected and actual" signature under
//! disk-pressure testing during this layout's design exploration: a no-op
//! failure re-reading the same untouched value twice.
//!
//! **What this file pins**: a non-mismatch failure must come back as a
//! *specifically named* transient/retriable variant, not merely "anything
//! other than `TipMoved`" -- collapsing it into the existing
//! `GitStorageError::Git(String)` catch-all would make it indistinguishable
//! from an unrelated, non-retriable I/O failure (a deleted repository, a
//! permissions error), which a caller must NOT retry. It asserts the
//! returned error matches none of the six variants that existed before this
//! fix (`TipMoved`/`Corruption`/`Git`/`NotFound`/`InvalidRef`/
//! `InvalidArity`), by exhaustive elimination -- a check that compiles
//! independently of the fix's own new variant's exact name, rather than
//! calling a method that might not exist yet and would abort `cargo test`'s
//! build for the whole package before any test in it could run (verified
//! directly: a single
//! non-compiling integration-test file blocks every test in the crate, not
//! just its own).
//!
//! RED at 60f93fe: a lock-contention failure that never compared a value at
//! all still comes back as `GitStorageError::TipMoved`, which the
//! elimination above matches on its first arm.

mod common;

use std::fs;

use common::init_repo;
use gix::hash::Kind as HashKind;
use storage_git::GitStorage;

/// [CAS CLASSIFICATION] Forces a `LockAcquire`-shaped failure directly:
/// pre-creates the exact lock file `gix`'s file-backed transaction would
/// take for this staging ref (`<gitdir>/<staging_ref>.lock`) before calling
/// `store_leaf`, so the transaction can never acquire it and therefore
/// never reaches the point of comparing `self.observed_tip` against
/// anything. A mutation reverting `cas()` to an unconditional
/// `Err(_) => TipMoved` (collapsing every failure shape into one outcome,
/// rather than matching `gix::reference::edit::Error` for the three genuine
/// mismatch variants via `is_genuine_cas_mismatch`) is exactly what turns
/// this red.
#[test]
fn lock_contention_before_any_compare_is_not_reported_as_tip_moved() {
    smol::block_on(async {
        let (dir, repo) = init_repo(HashKind::Sha1);
        let staging = "refs/eml/storage/lockrace/staging";
        let mut storage = GitStorage::new(repo, staging, 2).unwrap();

        let lock_path = dir.path().join(format!("{staging}.lock"));
        fs::create_dir_all(lock_path.parent().unwrap()).unwrap();
        fs::write(&lock_path, b"held by this test\n").unwrap();

        let result = common::append_leaf(&mut storage, 0, b"leaf0").await;
        let err = result.expect_err("a held lock must fail the write");

        assert!(
            !err.is_tip_moved(),
            "a lock-contention failure that never reached a value comparison must never be \
             reported as the compare-mismatch variant (TipMoved); got: {err}"
        );
        assert!(
            !matches!(err, storage_git::GitStorageError::Corruption(_)),
            "a lock-contention failure that never reached a value comparison, and never touched a \
             stored layout, must never be reported as Corruption either; got: {err}"
        );
        // Exhaustive elimination against every variant that exists at 60f93fe: the
        // only way to make this pass is for the implementer to add a NEW, specifically
        // named transient/retriable variant (e.g. GitStorageError::RefUpdateTransient) --
        // reusing the existing `Git(String)` catch-all is not enough, since a caller could
        // never tell a retriable lock race apart from an unrelated, non-retriable I/O
        // failure (a deleted repository, a permissions error) through that one variant.
        assert!(
            !matches!(
                err,
                storage_git::GitStorageError::TipMoved { .. }
                    | storage_git::GitStorageError::Corruption(_)
                    | storage_git::GitStorageError::Git(_)
                    | storage_git::GitStorageError::NotFound(_)
                    | storage_git::GitStorageError::InvalidRef(_)
                    | storage_git::GitStorageError::InvalidArity(_)
            ),
            "a lock-contention failure that never reached a value comparison must be reported as \
             a new, specifically named transient/retriable variant, distinct from every variant \
             that exists at 60f93fe -- none of \
             TipMoved/Corruption/Git/NotFound/InvalidRef/InvalidArity qualify; got: {err}"
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
        let result = common::append_leaf(&mut storage, 0, b"leaf0").await;
        let err = result.expect_err("a held lock must fail the genesis write");

        assert!(
            !err.is_tip_moved(),
            "a genesis-write lock-contention failure must never be reported as TipMoved; got: \
             {err}"
        );
        assert!(
            !matches!(err, storage_git::GitStorageError::Corruption(_)),
            "a genesis-write lock-contention failure must never be reported as Corruption either; \
             got: {err}"
        );
        // Same exhaustive elimination as the populated-ref case above -- genesis must not
        // be a special case a caller has to handle differently.
        assert!(
            !matches!(
                err,
                storage_git::GitStorageError::TipMoved { .. }
                    | storage_git::GitStorageError::Corruption(_)
                    | storage_git::GitStorageError::Git(_)
                    | storage_git::GitStorageError::NotFound(_)
                    | storage_git::GitStorageError::InvalidRef(_)
                    | storage_git::GitStorageError::InvalidArity(_)
            ),
            "a genesis-write lock-contention failure must be reported as the same new, \
             specifically named transient/retriable variant as the populated-ref case, distinct \
             from every variant that exists at 60f93fe; got: {err}"
        );

        fs::remove_file(&lock_path).ok();
    });
}
