//! Checkpoint-tree assembly: turning a [`polydigest::WriteOp`] batch into a
//! new `C(n')` tree object (§2, §3).
//!
//! Deliberately unimplemented (head's ruling, 2026-09-17): the operation
//! enum, the dropped kind byte, and the readable top-level names (`nodes`/
//! `leaves`/`epochs`/`roots` in place of `n`/`l`/`e`/`r`) all land together
//! in one rewrite of this file, which has no implementation yet. The
//! previous five-parameter `write_batch` assembly this file held (per-key
//! `n/l` fan-out, `e`/`r` projection) is gone with it rather than left as
//! dead code nothing calls -- see `git log` for that version if it is
//! useful as a starting point.

use gix::ObjectId;

use crate::error::GitStorageError as Error;

/// The result of assembling and writing a new `C(n')`.
pub(crate) struct Applied {
    pub tree_id: ObjectId,
    pub count: u64,
}

/// The instance's committed state as of its last observed write. Unread by
/// [`apply`]'s stub body; a real implementation reads both fields to decide
/// what to project forward.
#[derive(Clone, Copy)]
#[allow(dead_code, reason = "read by apply() once the write path lands")]
pub(crate) struct OldState {
    pub tree: Option<ObjectId>,
    pub count: u64,
}

/// Assemble and write the new checkpoint tree for one atomic batch of
/// [`polydigest::WriteOp`]s. Does not touch the staging ref; the caller
/// performs the compare-and-swap once this returns.
pub(crate) fn apply(
    _repo: &gix::Repository,
    _arity: u64,
    _old: OldState,
    _ops: &[polydigest::WriteOp<'_>],
) -> Result<Applied, Error> {
    unimplemented!(
        "storage-git::build::apply: the operation-enum write path is not implemented yet"
    )
}
