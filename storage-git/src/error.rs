//! Error type for [`crate::GitStorage`] operations.

/// Error type for [`crate::GitStorage`] operations.
#[derive(Debug, thiserror::Error)]
pub enum GitStorageError {
    /// An error occurred inside `gix` (repository open/init, object read or
    /// write, reference resolution). The underlying `gix` error type is
    /// erased to a string because `gix` reports failures through many
    /// distinct per-operation error enums; storage-fjall's own error type
    /// takes the same approach for its embedded database errors.
    #[error("git error: {0}")]
    Git(String),

    /// A stored object's bytes do not decode as this layer's layout expects
    /// (§2-3 of the spec): wrong blob length, an unexpected tree shape, a
    /// name outside the fixed alphabet, or similar. Distinct from
    /// [`Self::TipMoved`] and from "not found" (`get_node`/`get_leaf`
    /// signal absence through `Option`/a dedicated not-found path, not this
    /// variant).
    #[error("corrupted git storage layout: {0}")]
    Corruption(String),

    /// The requested leaf or node coordinate has no data in the current
    /// staged tree.
    #[error("not found: {0}")]
    NotFound(String),

    /// SG19/SG4.5 — the staging ref's compare-and-swap precondition failed:
    /// another writer moved the ref between this instance's last observed
    /// value and this write attempt. Distinguished from every other error
    /// shape so the caller (the `polydigest` combinator) knows to reload and
    /// retry rather than treat the write as a corruption or I/O failure.
    #[error("staging ref tip moved: expected {expected:?}, found {actual:?}")]
    TipMoved {
        /// The tree id this instance last observed at the staging ref (or
        /// `None` for a fresh instance that had never observed the ref).
        expected: Option<String>,
        /// The tree id actually found at the staging ref when the
        /// compare-and-swap was attempted (or `None` if the ref no longer
        /// exists at all).
        actual: Option<String>,
    },

    /// The supplied staging ref name is not a valid git reference name.
    #[error("invalid staging ref name: {0}")]
    InvalidRef(String),

    /// The instance's configured arity is out of `spine::ARITY_RANGE`, or
    /// disagrees with a previously-committed `meta.arity` on reopen.
    #[error("invalid arity: {0}")]
    InvalidArity(String),

    /// The staging ref's compare-and-swap failed for a reason that never
    /// reached the point of comparing a value at all -- a lock a concurrent
    /// `git gc`/`pack-refs` briefly held, an I/O error, or a packed-refs
    /// preparation failure (`gix::reference::edit::Error`'s non-mismatch
    /// variants). Distinct from [`Self::TipMoved`] (a genuine compare
    /// mismatch) and from [`Self::Corruption`] (a malformed stored layout):
    /// a caller MAY retry this one without first reloading, since nothing
    /// about the ref's value was ever observed to have changed. `cas()`
    /// already retries internally for up to its own bound before returning
    /// this variant, so seeing it means that bound was exhausted and the
    /// condition had not cleared.
    #[error("ref update transient failure (gave up retrying): {0}")]
    RefUpdateTransient(String),

    /// A [`polydigest::WriteOp`] handed to [`crate::GitStorage`]'s
    /// [`Storage::apply`](polydigest::Storage::apply) violated its own
    /// precondition: an append at a position other than the current
    /// count, a duplicate algorithm registration, or a
    /// removal/resume naming an algorithm this store has never registered.
    #[error("invalid apply operation: {0}")]
    InvalidOperation(String),
}

impl GitStorageError {
    /// Whether this error is the distinguished tip-moved variant (SG4.5).
    #[must_use]
    pub fn is_tip_moved(&self) -> bool {
        matches!(self, Self::TipMoved { .. })
    }

    /// Whether this error is the distinguished transient/retriable variant
    /// (SG19a): a compare-and-swap failure that never reached a genuine
    /// value comparison.
    #[must_use]
    pub fn is_transient(&self) -> bool {
        matches!(self, Self::RefUpdateTransient(_))
    }
}
