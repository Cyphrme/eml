//! Minimal structural error type.
//!
//! The spine's verification surface (inclusion) reports failure with `bool` /
//! `Option`, so it needs no error type there. Errors arise only where the spine
//! *constructs* a checked value — sealing a frontier — and the input can be
//! structurally ill-formed. This enum stays deliberately small: the
//! algorithm-lifecycle errors (a malformed committed epoch timeline) belong to
//! the `polydigest` combinator above the spine, not here.

use std::fmt;

/// A spine construction error.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
    /// The spine arity is outside the valid range `2..=256`.
    BadArity,
    /// A frontier was sealed with a peak count that does not match the canonical
    /// frontier geometry for `(tree_size, arity)` — a truncated or oversized
    /// peaks slice.
    MalformedFrontier,
    /// A member-root fold was requested but no hasher was supplied for an
    /// algorithm that has a frontier in the seal. Folding over a truncated
    /// member-root list would yield a root that no algorithm published, so a
    /// missing hasher is an error, not a silent skip. Carries the offending
    /// algorithm ID.
    MissingHasher {
        /// The algorithm whose hasher was absent from the supplied set.
        alg_id: u64,
    },
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::BadArity => write!(f, "spine arity is outside the valid range 2..=256"),
            Self::MalformedFrontier => {
                write!(
                    f,
                    "frontier peak count does not match the canonical geometry for the sealed \
                     (tree_size, arity)"
                )
            },
            Self::MissingHasher { alg_id } => {
                write!(
                    f,
                    "no hasher supplied for algorithm {alg_id}, which has a frontier in the seal; \
                     a member-root fold cannot be computed with a missing hasher"
                )
            },
        }
    }
}

impl std::error::Error for Error {}

/// A specialized `Result` alias for the spine.
pub type Result<T> = std::result::Result<T, Error>;
