//! CML engine error type.
//!
//! The engine reads from a borrowed [`NodeReader`](crate::NodeReader) substrate
//! and folds structure over it; its only failure modes are a propagated reader
//! error and a corrupted-on-read invariant violation. Multi-algorithm and epoch
//! errors (unknown algorithm, frozen, malformed timeline) are the `epoch`
//! combinator's concern, not the single-algorithm engine's.

use std::fmt;

/// CML engine error, parameterised by the [`NodeReader`](crate::NodeReader)
/// backend's error type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error<E> {
    /// An error wrapper around the read backend's error type.
    Read(E),
    /// A stored node or frontier read back malformed (wrong digest width, a
    /// missing node in an active range, or a frontier-stack underflow during the
    /// carry). The `alg_id` names which algorithm's view the engine was driving.
    Corrupted {
        /// The algorithm ID the engine was driving when the invariant broke.
        alg_id: u64,
        /// Why the read-back is corrupt.
        reason: String,
    },
}

impl<E: fmt::Display> fmt::Display for Error<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Read(e) => write!(f, "read error: {e}"),
            Self::Corrupted { alg_id, reason } => {
                write!(f, "corrupted state for algorithm {alg_id}: {reason}")
            },
        }
    }
}

impl<E: std::error::Error + 'static> std::error::Error for Error<E> {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Read(e) => Some(e),
            Self::Corrupted { .. } => None,
        }
    }
}

/// A specialized `Result` alias for the CML engine.
pub type Result<T, E> = std::result::Result<T, Error<E>>;
