//! The combinator driver's error type.
//!
//! [`NaryMerkleLog`](crate::NaryMerkleLog) drives N single-algorithm CML engines
//! over one shared storage substrate; its error space is the union of the
//! storage backend's errors, the multi-algorithm management errors the
//! combinator owns (unknown / duplicate / frozen / active algorithm, no active
//! algorithms), and the structural corruption the CML engine surfaces on read.
//! The single-snapshot [`Error`](crate::Error) (malformed timeline / spine) is a
//! distinct, non-storage-parameterised concern.

use std::fmt;

/// The combinator driver's error, parameterised by the storage backend's error
/// type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LogError<E> {
    /// An error wrapper around the storage backend's error type.
    Storage(E),
    /// Algorithm not found.
    UnknownAlgorithm(u64),
    /// Algorithm already registered.
    DuplicateAlgorithm(u64),
    /// Algorithm is frozen (deactivated) and cannot be modified.
    FrozenAlgorithm(u64),
    /// Algorithm is active and cannot be resumed.
    AlgorithmActive(u64),
    /// No algorithms are active.
    NoActiveAlgorithms,
    /// Index out of bounds.
    IndexOutOfBounds {
        /// The requested index.
        index: u64,
        /// The algorithm's tree size.
        tree_size: u64,
    },
    /// Persisted metadata does not match provided hashers on restore.
    OrphanedMetadata(u64),
    /// Provided hasher has no matching persisted metadata on restore.
    UnknownMetadata(u64),
    /// Persistent metadata is corrupted.
    CorruptedMetadata {
        /// The algorithm ID.
        alg_id: u64,
        /// Description of why it is corrupted.
        reason: String,
    },
    /// The spine rejected the timeline while building a [`spine::Seal`] /
    /// [`crate::BoundSnapshot`] (the committed epochs are not well-formed at the
    /// sealed size).
    MalformedSeal,
}

impl<E: fmt::Display> fmt::Display for LogError<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Storage(e) => write!(f, "storage error: {e}"),
            Self::UnknownAlgorithm(id) => write!(f, "unknown algorithm: {id}"),
            Self::DuplicateAlgorithm(id) => write!(f, "algorithm already registered: {id}"),
            Self::FrozenAlgorithm(id) => write!(f, "algorithm is frozen: {id}"),
            Self::AlgorithmActive(id) => write!(f, "algorithm is active: {id}"),
            Self::NoActiveAlgorithms => write!(f, "no active algorithms"),
            Self::IndexOutOfBounds { index, tree_size } => {
                write!(f, "index {index} out of bounds for tree size {tree_size}")
            },
            Self::OrphanedMetadata(id) => {
                write!(
                    f,
                    "algorithm {id} in storage metadata but no hasher provided"
                )
            },
            Self::UnknownMetadata(id) => {
                write!(
                    f,
                    "hasher provided for algorithm {id} with no stored metadata"
                )
            },
            Self::CorruptedMetadata { alg_id, reason } => {
                write!(f, "corrupted metadata for algorithm {alg_id}: {reason}")
            },
            Self::MalformedSeal => write!(f, "spine rejected the timeline while sealing"),
        }
    }
}

impl<E: std::error::Error + 'static> std::error::Error for LogError<E> {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Storage(e) => Some(e),
            _ => None,
        }
    }
}

/// A specialized `Result` alias for the combinator driver.
pub type LogResult<T, E> = std::result::Result<T, LogError<E>>;

impl<E> From<E> for LogError<E> {
    fn from(err: E) -> Self {
        Self::Storage(err)
    }
}

/// Map a CML engine error into the combinator's error space. A read error
/// becomes a storage error; a CML structural corruption becomes the
/// combinator's [`CorruptedMetadata`](LogError::CorruptedMetadata) carrying the
/// same algorithm and reason.
impl<E> From<cml::Error<E>> for LogError<E> {
    fn from(e: cml::Error<E>) -> Self {
        match e {
            cml::Error::Read(e) => Self::Storage(e),
            cml::Error::Corrupted { alg_id, reason } => Self::CorruptedMetadata { alg_id, reason },
        }
    }
}
