//! Minimal kernel error type.
//!
//! The kernel's verification surface (inclusion, coupling) reports failure with
//! `bool` / `Option`, so it needs no error type. Errors arise only where the
//! kernel *constructs* a checked value — sealing a frontier — and the input can
//! be structurally ill-formed. This enum stays deliberately small: the
//! storage-aware, algorithm-lifecycle errors belong to the engineering library
//! above the kernel, not here.

use std::fmt;

/// A kernel construction error.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
    /// The spine arity is outside the valid range `2..=256`.
    BadArity,
    /// A frontier was sealed with a malformed committed epoch timeline (not
    /// well-formed at the sealed tree size; see
    /// [`crate::proof::validate_committed_epochs`]), or the number of frontier
    /// peaks supplied does not match the expected count for `(tree_size, arity)`.
    MalformedEpochs,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::BadArity => write!(f, "spine arity is outside the valid range 2..=256"),
            Self::MalformedEpochs => {
                write!(
                    f,
                    "committed epoch timeline is not well-formed at the sealed tree size"
                )
            },
        }
    }
}

impl std::error::Error for Error {}

/// A specialized `Result` alias for the kernel.
pub type Result<T> = std::result::Result<T, Error>;
