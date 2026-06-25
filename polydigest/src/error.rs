//! The epoch combinator's error type.
//!
//! The structural spine reports its construction errors with [`spine::Error`]
//! (bad arity, malformed frontier, missing hasher). The epoch combinator adds
//! the one failure mode the structural layer cannot have: a committed epoch
//! timeline that is not well-formed at the bound size.

use std::fmt;

/// An epoch combinator error.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
    /// A snapshot was bound with a malformed committed epoch timeline: not
    /// well-formed at the bound tree size (see
    /// [`crate::validate_committed_epochs`]).
    MalformedEpochs,
    /// A structural construction error surfaced from the spine while building
    /// the bound snapshot (bad arity, malformed frontier, or a missing hasher).
    Spine(spine::Error),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MalformedEpochs => {
                write!(
                    f,
                    "committed epoch timeline is not well-formed at the bound tree size"
                )
            },
            Self::Spine(e) => write!(f, "{e}"),
        }
    }
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Spine(e) => Some(e),
            Self::MalformedEpochs => None,
        }
    }
}

impl From<spine::Error> for Error {
    fn from(e: spine::Error) -> Self {
        Self::Spine(e)
    }
}

/// A specialized `Result` alias for the epoch combinator.
pub type Result<T> = std::result::Result<T, Error>;
