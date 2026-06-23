//! `Sealed` — the kernel currency a mutable construction seals into and an
//! append-only construction consumes.
//!
//! `Sealed` makes the seal **one-way**: its fields are private, the only ingress
//! is [`Sealed::new`] (which validates the committed timeline), and the only
//! egress is a read borrow. There is no `unseal` and no field-level mutator, so
//! a value cannot be walked back to the construction it came from.

use crate::error::{Error, Result};
use crate::proof::validate_committed_epochs;

/// A sealed frontier: the active member roots and the committed epoch timeline
/// as they stood at `tree_size`, frozen so they can be carried across a seal.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Sealed {
    /// Tree size at which this frontier was sealed.
    tree_size: u64,
    /// Active member roots at the sealed size, sorted by algorithm ID:
    /// `(alg_id, raw_root)`.
    active_roots: Vec<(u64, Vec<u8>)>,
    /// Committed epoch timeline of every registered algorithm at the sealed
    /// size, sorted by algorithm ID.
    alg_epochs: Vec<(u64, Vec<(u64, u64)>)>,
}

impl Sealed {
    /// Seal a frontier at `tree_size`.
    ///
    /// The committed timeline must be well-formed at `tree_size`
    /// ([`validate_committed_epochs`]); otherwise this returns
    /// [`Error::MalformedEpochs`]. This is the only way to construct a
    /// `Sealed`, so every value in circulation carries a validated timeline.
    pub fn new(
        tree_size: u64,
        active_roots: Vec<(u64, Vec<u8>)>,
        alg_epochs: Vec<(u64, Vec<(u64, u64)>)>,
    ) -> Result<Self> {
        if !validate_committed_epochs(&alg_epochs, tree_size) {
            return Err(Error::MalformedEpochs);
        }
        Ok(Self {
            tree_size,
            active_roots,
            alg_epochs,
        })
    }

    /// The tree size this frontier was sealed at.
    #[must_use]
    pub fn tree_size(&self) -> u64 {
        self.tree_size
    }

    /// A read borrow of the sealed active member roots.
    #[must_use]
    pub fn active_roots(&self) -> &[(u64, Vec<u8>)] {
        &self.active_roots
    }

    /// A read borrow of the sealed committed epoch timeline.
    #[must_use]
    pub fn alg_epochs(&self) -> &[(u64, Vec<(u64, u64)>)] {
        &self.alg_epochs
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new_rejects_malformed_timeline() {
        // Open epoch starting past the sealed size is ill-formed.
        let err = Sealed::new(3, vec![(0, vec![0xAA; 32])], vec![(0, vec![(5, u64::MAX)])]);
        assert_eq!(err, Err(Error::MalformedEpochs));
    }

    #[test]
    fn new_accepts_well_formed_and_reads_back() {
        let sealed = Sealed::new(5, vec![(0, vec![0xAA; 32])], vec![(0, vec![(0, u64::MAX)])])
            .expect("well-formed timeline");
        assert_eq!(sealed.tree_size(), 5);
        assert_eq!(sealed.active_roots(), &[(0, vec![0xAA; 32])]);
        assert_eq!(sealed.alg_epochs(), &[(0, vec![(0, u64::MAX)])]);
    }
}
