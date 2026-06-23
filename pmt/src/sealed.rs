//! `Sealed` — the kernel currency a mutable construction seals into and an
//! append-only construction consumes.
//!
//! `Sealed` makes the seal **one-way**: its fields are private, the only ingress
//! is [`Sealed::new`] (which validates the committed timeline), and the only
//! egress is a read borrow. There is no `unseal` and no field-level mutator, so
//! a value cannot be walked back to the construction it came from.
//!
//! # Metadata channel
//!
//! `Sealed` carries an optional [`crate::Meta`] — an opaque, arbitrary byte
//! payload the library never interprets. It is set via [`Sealed::with_meta`]
//! and read via [`Sealed::meta`]. The channel is additive: a `Sealed` without
//! metadata behaves identically to one with `None`.

use crate::error::{Error, Result};
use crate::metadata::Meta;
use crate::proof::validate_committed_epochs;

/// A sealed frontier: the active member roots and the committed epoch timeline
/// as they stood at `tree_size`, frozen so they can be carried across a seal.
///
/// An optional opaque metadata channel ([`Meta`]) may be attached; the kernel
/// never reads or validates it.
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
    /// Opaque metadata channel; library never inspects the contents.
    meta: Option<Meta>,
}

impl Sealed {
    /// Seal a frontier at `tree_size` with no metadata attached.
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
            meta: None,
        })
    }

    /// Attach an opaque metadata payload, consuming and returning `self`.
    ///
    /// The library never reads or validates the payload; any byte sequence is
    /// accepted. Calling this again replaces any previously attached payload.
    #[must_use]
    pub fn with_meta(mut self, meta: Meta) -> Self {
        self.meta = Some(meta);
        self
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

    /// A read borrow of the attached opaque metadata, if any.
    ///
    /// Returns `None` when no metadata was attached via [`Self::with_meta`].
    /// The library never interprets the bytes; fidelity (round-trip) is the
    /// only guarantee.
    #[must_use]
    pub fn meta(&self) -> Option<&Meta> {
        self.meta.as_ref()
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

    // -------------------------------------------------------------------
    // Metadata channel — round-trip and additive tests.
    // -------------------------------------------------------------------

    #[test]
    fn new_has_no_meta() {
        let sealed = Sealed::new(1, vec![(0, vec![0xBB; 32])], vec![(0, vec![(0, u64::MAX)])])
            .expect("well-formed");
        assert_eq!(sealed.meta(), None);
    }

    #[test]
    fn with_meta_round_trips_arbitrary_bytes() {
        let payload: Vec<u8> = (0u8..=255u8).collect();
        let sealed = Sealed::new(1, vec![(0, vec![0xCC; 32])], vec![(0, vec![(0, u64::MAX)])])
            .expect("well-formed")
            .with_meta(Meta::new(payload.clone()));
        let got = sealed.meta().expect("metadata present");
        assert_eq!(got.as_bytes(), payload.as_slice());
    }

    #[test]
    fn with_meta_empty_bytes_round_trips() {
        let sealed = Sealed::new(2, vec![(0, vec![0xDD; 32])], vec![(0, vec![(0, u64::MAX)])])
            .expect("well-formed")
            .with_meta(Meta::new(vec![]));
        let got = sealed.meta().expect("metadata present");
        assert!(got.is_empty());
    }

    #[test]
    fn with_meta_does_not_change_other_fields() {
        let payload = vec![0xAB; 64];
        let sealed = Sealed::new(7, vec![(1, vec![0xEE; 32])], vec![(1, vec![(0, u64::MAX)])])
            .expect("well-formed")
            .with_meta(Meta::new(payload));
        // Core commitment fields are unchanged.
        assert_eq!(sealed.tree_size(), 7);
        assert_eq!(sealed.active_roots(), &[(1, vec![0xEE; 32])]);
        assert_eq!(sealed.alg_epochs(), &[(1, vec![(0, u64::MAX)])]);
    }

    #[test]
    fn with_meta_replaces_previous_meta() {
        let first = Meta::new(vec![0x01]);
        let second = Meta::new(vec![0x02, 0x03]);
        let sealed = Sealed::new(3, vec![(0, vec![0xFF; 32])], vec![(0, vec![(0, u64::MAX)])])
            .expect("well-formed")
            .with_meta(first)
            .with_meta(second.clone());
        assert_eq!(sealed.meta().unwrap().as_bytes(), second.as_bytes());
    }

    #[test]
    fn sealed_with_and_without_meta_differ() {
        let base = Sealed::new(4, vec![(0, vec![0x11; 32])], vec![(0, vec![(0, u64::MAX)])])
            .expect("well-formed");
        let with = base.clone().with_meta(Meta::new(vec![42]));
        // Meta changes the value.
        assert_ne!(base, with);
    }
}
