//! `Sealed` — the combinator's frozen multi-algorithm snapshot.
//!
//! `Sealed` is the polydigest combinator's public commitment: the structural
//! [`spine::Seal`] (frontier peaks + run-extents + opaque metadata) paired with
//! the **committed epoch timeline**, from which the **binding root** is derived.
//! It is the combinator-over-`Seal` (D13): the structural facet stays invariant
//! under algorithm churn, and this type adds the epoch facet as a wrapper rather
//! than baking an epoch field into the structural `Seal`.
//!
//! Internally it is a thin shell over [`BoundSnapshot`](crate::BoundSnapshot) —
//! the epoch facet — exposing the structural views (delegated to the seal) and
//! the epoch views (the binding root) on one type, the shape the append-only log
//! and the proofs over a snapshot consume.

use spine::{Hasher, Meta, RunExtent, Seal, frontier_for_size};

use crate::error::{Error, Result};
use crate::snapshot::BoundSnapshot;

/// The combinator's frozen multi-algorithm snapshot: a structural [`Seal`]
/// bound to a committed epoch timeline, deriving the binding root.
///
/// Beside the structural seal it carries the **dormant frontiers**: for each
/// algorithm closed before the seal, its frontier peaks at its close size. They
/// are not part of the structural seal (the member roots, binding root and
/// run-extents are derived from the active algorithms alone, unchanged), but a
/// resume needs them so a closed algorithm can still be resumed
/// ([`NaryMerkleLog::resume_algorithm`](crate::NaryMerkleLog::resume_algorithm)).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Sealed {
    snapshot: BoundSnapshot,
    dormant: Vec<(u64, Vec<Vec<u8>>)>,
}

impl Sealed {
    /// Seal a resumable frontier at `tree_size` with its committed timeline.
    ///
    /// # Errors
    ///
    /// Returns [`crate::Error::Spine`] for an ill-formed arity or frontier, or
    /// [`crate::Error::MalformedEpochs`] for an ill-formed timeline.
    pub fn new(
        tree_size: u64,
        arity: u64,
        frontiers: Vec<(u64, Vec<Vec<u8>>)>,
        alg_epochs: Vec<(u64, Vec<(u64, u64)>)>,
    ) -> Result<Self> {
        let seal = Seal::new(tree_size, arity, frontiers)?;
        Ok(Self {
            snapshot: BoundSnapshot::new(seal, alg_epochs)?,
            dormant: Vec::new(),
        })
    }

    /// Attach the dormant frontiers: each closed algorithm's frontier peaks at
    /// its close size, consuming and returning `self`. Replaces any earlier set.
    ///
    /// # Errors
    ///
    /// Returns [`crate::Error::MalformedEpochs`] if an entry names an algorithm
    /// whose committed timeline is absent or still open, or is named twice or
    /// also carries an active frontier, and [`crate::Error::Spine`] wrapping
    /// [`spine::Error::MalformedFrontier`] if its peak count does not match the
    /// canonical frontier geometry at its close size.
    pub fn with_dormant_frontiers(mut self, dormant: Vec<(u64, Vec<Vec<u8>>)>) -> Result<Self> {
        let arity = self.arity();
        for (i, (id, peaks)) in dormant.iter().enumerate() {
            let close = self
                .alg_epochs()
                .iter()
                .find(|(eid, _)| eid == id)
                .and_then(|(_, epochs)| epochs.last())
                .map(|&(_, end)| end)
                .filter(|&end| end != u64::MAX)
                .ok_or(Error::MalformedEpochs)?;
            if self.peaks(*id).is_some() || dormant[..i].iter().any(|(other, _)| other == id) {
                return Err(Error::MalformedEpochs);
            }
            if peaks.len() != frontier_for_size(close, arity).len() {
                return Err(spine::Error::MalformedFrontier.into());
            }
        }
        self.dormant = dormant;
        Ok(self)
    }

    /// The frontier peaks, at its close size, of each algorithm closed before
    /// the seal. Empty for a seal taken while every algorithm was active.
    #[must_use]
    pub fn dormant_frontiers(&self) -> &[(u64, Vec<Vec<u8>>)] {
        &self.dormant
    }

    /// Attach an opaque metadata payload, consuming and returning `self`.
    #[must_use]
    pub fn with_meta(self, meta: Meta) -> Self {
        let alg_epochs = self.snapshot.alg_epochs().to_vec();
        let seal = self.snapshot.seal().clone().with_meta(meta);
        // The timeline already validated at construction, so re-binding cannot fail.
        Self {
            snapshot: BoundSnapshot::new(seal, alg_epochs).expect("timeline already validated"),
            dormant: self.dormant,
        }
    }

    /// The tree size this frontier was sealed at.
    #[must_use]
    pub fn tree_size(&self) -> u64 {
        self.snapshot.seal().tree_size()
    }

    /// The spine arity `k` this frontier was sealed under.
    #[must_use]
    pub fn arity(&self) -> u64 {
        self.snapshot.seal().arity()
    }

    /// A read borrow of each active algorithm's frontier peaks.
    #[must_use]
    pub fn frontiers(&self) -> &[(u64, Vec<Vec<u8>>)] {
        self.snapshot.seal().frontiers()
    }

    /// The frontier peaks of a single algorithm, if active at the sealed size.
    #[must_use]
    pub fn peaks(&self, alg_id: u64) -> Option<&[Vec<u8>]> {
        self.snapshot.seal().peaks(alg_id)
    }

    /// A read borrow of the sealed committed epoch timeline.
    #[must_use]
    pub fn alg_epochs(&self) -> &[(u64, Vec<(u64, u64)>)] {
        self.snapshot.alg_epochs()
    }

    /// A read borrow of the attached opaque metadata, if any.
    #[must_use]
    pub fn meta(&self) -> Option<&Meta> {
        self.snapshot.seal().meta()
    }

    /// **Derived view.** Each active algorithm's member root, bagged with `bag`
    /// (the structure's peak fold — see [`spine::BagFn`]).
    #[must_use]
    pub fn member_roots(
        &self,
        hashers: &[(u64, &dyn Hasher)],
        bag: spine::BagFn,
    ) -> Vec<(u64, Vec<u8>)> {
        self.snapshot.seal().member_roots(hashers, bag)
    }

    /// **Derived view.** A single algorithm's member root, bagged with `bag`.
    #[must_use]
    pub fn member_root(
        &self,
        alg_id: u64,
        hasher: &dyn Hasher,
        bag: spine::BagFn,
    ) -> Option<Vec<u8>> {
        self.snapshot.seal().member_root(alg_id, hasher, bag)
    }

    /// **Derived view.** Every active algorithm's member root, erroring on a
    /// missing hasher. Bagged with `bag`.
    ///
    /// # Errors
    ///
    /// Returns [`crate::Error::Spine`] wrapping [`spine::Error::MissingHasher`]
    /// (naming the algorithm) if any active algorithm has no hasher in `hashers`.
    pub fn all_member_roots(
        &self,
        hashers: &[(u64, &dyn Hasher)],
        bag: spine::BagFn,
    ) -> Result<Vec<(u64, Vec<u8>)>> {
        self.snapshot
            .seal()
            .all_member_roots(hashers, bag)
            .map_err(Into::into)
    }

    /// **Derived view.** Each active algorithm's binding root, over member roots
    /// bagged with `bag`.
    ///
    /// # Errors
    ///
    /// Returns [`crate::Error::Spine`] wrapping [`spine::Error::MissingHasher`]
    /// (naming the algorithm) if any active algorithm has no hasher in `hashers`.
    pub fn binding_roots(
        &self,
        hashers: &[(u64, &dyn Hasher)],
        bag: spine::BagFn,
    ) -> Result<Vec<(u64, Vec<u8>)>> {
        self.snapshot.binding_roots(hashers, bag)
    }

    /// **Derived view.** A single algorithm's binding root under `hasher`, over
    /// member roots bagged with `bag`.
    ///
    /// # Errors
    ///
    /// Returns [`crate::Error::Spine`] wrapping [`spine::Error::MissingHasher`]
    /// (naming the algorithm) if any active algorithm — including `alg_id` — has
    /// no hasher in `all_hashers`.
    pub fn binding_root(
        &self,
        alg_id: u64,
        hasher: &dyn Hasher,
        all_hashers: &[(u64, &dyn Hasher)],
        bag: spine::BagFn,
    ) -> Result<Option<Vec<u8>>> {
        self.snapshot.binding_root(alg_id, hasher, all_hashers, bag)
    }

    /// **Derived view.** The committed canonicalization run-extents.
    #[must_use]
    pub fn run_extents(&self) -> Vec<RunExtent> {
        self.snapshot.seal().run_extents()
    }
}
