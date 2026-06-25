//! `BoundSnapshot` — the epoch facet over the general structural [`Seal`].
//!
//! The structural [`Seal`] freezes the *structural* facet of a snapshot — the
//! resumable frontier, the member roots folded from it, the run-extents, and the
//! opaque metadata channel. It carries no epoch concept (D13).
//!
//! `BoundSnapshot` is the **combinator over the `Seal`**: it pairs a structural
//! `Seal` with the **committed epoch timeline**, and from the two derives the
//! **binding root** — the atomic multi-tree commitment. The epoch facet is added
//! here as a wrapper, never baked into the structural `Seal`; that is what keeps
//! the `Seal` interface invariant when algorithms are added or retired.
//!
//! A `BoundSnapshot` is the natural producer of a [`crate::BindingProof`]: its
//! member roots and committed timeline are exactly the shared structure the
//! binding proof commits.

use spine::{Hasher, Seal};

use crate::error::{Error, Result};
use crate::root::{combined_root, validate_committed_epochs};

/// The epoch facet over a structural [`Seal`]: the seal paired with the
/// committed epoch timeline, from which the binding root is derived.
///
/// The structural `Seal` and the committed timeline together are the full
/// snapshot a multi-algorithm structure commits. Construction validates the
/// timeline against the seal's tree size, so every `BoundSnapshot` in
/// circulation carries a well-formed timeline.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BoundSnapshot {
    /// The structural facet — frontier peaks, member roots, run-extents, meta.
    seal: Seal,
    /// Committed epoch timeline of every registered algorithm at the sealed
    /// size, sorted by algorithm ID. The epoch facet.
    alg_epochs: Vec<(u64, Vec<(u64, u64)>)>,
}

impl BoundSnapshot {
    /// Bind a structural [`Seal`] to a committed epoch timeline.
    ///
    /// The timeline must be well-formed at the seal's tree size
    /// ([`validate_committed_epochs`]); otherwise this returns
    /// [`Error::MalformedEpochs`]. This is the only way to construct a
    /// `BoundSnapshot`, so every value carries a validated timeline.
    ///
    /// # Errors
    ///
    /// Returns [`Error::MalformedEpochs`] if the committed timeline is ill-formed
    /// at the seal's tree size.
    pub fn new(seal: Seal, alg_epochs: Vec<(u64, Vec<(u64, u64)>)>) -> Result<Self> {
        if !validate_committed_epochs(&alg_epochs, seal.tree_size()) {
            return Err(Error::MalformedEpochs);
        }
        Ok(Self { seal, alg_epochs })
    }

    /// A read borrow of the underlying structural seal.
    #[must_use]
    pub fn seal(&self) -> &Seal {
        &self.seal
    }

    /// A read borrow of the committed epoch timeline.
    #[must_use]
    pub fn alg_epochs(&self) -> &[(u64, Vec<(u64, u64)>)] {
        &self.alg_epochs
    }

    /// **Derived view.** Each algorithm's binding root: `(alg_id, binding_root)`,
    /// sorted by algorithm ID. A binding root is the [`combined_root`] — the
    /// canonicalization fold over the member roots as children (plus a coverage
    /// child iff the committed timeline is non-trivial), under that algorithm's
    /// own hash — the head the rest of the structure authenticates against.
    /// Computed on demand, never stored.
    ///
    /// Genesis promotion is native to the fold: a single member root under a
    /// trivial timeline folds (`nary_mr` `len == 1`) to that member root, so the
    /// promoted form is the structural consequence of having one child — there
    /// is no promotion predicate.
    ///
    /// `hashers` must resolve **every** algorithm's own hash: the fold commits
    /// all of them as children, so a missing one is [`spine::Error::MissingHasher`]
    /// (surfaced as [`Error::Spine`]), not a silent skip — a binding root folded
    /// over a truncated child set is one no algorithm published.
    ///
    /// # Errors
    ///
    /// Returns [`Error::Spine`] wrapping [`spine::Error::MissingHasher`] (naming
    /// the algorithm) if any algorithm with a frontier in the seal has no hasher
    /// in `hashers`.
    pub fn binding_roots(
        &self,
        hashers: &[(u64, &dyn Hasher)],
        bag: spine::BagFn,
    ) -> Result<Vec<(u64, Vec<u8>)>> {
        let members = self.seal.all_member_roots(hashers, bag)?;
        members
            .iter()
            .map(|(id, _)| {
                // Resolved already by `all_member_roots`, so this lookup cannot fail.
                let hasher = hashers
                    .iter()
                    .find(|(hid, _)| hid == id)
                    .map(|(_, h)| *h)
                    .ok_or(spine::Error::MissingHasher { alg_id: *id })?;
                Ok((
                    *id,
                    combined_root(
                        hasher,
                        &members,
                        &self.alg_epochs,
                        self.seal.tree_size(),
                        self.seal.arity(),
                    ),
                ))
            })
            .collect()
    }

    /// **Derived view.** A single algorithm's binding root under `hasher`.
    ///
    /// The fold is over **every** algorithm's member root, so `all_hashers` must
    /// resolve them all; the single returned binding root is the one for `alg_id`
    /// under `hasher`. See [`Self::binding_roots`].
    ///
    /// Returns `Ok(None)` if `alg_id` has no frontier in the seal (a well-formed
    /// query about an absent algorithm, not an error).
    ///
    /// # Errors
    ///
    /// Returns [`Error::Spine`] wrapping [`spine::Error::MissingHasher`] (naming
    /// the algorithm) if any algorithm with a frontier in the seal — including
    /// `alg_id` itself — has no hasher in `all_hashers`. A missing hasher would
    /// silently fold over a truncated child set and yield a binding root no
    /// algorithm committed.
    pub fn binding_root(
        &self,
        alg_id: u64,
        hasher: &dyn Hasher,
        all_hashers: &[(u64, &dyn Hasher)],
        bag: spine::BagFn,
    ) -> Result<Option<Vec<u8>>> {
        // An algorithm with no frontier was never active at the sealed size:
        // a well-formed `None`, distinct from a missing-hasher error.
        if self.seal.peaks(alg_id).is_none() {
            return Ok(None);
        }
        // The complete child set the fold commits — errors if any algorithm
        // lacks a hasher, rather than silently dropping it.
        let members = self.seal.all_member_roots(all_hashers, bag)?;
        Ok(Some(combined_root(
            hasher,
            &members,
            &self.alg_epochs,
            self.seal.tree_size(),
            self.seal.arity(),
        )))
    }
}

#[cfg(test)]
mod tests {
    use sha2::{Digest, Sha256};

    use super::*;

    #[derive(Debug, Clone)]
    struct H;
    impl Hasher for H {
        fn leaf(&self, data: &[u8]) -> Vec<u8> {
            Sha256::digest(data).to_vec()
        }

        fn node(&self, children: &[&[u8]]) -> Vec<u8> {
            let mut h = Sha256::new();
            for c in children {
                h.update(c);
            }
            h.finalize().to_vec()
        }

        fn empty(&self) -> Vec<u8> {
            Sha256::digest(b"").to_vec()
        }

        fn hash(&self, data: &[u8]) -> Vec<u8> {
            Sha256::digest(data).to_vec()
        }

        fn clone_box(&self) -> Box<dyn Hasher> {
            Box::new(self.clone())
        }
    }

    #[test]
    fn new_rejects_malformed_timeline() {
        // Open epoch starting past the sealed size is ill-formed.
        let seal = Seal::new(3, 2, vec![(0, vec![vec![0xAA; 32], vec![0xBB; 32]])])
            .expect("well-formed seal");
        assert_eq!(
            BoundSnapshot::new(seal, vec![(0, vec![(5, u64::MAX)])]),
            Err(Error::MalformedEpochs)
        );
    }

    /// The append-only log's mountain bag — these tests exercise the
    /// binding-root fold over member roots, so any consistent `bag` works; the
    /// MMR bag stands in for a concrete topology.
    fn bag(hasher: &dyn Hasher, peaks: &[Vec<u8>], k: u64) -> Vec<u8> {
        cml::mountain::bag_peaks(hasher, peaks, k)
    }

    #[test]
    fn promoted_registry_binding_root_equals_member_root() {
        let p0 = vec![0x11; 32];
        let p1 = vec![0x22; 32];
        let seal = Seal::new(3, 2, vec![(0, vec![p0.clone(), p1.clone()])]).expect("well-formed");
        let member = seal.member_root(0, &H, bag).unwrap();
        let snap =
            BoundSnapshot::new(seal, vec![(0, vec![(0, u64::MAX)])]).expect("well-formed timeline");
        let hashers: [(u64, &dyn Hasher); 1] = [(0, &H)];
        assert_eq!(
            snap.binding_root(0, &H, &hashers, bag),
            Ok(Some(member.clone()))
        );
        assert_eq!(snap.binding_roots(&hashers, bag), Ok(vec![(0, member)]));
    }

    #[test]
    fn binding_root_errors_on_a_missing_active_hasher() {
        // Two algorithms with frontiers, but a hasher only for alg 0. The
        // binding-root fold commits *both* member roots as children, so a missing
        // hasher for alg 1 must surface as a clear error rather than silently
        // folding over a truncated child set.
        let p0 = vec![0x11; 32];
        let p1 = vec![0x22; 32];
        let seal = Seal::new(
            3,
            2,
            vec![(0, vec![p0.clone(), p0.clone()]), (1, vec![p1.clone(), p1])],
        )
        .expect("well-formed");
        let snap = BoundSnapshot::new(
            seal,
            vec![(0, vec![(0, u64::MAX)]), (1, vec![(0, u64::MAX)])],
        )
        .expect("well-formed timeline");
        let partial: [(u64, &dyn Hasher); 1] = [(0, &H)];

        // The single-root accessor errors naming the absent algorithm …
        assert_eq!(
            snap.binding_root(0, &H, &partial, bag),
            Err(Error::Spine(spine::Error::MissingHasher { alg_id: 1 }))
        );
        // … and so does the all-roots accessor.
        assert_eq!(
            snap.binding_roots(&partial, bag),
            Err(Error::Spine(spine::Error::MissingHasher { alg_id: 1 }))
        );

        // With every hasher present the fold succeeds.
        let full: [(u64, &dyn Hasher); 2] = [(0, &H), (1, &H)];
        assert!(snap.binding_root(0, &H, &full, bag).unwrap().is_some());
        assert_eq!(snap.binding_roots(&full, bag).unwrap().len(), 2);

        // An algorithm with no frontier is a well-formed `Ok(None)`, never an
        // error — distinct from a missing hasher for an active algorithm.
        assert_eq!(snap.binding_root(9, &H, &full, bag), Ok(None));
    }
}
