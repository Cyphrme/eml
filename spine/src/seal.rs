//! `Seal` — the general structural commitment lattice.
//!
//! Every freeze of a tree — mutable or append-only — produces a `Seal`. There
//! is exactly one structural commitment type, and it carries the **resumable
//! frontier**: per algorithm, the digests of the perfect k-ary subtrees that
//! [`frontier_for_size`](crate::topology::frontier_for_size) names at the sealed
//! size (the "peaks", in MMR terms). The frontier is the complete continuation
//! state of an append-only log, so a log can be *resumed* from any `Seal`
//! regardless of which kind sealed it.
//!
//! # Structural only — no epoch facet (D13)
//!
//! `Seal` is the **structural facet** of a snapshot: frontier peaks, the member
//! roots folded from them, the canonicalization run-extents, and an opaque
//! metadata channel. It carries **no committed epoch timeline and no binding
//! root** — those are the *epoch facet*, added by the `polydigest` combinator as a
//! wrapper over this general `Seal`, never baked in. Keeping the epoch logic out
//! is what lets the structural facet stay invariant when algorithms are added or
//! retired (the `Seal` interface does not move under algorithm churn).
//!
//! # One commitment, derived views
//!
//! The frontier is the stored content; everything else a consumer asks of a
//! `Seal` is a **derived view**, computed on demand and never stored (this
//! metadata is provably derivable from the tree, not a parallel committed
//! channel):
//!
//! - each algorithm's **member root** is the consumer's *bag* of its frontier peaks
//!   ([`Seal::member_root`]) — the raw per-algorithm root the leaves authenticate against. The
//!   `Seal` stores peaks only and is topology-agnostic: how peaks bag into one root (an append-only
//!   log's mountain backward-bag, a mutable tree's rebalanced fold) is supplied by the consumer,
//!   not owned here;
//! - the **canonicalization run-extents** are the height `>= 1` frontier nodes, derived from
//!   `(tree_size, arity)` alone ([`Seal::run_extents`]).
//!
//! Member roots are bags, so they need the algorithm's own hasher *and* the
//! consumer's bagging function; the run-extents are pure geometry and need
//! nothing. The **binding root** — the combined root over the member roots and
//! the committed timeline — is the `polydigest` combinator's derived view, not the
//! structural `Seal`'s.
//!
//! # One-way
//!
//! `Seal` makes the seal **one-way**: its fields are private, the only ingress
//! is [`Seal::new`], and the only egress is a read borrow or a derived view.
//! There is no `unseal` and no field-level mutator, so a value cannot be walked
//! back to the construction it came from.
//!
//! # Metadata channel
//!
//! `Seal` carries an optional [`crate::Meta`] — an opaque, arbitrary byte
//! payload the library never interprets (an out-of-band tree-head attestation
//! may ride here). It is set via [`Seal::with_meta`] and read via [`Seal::meta`].
//! The channel is additive: a `Seal` without metadata behaves identically to one
//! with `None`.

use crate::error::{Error, Result};
use crate::hasher::Hasher;
use crate::metadata::Meta;
use crate::topology::{ARITY_RANGE, frontier_for_size};

/// One committed canonicalization run-extent: a contiguous collapse of
/// `arity^height` consecutive leaves into a single subtree, beginning at leaf
/// index `left`.
///
/// A run-extent is emitted only for a *collapse* — a frontier node above leaf
/// level (`height >= 1`). A promoted singleton leaf (`height == 0`) is
/// structurally deterministic and commits no run-extent (promotion commits
/// nothing, collapse commits its minimal run-extent), so it never appears here.
///
/// The extent is the minimal metadata the `fill` step unrolls from: it says how
/// many real historical leaves a subtree root stands for, so a complete
/// (gapless) history can be recomputed without inferring shape from the digest.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RunExtent {
    /// Index of the first leaf the run collapses.
    left: u64,
    /// Height of the collapsed subtree; the run spans `arity.pow(height)`
    /// leaves. Always `>= 1` — a height-0 node is a promotion, not a collapse.
    height: u32,
}

impl RunExtent {
    /// Index of the first leaf this run collapses.
    #[must_use]
    pub fn left(&self) -> u64 {
        self.left
    }

    /// Height of the collapsed subtree. The run spans `arity.pow(height)`
    /// leaves.
    #[must_use]
    pub fn height(&self) -> u32 {
        self.height
    }

    /// Number of leaves this run collapses, given the arity `k`.
    #[must_use]
    pub fn span(&self, k: u64) -> u64 {
        k.pow(self.height)
    }
}

/// The general structural commitment lattice: a sealed, resumable frontier.
///
/// Carries, per algorithm with a frontier at `tree_size`, the digests of the
/// perfect k-ary subtrees of the frontier (the resume state), and an optional
/// opaque metadata channel ([`Meta`]). Member roots and run-extents are *derived
/// views* — see the module docs. The committed epoch timeline and binding root
/// are the `polydigest` combinator's facet, not stored here.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Seal {
    /// Tree size at which this frontier was sealed.
    tree_size: u64,
    /// Arity `k` (`2..=256`) the frontier was sealed under; fixes the frontier
    /// geometry every derived view reads.
    arity: u64,
    /// Per-algorithm frontier peaks: `(alg_id, peaks)`, sorted by algorithm ID.
    /// `peaks` are the digests of the perfect k-ary subtrees named by
    /// [`frontier_for_size`]`(tree_size, arity)`, left to right — the complete
    /// continuation state for an append-only resume. The member root is their
    /// fold.
    frontiers: Vec<(u64, Vec<Vec<u8>>)>,
    /// Opaque metadata channel; library never inspects the contents.
    meta: Option<Meta>,
}

impl Seal {
    /// Seal a resumable frontier at `tree_size` with no metadata attached.
    ///
    /// `arity` is the spine arity `k` (`2..=256`); `frontiers` carries each
    /// algorithm's frontier peaks (the digests of the perfect k-ary subtrees of
    /// the frontier, left to right), sorted by algorithm ID.
    ///
    /// This is the only way to construct a `Seal`, so every value in
    /// circulation carries a correctly-sized frontier. The committed epoch
    /// timeline is **not** an input — it is the `polydigest` combinator's concern.
    ///
    /// # Errors
    ///
    /// Returns [`Error::BadArity`] if `arity` is outside `2..=256`, or
    /// [`Error::MalformedFrontier`] if any algorithm's peak count does not match
    /// the canonical frontier length for `(tree_size, arity)`.
    pub fn new(tree_size: u64, arity: u64, frontiers: Vec<(u64, Vec<Vec<u8>>)>) -> Result<Self> {
        if !ARITY_RANGE.contains(&arity) {
            return Err(Error::BadArity);
        }
        // Cross-check that every algorithm's peak count matches the canonical
        // frontier geometry for (tree_size, arity). A mismatched count means
        // a caller constructed a Seal with a wrong or truncated peaks slice —
        // a malformed frontier that member_root would silently fold incorrectly.
        let expected_peak_count = frontier_for_size(tree_size, arity).len();
        for (_, peaks) in &frontiers {
            if peaks.len() != expected_peak_count {
                return Err(Error::MalformedFrontier);
            }
        }
        Ok(Self {
            tree_size,
            arity,
            frontiers,
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

    /// The spine arity `k` this frontier was sealed under.
    #[must_use]
    pub fn arity(&self) -> u64 {
        self.arity
    }

    /// A read borrow of each algorithm's frontier peaks: `(alg_id, peaks)`,
    /// sorted by algorithm ID. These are the resume state; the member root is
    /// their fold ([`Self::member_root`]).
    #[must_use]
    pub fn frontiers(&self) -> &[(u64, Vec<Vec<u8>>)] {
        &self.frontiers
    }

    /// The frontier peaks of a single algorithm, if it has a frontier in this
    /// seal.
    #[must_use]
    pub fn peaks(&self, alg_id: u64) -> Option<&[Vec<u8>]> {
        self.frontiers
            .iter()
            .find(|(id, _)| *id == alg_id)
            .map(|(_, p)| p.as_slice())
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

    // --- derived views -------------------------------------------------------

    /// **Derived view.** Each algorithm's member root: `(alg_id, member_root)`,
    /// sorted by algorithm ID. A member root is the consumer's `bag` of that
    /// algorithm's frontier peaks under its own hash — the raw per-algorithm root
    /// the leaves authenticate against. Folded on demand, never stored.
    ///
    /// The `Seal` stores peaks only and is **topology-agnostic**: how the peaks
    /// bag into one root is the consumer's choice, supplied as
    /// `bag(hasher, peaks, arity)` — the append-only log passes its mountain
    /// backward-bag, the mutable tree its rebalanced fold. The same `bag` applies
    /// to every algorithm (one topology per structure).
    ///
    /// `hashers` resolves an algorithm's own hash; an algorithm with no hasher
    /// in `hashers` is skipped (its member root cannot be folded).
    #[must_use]
    pub fn member_roots(
        &self,
        hashers: &[(u64, &dyn Hasher)],
        bag: crate::topology::BagFn,
    ) -> Vec<(u64, Vec<u8>)> {
        self.frontiers
            .iter()
            .filter_map(|(id, peaks)| {
                let hasher = hashers.iter().find(|(hid, _)| hid == id).map(|(_, h)| *h)?;
                Some((*id, bag(hasher, peaks, self.arity)))
            })
            .collect()
    }

    /// **Derived view.** A single algorithm's member root — the consumer's `bag`
    /// of its frontier peaks under `hasher`. Returns `None` if the algorithm has
    /// no frontier in this seal. See [`Self::member_roots`] for the `bag`
    /// contract.
    #[must_use]
    pub fn member_root(
        &self,
        alg_id: u64,
        hasher: &dyn Hasher,
        bag: crate::topology::BagFn,
    ) -> Option<Vec<u8>> {
        let peaks = self.peaks(alg_id)?;
        Some(bag(hasher, peaks, self.arity))
    }

    /// **Derived view.** Every algorithm's member root, in sealed (sorted)
    /// order, bagged under the supplied hashers — or [`Error::MissingHasher`]
    /// naming the first algorithm with no hasher.
    ///
    /// Unlike [`Self::member_roots`], which is the *produce*-side view a caller
    /// may legitimately take over a subset of hashers, this is the *complete*
    /// member-root child set the `polydigest` binding-root fold commits. Folding over
    /// a truncated child list would yield a combined root no algorithm
    /// published, so a missing hasher is an error, never a silent skip. See
    /// [`Self::member_roots`] for the `bag` contract.
    ///
    /// # Errors
    ///
    /// Returns [`Error::MissingHasher`] (naming the algorithm) if any algorithm
    /// with a frontier in this seal has no hasher in `hashers`.
    pub fn all_member_roots(
        &self,
        hashers: &[(u64, &dyn Hasher)],
        bag: crate::topology::BagFn,
    ) -> Result<Vec<(u64, Vec<u8>)>> {
        self.frontiers
            .iter()
            .map(|(id, peaks)| {
                let hasher = hashers
                    .iter()
                    .find(|(hid, _)| hid == id)
                    .map(|(_, h)| *h)
                    .ok_or(Error::MissingHasher { alg_id: *id })?;
                Ok((*id, bag(hasher, peaks, self.arity)))
            })
            .collect()
    }

    /// **Derived view.** The committed canonicalization run-extents: the
    /// height `>= 1` nodes of the frontier at the sealed size, in left-to-right
    /// order. Derived from `(tree_size, arity)` alone — never inferred from a
    /// digest. Promotions (height-0 frontier nodes) commit nothing and are
    /// omitted.
    #[must_use]
    pub fn run_extents(&self) -> Vec<RunExtent> {
        frontier_for_size(self.tree_size, self.arity)
            .into_iter()
            .filter(|&(_, height)| height >= 1)
            .map(|(left, height)| RunExtent { left, height })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use sha2::{Digest, Sha256};

    use super::*;

    /// A fixed-width (32-byte) test hasher.
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

    /// A generic rightmost-`k` grouping bag, used here only to exercise the
    /// `Seal`'s topology-agnostic peak-storage mechanism. A real consumer
    /// supplies its own (the log's mountain backward-bag, the tree's rebalanced
    /// fold); the `Seal` itself owns no topology.
    fn test_bag(hasher: &dyn Hasher, peaks: &[Vec<u8>], k: u64) -> Vec<u8> {
        use crate::mr::nary_mr;
        use crate::topology::fold_frontier;
        if peaks.is_empty() {
            return hasher.empty();
        }
        fold_frontier(peaks.to_vec(), k as usize, |chunk| {
            let refs: Vec<&[u8]> = chunk.iter().map(|v| v.as_slice()).collect();
            nary_mr(hasher, &refs)
        })
    }

    #[test]
    fn new_rejects_out_of_range_arity() {
        assert_eq!(
            Seal::new(1, 1, vec![(0, vec![vec![0xAA; 32]])]),
            Err(Error::BadArity)
        );
        assert_eq!(
            Seal::new(1, 257, vec![(0, vec![vec![0xAA; 32]])]),
            Err(Error::BadArity)
        );
    }

    #[test]
    fn new_rejects_mismatched_peak_count() {
        // A wrong peak count is a malformed *frontier*. Size 3, k=2 → frontier =
        // [(0,1),(2,0)] → 2 peaks expected. Supplying 1 peak is malformed.
        assert_eq!(
            Seal::new(3, 2, vec![(0, vec![vec![0xAA; 32]])]),
            Err(Error::MalformedFrontier)
        );
        // Supplying 3 peaks is also malformed.
        assert_eq!(
            Seal::new(
                3,
                2,
                vec![(0, vec![vec![0xAA; 32], vec![0xBB; 32], vec![0xCC; 32]])]
            ),
            Err(Error::MalformedFrontier)
        );
    }

    #[test]
    fn new_accepts_well_formed_and_reads_back() {
        let sealed = Seal::new(1, 2, vec![(0, vec![vec![0xAA; 32]])]).expect("well-formed");
        assert_eq!(sealed.tree_size(), 1);
        assert_eq!(sealed.arity(), 2);
        assert_eq!(sealed.peaks(0), Some([vec![0xAA; 32]].as_slice()));
    }

    #[test]
    fn member_root_folds_a_single_peak_to_itself() {
        // A single frontier peak is the member root (promotion).
        let peak = vec![0xCD; 32];
        let sealed = Seal::new(1, 2, vec![(0, vec![peak.clone()])]).expect("well-formed");
        assert_eq!(sealed.member_root(0, &H, test_bag), Some(peak));
    }

    #[test]
    fn member_root_folds_two_peaks_with_the_hasher() {
        use crate::mr::nary_mr;
        // Two peaks bag to nary_mr(hasher, [p0, p1]) under the generic bag.
        let p0 = vec![0x01; 32];
        let p1 = vec![0x02; 32];
        let expected = nary_mr(&H, &[p0.as_slice(), p1.as_slice()]);
        let sealed = Seal::new(3, 2, vec![(0, vec![p0.clone(), p1.clone()])]).expect("well-formed");
        assert_eq!(sealed.member_root(0, &H, test_bag), Some(expected));
    }

    #[test]
    fn all_member_roots_errors_on_a_missing_hasher() {
        // Two algorithms with frontiers, but a hasher only for alg 0. The
        // complete member-root child set cannot be folded, so a missing hasher
        // for alg 1 must surface as a clear error, not a silent skip.
        let p0 = vec![0x11; 32];
        let p1 = vec![0x22; 32];
        let sealed = Seal::new(
            3,
            2,
            vec![(0, vec![p0.clone(), p0.clone()]), (1, vec![p1.clone(), p1])],
        )
        .expect("well-formed");
        let partial: [(u64, &dyn Hasher); 1] = [(0, &H)];
        assert_eq!(
            sealed.all_member_roots(&partial, test_bag),
            Err(Error::MissingHasher { alg_id: 1 })
        );
        // With every hasher present the fold succeeds.
        let full: [(u64, &dyn Hasher); 2] = [(0, &H), (1, &H)];
        assert_eq!(sealed.all_member_roots(&full, test_bag).unwrap().len(), 2);
    }

    #[test]
    fn run_extents_are_the_collapse_frontier_geometry() {
        // Size 7, k=2: frontier = [(0,2),(4,1),(6,0)]; the height-0 entry is a
        // promotion and is omitted.
        let sealed = Seal::new(
            7,
            2,
            vec![(0, vec![vec![0xAA; 32], vec![0xBB; 32], vec![0xCC; 32]])],
        )
        .expect("well-formed");
        let extents = sealed.run_extents();
        assert_eq!(extents.len(), 2);
        assert_eq!((extents[0].left(), extents[0].height()), (0, 2));
        assert_eq!((extents[1].left(), extents[1].height()), (4, 1));
        assert_eq!(extents[0].span(2), 4);
        assert_eq!(extents[1].span(2), 2);
    }

    #[test]
    fn no_meta_by_default_and_with_meta_round_trips() {
        let sealed = Seal::new(1, 2, vec![(0, vec![vec![0xBB; 32]])]).expect("well-formed");
        assert_eq!(sealed.meta(), None);
        let payload: Vec<u8> = (0u8..=255).collect();
        let with = sealed.with_meta(Meta::new(payload.clone()));
        assert_eq!(with.meta().map(Meta::as_bytes), Some(payload.as_slice()));
    }
}
