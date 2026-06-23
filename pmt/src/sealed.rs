//! `Sealed` — the one kernel commitment currency.
//!
//! Every freeze of a tree — mutable ([`emt`](../../emt/index.html)) or
//! append-only ([`eml`](../../eml_log/index.html)) — produces a `Sealed`. There
//! is exactly one commitment type, and it carries the **resumable frontier**:
//! per active algorithm, the digests of the perfect k-ary subtrees that
//! [`frontier_for_size`](crate::topology::frontier_for_size) names at the sealed
//! size (the "peaks", in MMR terms). The frontier is the complete continuation
//! state of an append-only log, so an EML can be *resumed* from any `Sealed`
//! regardless of which kind sealed it.
//!
//! # One commitment, three views
//!
//! The frontier is the stored content; everything else a consumer asks of a
//! `Sealed` is a **derived view**, computed on demand and never stored
//! (D12 / KU11 — this metadata is provably derivable from the tree, not a
//! parallel committed channel):
//!
//! - each algorithm's **member root** is the fold of its frontier peaks ([`Sealed::member_root`]) —
//!   the raw per-algorithm root the leaves authenticate against;
//! - each algorithm's **binding root** is the promotion-aware combined root over the member roots
//!   and the committed timeline ([`Sealed::binding_root`]) — the head the structure authenticates
//!   against;
//! - the **canonicalization run-extents** are the height `>= 1` frontier nodes, derived from
//!   `(tree_size, arity)` alone ([`Sealed::run_extents`]).
//!
//! Member and binding roots are folds, so they need the algorithm's own hasher;
//! the run-extents are pure geometry and need nothing.
//!
//! # One-way
//!
//! `Sealed` makes the seal **one-way**: its fields are private, the only ingress
//! is [`Sealed::new`] (which validates the committed timeline), and the only
//! egress is a read borrow or a derived view. There is no `unseal` and no
//! field-level mutator, so a value cannot be walked back to the construction it
//! came from (C-SEAL-ONEWAY).
//!
//! # Metadata channel
//!
//! `Sealed` carries an optional [`crate::Meta`] — an opaque, arbitrary byte
//! payload the library never interprets (an out-of-band tree-head attestation
//! may ride here). It is set via [`Sealed::with_meta`] and read via
//! [`Sealed::meta`]. The channel is additive: a `Sealed` without metadata
//! behaves identically to one with `None`.

use crate::error::{Error, Result};
use crate::hasher::Hasher;
use crate::metadata::Meta;
use crate::mr::nary_mr;
use crate::proof::{combined_root_preimage, validate_committed_epochs};
use crate::topology::{ARITY_RANGE, fold_frontier, frontier_for_size};

/// One committed canonicalization run-extent: a contiguous collapse of
/// `arity^height` consecutive leaves into a single subtree, beginning at leaf
/// index `left`.
///
/// A run-extent is emitted only for a *collapse* — a frontier node above leaf
/// level (`height >= 1`). A promoted singleton leaf (`height == 0`) is
/// structurally deterministic and commits no run-extent (INV-AUTH-BOUNDARY:
/// promotion commits nothing, collapse commits its minimal run-extent), so it
/// never appears here.
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

/// The one kernel commitment currency: a sealed, resumable frontier.
///
/// Carries, per algorithm active at `tree_size`, the digests of the perfect
/// k-ary subtrees of the frontier (the resume state), the committed epoch
/// timeline, and an optional opaque metadata channel ([`Meta`]). Member roots,
/// binding roots, and run-extents are *derived views* — see the module docs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Sealed {
    /// Tree size at which this frontier was sealed.
    tree_size: u64,
    /// Arity `k` (`2..=256`) the frontier was sealed under; fixes the frontier
    /// geometry every derived view reads.
    arity: u64,
    /// Per active-algorithm frontier peaks: `(alg_id, peaks)`, sorted by
    /// algorithm ID. `peaks` are the digests of the perfect k-ary subtrees
    /// named by [`frontier_for_size`]`(tree_size, arity)`, left to right — the
    /// complete continuation state for an append-only resume. The member root
    /// is their fold.
    frontiers: Vec<(u64, Vec<Vec<u8>>)>,
    /// Committed epoch timeline of every registered algorithm at the sealed
    /// size, sorted by algorithm ID.
    alg_epochs: Vec<(u64, Vec<(u64, u64)>)>,
    /// Opaque metadata channel; library never inspects the contents.
    meta: Option<Meta>,
}

impl Sealed {
    /// Seal a resumable frontier at `tree_size` with no metadata attached.
    ///
    /// `arity` is the spine arity `k` (`2..=256`); `frontiers` carries each
    /// active algorithm's frontier peaks (the digests of the perfect k-ary
    /// subtrees of the frontier, left to right), sorted by algorithm ID;
    /// `alg_epochs` is the committed timeline.
    ///
    /// The committed timeline must be well-formed at `tree_size`
    /// ([`validate_committed_epochs`]); otherwise this returns
    /// [`Error::MalformedEpochs`]. This is the only way to construct a
    /// `Sealed`, so every value in circulation carries a validated timeline
    /// and a correctly-sized frontier.
    ///
    /// # Errors
    ///
    /// Returns [`Error::BadArity`] if `arity` is outside `2..=256`. Returns
    /// [`Error::MalformedEpochs`] if the committed timeline is ill-formed at
    /// `tree_size`, or if any algorithm's peak count does not match the
    /// canonical frontier length for `(tree_size, arity)`.
    pub fn new(
        tree_size: u64,
        arity: u64,
        frontiers: Vec<(u64, Vec<Vec<u8>>)>,
        alg_epochs: Vec<(u64, Vec<(u64, u64)>)>,
    ) -> Result<Self> {
        if !ARITY_RANGE.contains(&arity) {
            return Err(Error::BadArity);
        }
        if !validate_committed_epochs(&alg_epochs, tree_size) {
            return Err(Error::MalformedEpochs);
        }
        // Cross-check that every algorithm's peak count matches the canonical
        // frontier geometry for (tree_size, arity). A mismatched count means
        // a caller constructed Sealed with a wrong or truncated peaks slice —
        // a malformed frontier that member_root would silently fold incorrectly.
        let expected_peak_count = frontier_for_size(tree_size, arity).len();
        for (_, peaks) in &frontiers {
            if peaks.len() != expected_peak_count {
                return Err(Error::MalformedEpochs);
            }
        }
        Ok(Self {
            tree_size,
            arity,
            frontiers,
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

    /// The spine arity `k` this frontier was sealed under.
    #[must_use]
    pub fn arity(&self) -> u64 {
        self.arity
    }

    /// A read borrow of each active algorithm's frontier peaks: `(alg_id,
    /// peaks)`, sorted by algorithm ID. These are the resume state; the member
    /// root is their fold ([`Self::member_root`]).
    #[must_use]
    pub fn frontiers(&self) -> &[(u64, Vec<Vec<u8>>)] {
        &self.frontiers
    }

    /// The frontier peaks of a single algorithm, if it was active at the sealed
    /// size.
    #[must_use]
    pub fn peaks(&self, alg_id: u64) -> Option<&[Vec<u8>]> {
        self.frontiers
            .iter()
            .find(|(id, _)| *id == alg_id)
            .map(|(_, p)| p.as_slice())
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

    // --- derived views -------------------------------------------------------

    /// **Derived view.** Each active algorithm's member root: `(alg_id,
    /// member_root)`, sorted by algorithm ID. A member root is the fold of that
    /// algorithm's frontier peaks under its own hash — the raw per-algorithm
    /// root the leaves authenticate against. Folded on demand, never stored.
    ///
    /// `hashers` resolves an algorithm's own hash; an algorithm with no hasher
    /// in `hashers` is skipped (its member root cannot be folded).
    #[must_use]
    pub fn member_roots(&self, hashers: &[(u64, &dyn Hasher)]) -> Vec<(u64, Vec<u8>)> {
        self.frontiers
            .iter()
            .filter_map(|(id, peaks)| {
                let hasher = hashers.iter().find(|(hid, _)| hid == id).map(|(_, h)| *h)?;
                Some((*id, fold_peaks(hasher, peaks, self.arity)))
            })
            .collect()
    }

    /// **Derived view.** A single algorithm's member root — the fold of its
    /// frontier peaks under `hasher`. Returns `None` if the algorithm was not
    /// active at the sealed size.
    #[must_use]
    pub fn member_root(&self, alg_id: u64, hasher: &dyn Hasher) -> Option<Vec<u8>> {
        let peaks = self.peaks(alg_id)?;
        Some(fold_peaks(hasher, peaks, self.arity))
    }

    /// **Derived view.** Each active algorithm's binding root: `(alg_id,
    /// binding_root)`, sorted by algorithm ID. A binding root is the
    /// promotion-aware combined root over the member roots and the committed
    /// timeline, under that algorithm's own hash — the head the rest of the
    /// structure authenticates against. Computed on demand, never stored.
    ///
    /// The genesis-promotion rule mirrors the log's live combined root: a
    /// registry-singleton with the forced default timeline `[(0, MAX)]` binds
    /// to the *raw* member root; any lifecycle event switches permanently to
    /// the hashed form (see
    /// [`combined_root_at`](../../eml_log/tree/struct.NaryMerkleLog.html#method.combined_root_at)).
    ///
    /// `hashers` resolves each algorithm's own hash; an algorithm with no hasher
    /// is skipped.
    #[must_use]
    pub fn binding_roots(&self, hashers: &[(u64, &dyn Hasher)]) -> Vec<(u64, Vec<u8>)> {
        let members = self.member_roots(hashers);
        let promoted = self.is_promoted_registry();
        members
            .iter()
            .filter_map(|(id, member_root)| {
                let hasher = hashers.iter().find(|(hid, _)| hid == id).map(|(_, h)| *h)?;
                let br = if promoted {
                    member_root.clone()
                } else {
                    hasher.hash(&combined_root_preimage(&members, &self.alg_epochs))
                };
                Some((*id, br))
            })
            .collect()
    }

    /// **Derived view.** A single algorithm's binding root under `hasher`.
    /// Returns `None` if the algorithm was not active at the sealed size.
    ///
    /// Promotion-aware; see [`Self::binding_roots`]. The non-promoted form needs
    /// every active algorithm's member root for the combined-root preimage, so
    /// `all_hashers` must resolve them; the single returned binding root is the
    /// one for `alg_id` under `hasher`.
    #[must_use]
    pub fn binding_root(
        &self,
        alg_id: u64,
        hasher: &dyn Hasher,
        all_hashers: &[(u64, &dyn Hasher)],
    ) -> Option<Vec<u8>> {
        let member_root = self.member_root(alg_id, hasher)?;
        if self.is_promoted_registry() {
            return Some(member_root);
        }
        let members = self.member_roots(all_hashers);
        Some(hasher.hash(&combined_root_preimage(&members, &self.alg_epochs)))
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

    /// Whether the committed registry is a single algorithm under the forced
    /// default timeline `[(0, MAX)]` — the genesis-promotion case in which a
    /// binding root promotes to the raw member root.
    fn is_promoted_registry(&self) -> bool {
        self.alg_epochs.len() == 1 && self.alg_epochs[0].1 == vec![(0u64, u64::MAX)]
    }
}

/// Fold a frontier's peaks into the single member root using the shared
/// [`fold_frontier`] combinator — identical to the append-only log's own root
/// fold, so the folded member root matches a from-scratch build over the same
/// data.
fn fold_peaks(hasher: &dyn Hasher, peaks: &[Vec<u8>], k: u64) -> Vec<u8> {
    if peaks.is_empty() {
        return hasher.empty();
    }
    fold_frontier(peaks.to_vec(), k as usize, |chunk| {
        let refs: Vec<&[u8]> = chunk.iter().map(|v| v.as_slice()).collect();
        nary_mr(hasher, &refs)
    })
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

    #[test]
    fn new_rejects_malformed_timeline() {
        // Open epoch starting past the sealed size is ill-formed.
        let err = Sealed::new(
            3,
            2,
            vec![(0, vec![vec![0xAA; 32]])],
            vec![(0, vec![(5, u64::MAX)])],
        );
        assert_eq!(err, Err(Error::MalformedEpochs));
    }

    #[test]
    fn new_rejects_out_of_range_arity() {
        assert_eq!(
            Sealed::new(
                1,
                1,
                vec![(0, vec![vec![0xAA; 32]])],
                vec![(0, vec![(0, u64::MAX)])]
            ),
            Err(Error::BadArity)
        );
        assert_eq!(
            Sealed::new(
                1,
                257,
                vec![(0, vec![vec![0xAA; 32]])],
                vec![(0, vec![(0, u64::MAX)])]
            ),
            Err(Error::BadArity)
        );
    }

    #[test]
    fn new_rejects_mismatched_peak_count() {
        // Size 3, k=2 → frontier = [(0,1),(2,0)] → 2 peaks expected.
        // Supplying 1 peak is malformed.
        assert_eq!(
            Sealed::new(
                3,
                2,
                vec![(0, vec![vec![0xAA; 32]])],
                vec![(0, vec![(0, u64::MAX)])]
            ),
            Err(Error::MalformedEpochs)
        );
        // Supplying 3 peaks is also malformed.
        assert_eq!(
            Sealed::new(
                3,
                2,
                vec![(0, vec![vec![0xAA; 32], vec![0xBB; 32], vec![0xCC; 32]])],
                vec![(0, vec![(0, u64::MAX)])]
            ),
            Err(Error::MalformedEpochs)
        );
    }

    #[test]
    fn new_accepts_well_formed_and_reads_back() {
        let sealed = Sealed::new(
            1,
            2,
            vec![(0, vec![vec![0xAA; 32]])],
            vec![(0, vec![(0, u64::MAX)])],
        )
        .expect("well-formed");
        assert_eq!(sealed.tree_size(), 1);
        assert_eq!(sealed.arity(), 2);
        assert_eq!(sealed.peaks(0), Some([vec![0xAA; 32]].as_slice()));
        assert_eq!(sealed.alg_epochs(), &[(0, vec![(0, u64::MAX)])]);
    }

    #[test]
    fn member_root_folds_a_single_peak_to_itself() {
        // A single frontier peak is the member root (promotion).
        let peak = vec![0xCD; 32];
        let sealed = Sealed::new(
            1,
            2,
            vec![(0, vec![peak.clone()])],
            vec![(0, vec![(0, u64::MAX)])],
        )
        .expect("well-formed");
        assert_eq!(sealed.member_root(0, &H), Some(peak));
    }

    #[test]
    fn member_root_folds_two_peaks_with_the_hasher() {
        // Two peaks fold to nary_mr(hasher, [p0, p1]).
        let p0 = vec![0x01; 32];
        let p1 = vec![0x02; 32];
        let expected = nary_mr(&H, &[p0.as_slice(), p1.as_slice()]);
        let sealed = Sealed::new(
            3,
            2,
            vec![(0, vec![p0.clone(), p1.clone()])],
            vec![(0, vec![(0, u64::MAX)])],
        )
        .expect("well-formed");
        assert_eq!(sealed.member_root(0, &H), Some(expected));
    }

    #[test]
    fn promoted_registry_binding_root_equals_member_root() {
        let p0 = vec![0x11; 32];
        let p1 = vec![0x22; 32];
        let sealed = Sealed::new(
            3,
            2,
            vec![(0, vec![p0.clone(), p1.clone()])],
            vec![(0, vec![(0, u64::MAX)])],
        )
        .expect("well-formed");
        let member = sealed.member_root(0, &H).unwrap();
        let hashers: [(u64, &dyn Hasher); 1] = [(0, &H)];
        assert_eq!(sealed.binding_root(0, &H, &hashers), Some(member.clone()));
        assert_eq!(sealed.binding_roots(&hashers), vec![(0, member)]);
    }

    #[test]
    fn run_extents_are_the_collapse_frontier_geometry() {
        // Size 7, k=2: frontier = [(0,2),(4,1),(6,0)]; the height-0 entry is a
        // promotion and is omitted.
        let sealed = Sealed::new(
            7,
            2,
            vec![(0, vec![vec![0xAA; 32], vec![0xBB; 32], vec![0xCC; 32]])],
            vec![(0, vec![(0, u64::MAX)])],
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
        let sealed = Sealed::new(
            1,
            2,
            vec![(0, vec![vec![0xBB; 32]])],
            vec![(0, vec![(0, u64::MAX)])],
        )
        .expect("well-formed");
        assert_eq!(sealed.meta(), None);
        let payload: Vec<u8> = (0u8..=255).collect();
        let with = sealed.with_meta(Meta::new(payload.clone()));
        assert_eq!(with.meta().map(Meta::as_bytes), Some(payload.as_slice()));
    }
}
