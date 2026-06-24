//! `pmt` — compatibility facade over the re-layered `spine` + `epoch` crates.
//!
//! The kernel was split into two crates: the structural **Merkle Spine**
//! ([`spine`]) and the **`epoch` combinator** ([`epoch`]). The spine owns
//! canonicalization, the proof spine, inclusion/leaf proofs, and the general
//! structural [`spine::Seal`]; the combinator owns the activation timeline, the
//! null-run-extents, the binding root, coupling, and the [`epoch::BoundSnapshot`]
//! wrapper over the seal.
//!
//! This crate is a thin **facade** that re-exports the spine surface verbatim and
//! reconstructs the pre-split combined `Sealed` API (structural facet plus epoch
//! facet on one type) so existing consumers keep compiling while they are
//! re-pointed at `spine` / `epoch` directly. It is transitional and carries no
//! logic of its own beyond the delegating shim below.

// Structural surface — re-exported verbatim from the spine.
// Epoch surface — re-exported verbatim from the combinator.
pub use epoch::{
    AuditPayload, BindingProof, CouplingProof, NullRun, TrustedBindingRoot, VerifierConfig,
    all_null_runs, combined_root, committed_active_algs, committed_active_at,
    null_runs_are_trivial, null_runs_for_alg, serialize_null_runs, validate_committed_epochs,
    verify_inactivity_with_coupling, verify_inclusion_with_coupling,
};
pub use spine::{
    ARITY_RANGE, Hasher, InclusionProof, LeafProof, Meta, ProofStep, RunExtent, SkeletonStep,
    Subtree, constant_time_eq, count_leaves, evaluate, fold_frontier, frontier_for_size,
    inclusion_skeleton, nary_mr, null_digest, reconstruct_inclusion_root, verify_inclusion,
    verify_inclusion_path_structure, within_subtree_path,
};
// Module re-exports preserved for `pmt::mr::…`, `pmt::topology::…`, etc.
pub use spine::{hasher, mr, proof, subtree, topology};

/// The pre-split kernel error type, preserved so consumers that match its
/// variants stay exhaustive. Maps from the structural [`spine::Error`] and the
/// combinator [`epoch::Error`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
    /// The spine arity is outside the valid range `2..=256`.
    BadArity,
    /// A frontier was sealed with a malformed committed epoch timeline.
    MalformedEpochs,
    /// A frontier was sealed with a peak count that does not match the canonical
    /// frontier geometry.
    MalformedFrontier,
    /// No hasher was supplied for an algorithm active at the sealed size.
    MissingHasher {
        /// The active algorithm whose hasher was absent from the supplied set.
        alg_id: u64,
    },
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::BadArity => write!(f, "spine arity is outside the valid range 2..=256"),
            Self::MalformedEpochs => write!(
                f,
                "committed epoch timeline is not well-formed at the sealed tree size"
            ),
            Self::MalformedFrontier => write!(
                f,
                "frontier peak count does not match the canonical geometry for the sealed \
                 (tree_size, arity)"
            ),
            Self::MissingHasher { alg_id } => write!(
                f,
                "no hasher supplied for algorithm {alg_id}, which is active at the sealed size"
            ),
        }
    }
}

impl std::error::Error for Error {}

impl From<spine::Error> for Error {
    fn from(e: spine::Error) -> Self {
        match e {
            spine::Error::BadArity => Self::BadArity,
            spine::Error::MalformedFrontier => Self::MalformedFrontier,
            spine::Error::MissingHasher { alg_id } => Self::MissingHasher { alg_id },
        }
    }
}

impl From<epoch::Error> for Error {
    fn from(e: epoch::Error) -> Self {
        match e {
            epoch::Error::MalformedEpochs => Self::MalformedEpochs,
            epoch::Error::Spine(s) => s.into(),
        }
    }
}

/// A specialized `Result` alias matching the pre-split kernel.
pub type Result<T> = std::result::Result<T, Error>;

/// The pre-split combined commitment: the structural [`spine::Seal`] plus the
/// epoch facet, on one type.
///
/// Delegates the structural views to the seal and the epoch views to the
/// [`epoch::BoundSnapshot`] wrapper; the split has moved the logic, this shim
/// only preserves the old call shape.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Sealed(epoch::BoundSnapshot);

impl Sealed {
    /// Seal a resumable frontier at `tree_size` with its committed timeline.
    ///
    /// # Errors
    ///
    /// Returns [`Error::BadArity`], [`Error::MalformedFrontier`], or
    /// [`Error::MalformedEpochs`] for an ill-formed arity, frontier, or timeline.
    pub fn new(
        tree_size: u64,
        arity: u64,
        frontiers: Vec<(u64, Vec<Vec<u8>>)>,
        alg_epochs: Vec<(u64, Vec<(u64, u64)>)>,
    ) -> Result<Self> {
        let seal = spine::Seal::new(tree_size, arity, frontiers)?;
        Ok(Self(epoch::BoundSnapshot::new(seal, alg_epochs)?))
    }

    /// Attach an opaque metadata payload, consuming and returning `self`.
    #[must_use]
    pub fn with_meta(self, meta: Meta) -> Self {
        let alg_epochs = self.0.alg_epochs().to_vec();
        let seal = self.0.seal().clone().with_meta(meta);
        // The timeline already validated at construction, so re-binding cannot fail.
        Self(epoch::BoundSnapshot::new(seal, alg_epochs).expect("timeline already validated"))
    }

    /// The tree size this frontier was sealed at.
    #[must_use]
    pub fn tree_size(&self) -> u64 {
        self.0.seal().tree_size()
    }

    /// The spine arity `k` this frontier was sealed under.
    #[must_use]
    pub fn arity(&self) -> u64 {
        self.0.seal().arity()
    }

    /// A read borrow of each active algorithm's frontier peaks.
    #[must_use]
    pub fn frontiers(&self) -> &[(u64, Vec<Vec<u8>>)] {
        self.0.seal().frontiers()
    }

    /// The frontier peaks of a single algorithm, if active at the sealed size.
    #[must_use]
    pub fn peaks(&self, alg_id: u64) -> Option<&[Vec<u8>]> {
        self.0.seal().peaks(alg_id)
    }

    /// A read borrow of the sealed committed epoch timeline.
    #[must_use]
    pub fn alg_epochs(&self) -> &[(u64, Vec<(u64, u64)>)] {
        self.0.alg_epochs()
    }

    /// A read borrow of the attached opaque metadata, if any.
    #[must_use]
    pub fn meta(&self) -> Option<&Meta> {
        self.0.seal().meta()
    }

    /// **Derived view.** Each active algorithm's member root.
    #[must_use]
    pub fn member_roots(&self, hashers: &[(u64, &dyn Hasher)]) -> Vec<(u64, Vec<u8>)> {
        self.0.seal().member_roots(hashers)
    }

    /// **Derived view.** A single algorithm's member root.
    #[must_use]
    pub fn member_root(&self, alg_id: u64, hasher: &dyn Hasher) -> Option<Vec<u8>> {
        self.0.seal().member_root(alg_id, hasher)
    }

    /// **Derived view.** Every active algorithm's member root, erroring on a
    /// missing hasher.
    ///
    /// # Errors
    ///
    /// Returns [`Error::MissingHasher`] (naming the algorithm) if any active
    /// algorithm has no hasher in `hashers`.
    pub fn all_member_roots(&self, hashers: &[(u64, &dyn Hasher)]) -> Result<Vec<(u64, Vec<u8>)>> {
        self.0.seal().all_member_roots(hashers).map_err(Into::into)
    }

    /// **Derived view.** Each active algorithm's binding root.
    ///
    /// # Errors
    ///
    /// Returns [`Error::MissingHasher`] (naming the algorithm) if any active
    /// algorithm has no hasher in `hashers`.
    pub fn binding_roots(&self, hashers: &[(u64, &dyn Hasher)]) -> Result<Vec<(u64, Vec<u8>)>> {
        self.0.binding_roots(hashers).map_err(Into::into)
    }

    /// **Derived view.** A single algorithm's binding root under `hasher`.
    ///
    /// # Errors
    ///
    /// Returns [`Error::MissingHasher`] (naming the algorithm) if any active
    /// algorithm — including `alg_id` — has no hasher in `all_hashers`.
    pub fn binding_root(
        &self,
        alg_id: u64,
        hasher: &dyn Hasher,
        all_hashers: &[(u64, &dyn Hasher)],
    ) -> Result<Option<Vec<u8>>> {
        self.0
            .binding_root(alg_id, hasher, all_hashers)
            .map_err(Into::into)
    }

    /// **Derived view.** The committed canonicalization run-extents.
    #[must_use]
    pub fn run_extents(&self) -> Vec<RunExtent> {
        self.0.seal().run_extents()
    }
}
