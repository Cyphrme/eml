//! `epoch(cmt)` — the epoch combinator over the Canonical Mutable Tree.
//!
//! [`EpochTree`] lifts a single-algorithm [`cmt::Cmt`] across **N algorithms**
//! and adds the **epoch facet** the structural tree deliberately omits (D13): the
//! committed activation timeline and the **binding / combined root** over the
//! per-algorithm member roots. The CMT owns the structure — `set`/`get`,
//! inclusion, the per-node multi-hash materialization, and the structural
//! [`cmt::Cmt::seal`] into a [`spine::Seal`]; this combinator owns only the
//! cross-tree binding.
//!
//! A mutable tree is **dense and active from genesis**: it has no epoch
//! lifecycle of its own, so the only committed timeline it can assert is the
//! trivial open epoch `(0, MAX)` per registered algorithm. With that trivial
//! activation no algorithm has a null run, so the binding root's coverage child
//! is absent and the [`combined_root`](EpochTree::combined_root) is the plain
//! canonicalization fold over the member roots (genesis promotion native: a lone
//! algorithm folds to its own member root). The same trivial timeline pairs with
//! the structural `Seal` to form the one commitment currency [`Sealed`].

// The mutable tree's structural construction/mutation types, re-exported so an
// instantiation (e.g. `cyphr-tree`) names them through `epoch` alongside
// [`EpochTree`]. Aliased to avoid colliding with the combinator's own
// `Error`/`Result` (the timeline/binding errors).
use cmt::{Cmt, Config, Hasher, ProofStep};
pub use cmt::{Config as CmtConfig, Error as CmtError, Result as CmtResult};
use spine::Seal;

use crate::Sealed;
use crate::root::combined_root;

/// The trivial open epoch a mutable tree asserts for every registered algorithm:
/// active from genesis, never closed.
const OPEN_EPOCH: (u64, u64) = (0, u64::MAX);

/// The epoch combinator over a [`Cmt`] — the Epoch Merkle Tree (`epoch(cmt)`).
///
/// Wraps a structural [`Cmt`] and adds the binding/combined root and the
/// combined-currency seal. The structural surface (`set`, `get`, inclusion, the
/// per-node multi-hash) delegates to the inner tree; the binding facet is this
/// type's own.
#[derive(Debug)]
pub struct EpochTree {
    inner: Cmt,
}

impl EpochTree {
    /// Create an empty epoch tree.
    ///
    /// # Errors
    ///
    /// Propagates [`cmt::Error::InvalidArity`] if `config.arity` is out of range.
    pub fn new(config: Config) -> cmt::Result<Self> {
        Ok(Self {
            inner: Cmt::new(config)?,
        })
    }

    /// Register an algorithm, hashing every existing cell under it
    /// ([`Cmt::register_algorithm`]).
    ///
    /// # Errors
    ///
    /// Propagates [`cmt::Error::DuplicateAlgorithm`].
    pub fn register_algorithm(&mut self, alg_id: u64, hasher: Box<dyn Hasher>) -> cmt::Result<()> {
        self.inner.register_algorithm(alg_id, hasher)
    }

    /// Add `alg_id` to a single cell after the fact ([`Cmt::add_algorithm_at`]),
    /// recomputing only that cell's ancestor path (`O(log n)`).
    ///
    /// # Errors
    ///
    /// Propagates [`cmt::Error::DuplicateAlgorithm`] / [`cmt::Error::IndexGap`].
    pub fn add_algorithm_at(
        &mut self,
        alg_id: u64,
        index: u64,
        hasher: Box<dyn Hasher>,
    ) -> cmt::Result<usize> {
        self.inner.add_algorithm_at(alg_id, index, hasher)
    }

    /// Set the payload (and opaque metadata) of cell `index`
    /// ([`Cmt::set`]).
    ///
    /// # Errors
    ///
    /// Propagates [`cmt::Error::IndexGap`].
    pub fn set(&mut self, index: u64, payload: Vec<u8>, metadata: Vec<u8>) -> cmt::Result<()> {
        self.inner.set(index, payload, metadata)
    }

    /// Read the payload of cell `index`.
    #[must_use]
    pub fn get(&self, index: u64) -> Option<&[u8]> {
        self.inner.get(index)
    }

    /// Read the opaque metadata of cell `index`.
    #[must_use]
    pub fn metadata(&self, index: u64) -> Option<&[u8]> {
        self.inner.metadata(index)
    }

    /// Number of cells in the tree.
    #[must_use]
    pub fn len(&self) -> u64 {
        self.inner.len()
    }

    /// Whether the tree holds no cells.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// The configured proof-spine arity.
    #[must_use]
    pub fn arity(&self) -> u64 {
        self.inner.arity()
    }

    /// The current per-algorithm **member root** under `alg_id` — the raw root
    /// the leaves authenticate against ([`Cmt::root`]).
    #[must_use]
    pub fn root(&self, alg_id: u64) -> Option<Vec<u8>> {
        self.inner.root(alg_id)
    }

    /// The current live **combined root** under `alg_id`'s hash — the primary
    /// identity of the tree, the epoch facet over the structural member roots.
    ///
    /// The combined root is the canonicalization fold ([`combined_root`]) over
    /// every registered algorithm's member root as children, under `alg_id`'s own
    /// hash. A mutable tree is dense and active from genesis, so its committed
    /// timeline is trivial and no coverage child joins the fold; genesis
    /// promotion is native, so for the common one-algorithm tree the combined
    /// root equals [`Self::root`].
    ///
    /// Computed live from the inner tree's materialized member roots — no seal
    /// required — and symmetric with the append-only log's combined root.
    /// Returns `None` if `alg_id` is unregistered or the tree is empty.
    #[must_use]
    pub fn combined_root(&self, alg_id: u64) -> Option<Vec<u8>> {
        let hasher = self.inner.hasher(alg_id)?;
        // Empty tree (or unregistered alg) has no member root, hence no combined root.
        self.inner.root(alg_id)?;
        let member_roots = self.inner.member_roots();
        // Trivial open epoch per algorithm: dense, active from genesis. No null
        // run, so no coverage child joins the fold whatever the size or arity.
        let alg_epochs: Vec<(u64, Vec<(u64, u64)>)> = member_roots
            .iter()
            .map(|&(id, _)| (id, vec![OPEN_EPOCH]))
            .collect();
        Some(combined_root(
            hasher,
            &member_roots,
            &alg_epochs,
            self.len(),
            self.arity(),
        ))
    }

    /// Generate an inclusion proof for cell `index` under `alg_id`
    /// ([`Cmt::inclusion_proof`]).
    #[must_use]
    pub fn inclusion_proof(&self, alg_id: u64, index: u64) -> Option<(Vec<u8>, Vec<ProofStep>)> {
        self.inner.inclusion_proof(alg_id, index)
    }

    /// Produce a self-contained [`spine::LeafProof`] for cell `index`
    /// ([`Cmt::leaf_proof`]).
    #[must_use]
    pub fn leaf_proof(&self, alg_id: u64, index: u64) -> Option<spine::LeafProof> {
        self.inner.leaf_proof(alg_id, index)
    }

    /// Generate a non-membership proof for `index` under `alg_id`
    /// ([`Cmt::non_membership_proof`]).
    #[must_use]
    pub fn non_membership_proof(
        &self,
        alg_id: u64,
        index: u64,
    ) -> Option<(Vec<u8>, Vec<ProofStep>)> {
        self.inner.non_membership_proof(alg_id, index)
    }

    /// Consume the tree and seal it into the one commitment currency [`Sealed`].
    ///
    /// The inner [`Cmt`] computes the structural [`Seal`] (the resumable
    /// frontier); this combinator pairs it with the trivial committed timeline
    /// `(0, MAX)` per registered algorithm — the only timeline a mutable tree can
    /// assert — to form the `Sealed` (the [`BoundSnapshot`](crate::BoundSnapshot)
    /// epoch facet over the structural seal, D13). One-way: there is no `unseal`
    /// and no path back to an `EpochTree` (C-SEAL-ONEWAY).
    ///
    /// # Errors
    ///
    /// Propagates [`cmt::Error::EmptySeal`] on an empty tree and
    /// [`cmt::Error::MalformedSeal`] if the spine rejects the frontier; the
    /// combined currency cannot itself fail once the structural seal succeeds, so
    /// a `Sealed` build error is mapped back to `MalformedSeal`.
    pub fn seal(self) -> cmt::Result<Sealed> {
        let seal: Seal = self.inner.seal()?;
        // The trivial open epoch for every algorithm carried in the structural
        // seal — sorted by algorithm ID, as the seal's frontiers already are.
        let alg_epochs: Vec<(u64, Vec<(u64, u64)>)> = seal
            .frontiers()
            .iter()
            .map(|(id, _)| (*id, vec![OPEN_EPOCH]))
            .collect();
        Sealed::new(
            seal.tree_size(),
            seal.arity(),
            seal.frontiers().to_vec(),
            alg_epochs,
        )
        .map_err(|_| cmt::Error::MalformedSeal)
    }
}
