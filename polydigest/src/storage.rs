//! Storage abstraction for leaf and node persistence.
//!
//! THE CONTRACT (head's ruling, 2026-09-17): a log's kind (flat vs. subtree)
//! is never persisted -- it is derived from content (a store with any leaf
//! holds a flat log; a store with a nonzero append count and no leaves holds
//! a subtree log; a store at count 0 has no kind, since either append is
//! still legal). Log metadata is therefore just the append count, always
//! present (never `Option`) and `0` for a fresh store. And every mutation is
//! one of five fixed shapes -- append a leaf, append a subtree, add an
//! algorithm, remove (freeze) an algorithm, resume (reactivate) an algorithm
//! -- passed through the one mutating entry point, [`Storage::apply`], as a
//! [`WriteOp`]. There is exactly one way to write: no standalone
//! `store_leaf`/`store_node`/`store_algorithm_meta`, no five-parameter
//! `write_batch` where most parameters are usually empty. Illegal
//! combinations (a leaf write with no data, an algorithm removal with a node
//! list) are unrepresentable rather than merely unused.
//!
//! [`WriteOp::SeedFrontier`] is a sixth shape, added beyond the ruling's five:
//! [`crate::tree::NaryMerkleLog::resume`] seeds a genesis frontier for
//! potentially several algorithms at once, atomically, at a caller-chosen
//! size -- a capability none of the five per-algorithm operations on an
//! already-running log provide (the five are exactly `NaryMerkleLog`'s five
//! *mutating methods*; `resume` is a *constructor*, building a log's initial
//! state before any method runs). Modelling it as N independent
//! `ResumeAlgorithm`-shaped calls would drop the atomicity a crash-safe
//! genesis write needs across algorithms; modelling it as N `AddAlgorithm`
//! calls cannot express the inherited frontier nodes or checkpoint roots at
//! all. `SeedFrontier` is the smallest addition that keeps the invariant
//! "one op, one atomic write" without smuggling optionality back into the
//! other five.
//!
//! Field-name collisions are handled by small named structs
//! ([`NodeWrite`], [`AlgorithmRoot`], [`AlgorithmSeed`]) instead of
//! positional tuples: `(u64, u64, u32, &[u8])` lets a caller transpose an
//! algorithm id and a left coordinate (both `u64`) with no compiler
//! complaint; a struct with named fields does not.

use std::collections::HashMap;

/// Epoch metadata for a registered algorithm: a sequence of half-open `[start, end)` intervals.
pub type Epochs = Vec<(u64, u64)>;

/// Reconstructed metadata for registered algorithms: a list of `(alg_id, epochs)` pairs.
pub type AlgorithmMetas = Vec<(u64, Epochs)>;

/// One sealed internal node digest to persist, at its `(alg_id, left,
/// height)` coordinate. A named struct rather than a `(u64, u64, u32, &[u8])`
/// tuple so `alg_id` and `left` -- both `u64` -- cannot be transposed at a
/// call site with no compiler complaint.
#[derive(Debug, Clone, Copy)]
pub struct NodeWrite<'a> {
    /// The algorithm this node belongs to.
    pub alg_id: u64,
    /// The coordinate's left bound (leaf index at height 0).
    pub left: u64,
    /// The coordinate's height (0 = leaf level).
    pub height: u32,
    /// The node's digest.
    pub hash: &'a [u8],
}

/// One algorithm's checkpoint root, as part of a batch spanning several
/// active algorithms.
#[derive(Debug, Clone, Copy)]
pub struct AlgorithmRoot<'a> {
    /// The algorithm this root belongs to.
    pub alg_id: u64,
    /// The root hash at the current tip.
    pub root: &'a [u8],
}

/// One algorithm's inherited genesis state, as part of a
/// [`WriteOp::SeedFrontier`] batch: its epoch history so far (carried from
/// the sealed source), the frontier peaks [`crate::tree::NaryMerkleLog::resume`]
/// materializes as nodes, and the checkpoint root folded from that frontier.
#[derive(Debug, Clone, Copy)]
pub struct AlgorithmSeed<'a> {
    /// The algorithm being seeded.
    pub alg_id: u64,
    /// The algorithm's epoch history as of the seal.
    pub epochs: &'a [(u64, u64)],
    /// The frontier peaks to materialize as nodes (active ranges only).
    pub nodes: &'a [NodeWrite<'a>],
    /// The checkpoint root folded from the seeded frontier. Named distinctly
    /// from [`AppendLeaf`](WriteOp::AppendLeaf)/[`AppendSubtree`](WriteOp::AppendSubtree)'s
    /// plural `checkpoint_roots` so the two cannot be typo'd into each other
    /// at a call site.
    pub seeded_root: &'a [u8],
}

/// One atomic storage mutation. Every field on every variant is always
/// meaningful for that variant -- there is no optional field a caller must
/// remember to leave empty, and no combination [`Storage::apply`] must
/// reject at run time because the type system already refused to construct
/// it.
#[derive(Debug, Clone, Copy)]
pub enum WriteOp<'a> {
    /// Append a raw leaf payload at log position `at`, together with any
    /// active algorithm's leaf-hash node and refreshed checkpoint root.
    AppendLeaf {
        /// The append-only position being written (== the count before this op).
        at: u64,
        /// The raw leaf payload.
        data: &'a [u8],
        /// Per-active-algorithm leaf node(s) produced by this append.
        nodes: &'a [NodeWrite<'a>],
        /// Per-active-algorithm checkpoint root after this append.
        checkpoint_roots: &'a [AlgorithmRoot<'a>],
    },
    /// Append a structured subtree at log position `at`: no leaf payload is
    /// stored, only the per-algorithm subtree-root node(s).
    AppendSubtree {
        /// The append-only position being written (== the count before this op).
        at: u64,
        /// Per-active-algorithm subtree-root node(s) produced by this append.
        nodes: &'a [NodeWrite<'a>],
        /// Per-active-algorithm checkpoint root after this append.
        checkpoint_roots: &'a [AlgorithmRoot<'a>],
    },
    /// Register a new algorithm, active from the current append count.
    AddAlgorithm {
        /// The algorithm being registered.
        alg_id: u64,
        /// Its initial (single, open) epoch.
        epochs: &'a [(u64, u64)],
    },
    /// Freeze (deactivate) an already-registered algorithm.
    RemoveAlgorithm {
        /// The algorithm being frozen.
        alg_id: u64,
        /// Its epoch history with the final epoch now closed.
        epochs: &'a [(u64, u64)],
        /// The checkpoint root at the freeze point. Named distinctly from
        /// the append variants' plural `checkpoint_roots` so the two cannot
        /// be typo'd into each other at a call site.
        frozen_root: &'a [u8],
    },
    /// Reactivate a previously frozen algorithm, replaying its frontier
    /// forward across the gap.
    ResumeAlgorithm {
        /// The algorithm being reactivated.
        alg_id: u64,
        /// Its epoch history with a new open epoch appended.
        epochs: &'a [(u64, u64)],
        /// Any mixed (frozen/live) nodes reconstructed across the gap.
        nodes: &'a [NodeWrite<'a>],
        /// The checkpoint root after reactivation. Named distinctly from
        /// the append variants' plural `checkpoint_roots` so the two cannot
        /// be typo'd into each other at a call site.
        resumed_root: &'a [u8],
    },
    /// Seed one or more algorithms' genesis frontier state atomically, at
    /// caller-chosen size `size` -- [`crate::tree::NaryMerkleLog::resume`]'s
    /// write. Never used by an already-running log's own methods.
    SeedFrontier {
        /// The append count every seeded algorithm starts from -- a
        /// frontier seed moves [`Storage::append_count`] to this value
        /// directly, never additively.
        size: u64,
        /// Each algorithm's inherited frontier state.
        algorithms: &'a [AlgorithmSeed<'a>],
    },
}

/// Backend for persisting and retrieving raw leaf payloads and sealed
/// internal node hashes.
pub trait Storage: Send + Sync {
    /// Error type for storage operations.
    type Error: std::error::Error + Send + Sync + 'static;

    /// Retrieve the raw leaf payload at the given index.
    fn get_leaf(
        &self,
        index: u64,
    ) -> impl std::future::Future<Output = Result<Vec<u8>, Self::Error>> + Send;

    /// The number of leaves currently stored, or an error if storage is
    /// unreadable. Never returns 0 on error; a storage failure must be
    /// propagated so callers can distinguish "empty log" from "broken store".
    ///
    /// This is the leaf count specifically -- `0` for a subtree-kind log
    /// regardless of its append count -- which is exactly the signal a log's
    /// derived kind is read from: a store with `len() > 0` holds a flat log,
    /// a store with `append_count() > 0` and `len() == 0` holds a subtree
    /// log, and a store at `append_count() == 0` has no kind yet.
    fn len(&self) -> impl std::future::Future<Output = Result<u64, Self::Error>> + Send;

    /// Whether the storage contains no leaves.
    fn is_empty(&self) -> impl std::future::Future<Output = Result<bool, Self::Error>> + Send {
        async move { self.len().await.map(|n| n == 0) }
    }

    /// Retrieve a sealed internal node hash.
    fn get_node(
        &self,
        alg_id: u64,
        left: u64,
        height: u32,
    ) -> impl std::future::Future<Output = Result<Option<Vec<u8>>, Self::Error>> + Send;

    /// Load all persisted algorithm metadata.
    fn load_algorithm_metas(
        &self,
    ) -> impl std::future::Future<Output = Result<AlgorithmMetas, Self::Error>> + Send;

    /// The total number of log-level appends committed so far (leaves for a
    /// flat log, subtrees for a subtree log) -- `0` for a fresh store,
    /// always present. A log's kind is never stored; it is derived from this
    /// value together with [`Storage::len`] (see that method's doc comment).
    /// An append moves this count forward by exactly one; a
    /// [`WriteOp::SeedFrontier`] moves it directly to its own `size`
    /// instead; nothing else touches it.
    fn append_count(&self) -> impl std::future::Future<Output = Result<u64, Self::Error>> + Send;

    /// Load per-algorithm checkpoint roots last written by [`Storage::apply`].
    ///
    /// Used by `from_storage` to verify frontier integrity: the root
    /// recomputed from the loaded frontier must match the stored checkpoint.
    /// Returns an empty list for a fresh store.
    fn load_checkpoint_roots(
        &self,
    ) -> impl std::future::Future<Output = Result<Vec<(u64, Vec<u8>)>, Self::Error>> + Send;

    /// Atomically commit one or more [`WriteOp`]s in a single durable
    /// transaction -- the *only* way to mutate a [`Storage`] backend.
    ///
    /// The implementation MUST guarantee all-or-nothing semantics: a crash
    /// between any two ops, or between any two of one op's own component
    /// writes, must leave no partial state.
    ///
    /// The implementation MUST return an error and MUST NOT panic when a
    /// variant's precondition is violated -- an unregistered algorithm
    /// removed, a duplicate registration, or an append whose position is
    /// not the current count.
    fn apply(
        &mut self,
        ops: &[WriteOp<'_>],
    ) -> impl std::future::Future<Output = Result<(), Self::Error>> + Send;
}

/// A borrowed [`Storage`] presented as the CML engine's [`cml::NodeReader`] read
/// substrate, so the combinator can drive N single-algorithm `cml` views over
/// its **one** shared store (D14). The wrapper forwards the two read methods the
/// engine needs; the write surface stays the combinator's concern.
///
/// A local newtype is required because [`cml::NodeReader`] and a generic backend
/// `S` are both foreign to this crate's orphan scope; wrapping the borrow gives
/// the impl a local owner.
pub(crate) struct StorageReader<'a, S: Storage>(pub(crate) &'a S);

impl<S: Storage> cml::NodeReader for StorageReader<'_, S> {
    type Error = S::Error;

    async fn get_node(
        &self,
        alg_id: u64,
        left: u64,
        height: u32,
    ) -> Result<Option<Vec<u8>>, Self::Error> {
        self.0.get_node(alg_id, left, height).await
    }

    async fn get_leaf(&self, index: u64) -> Result<Vec<u8>, Self::Error> {
        self.0.get_leaf(index).await
    }
}

// ============================================================================
// In-memory implementation
// ============================================================================

/// In-memory leaf and node storage backed by collections.
#[derive(Debug, Default, Clone)]
pub struct MemoryStorage {
    /// Raw leaf payloads.
    pub leaves: Vec<Vec<u8>>,
    /// Sealed internal node hashes, keyed by `(alg_id, left, height)`.
    pub nodes: HashMap<(u64, u64, u32), Vec<u8>>,
    /// Algorithm epoch metadata, keyed by algorithm ID.
    pub algorithm_metas: HashMap<u64, Vec<(u64, u64)>>,
    /// The total append count. Never `Option`: `0` for a fresh store.
    pub count: u64,
    /// Per-algorithm checkpoint roots: the root hash at the last append.
    pub checkpoint_roots: HashMap<u64, Vec<u8>>,
}

impl MemoryStorage {
    /// Create a new empty in-memory storage.
    #[must_use]
    pub fn new() -> Self {
        Self {
            leaves: Vec::new(),
            nodes: HashMap::new(),
            algorithm_metas: HashMap::new(),
            count: 0,
            checkpoint_roots: HashMap::new(),
        }
    }
}

/// Error type for [`MemoryStorage`] operations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MemoryStorageError {
    /// The index that was requested.
    pub index: u64,
    /// The number of stored leaves.
    pub stored: u64,
}

impl std::fmt::Display for MemoryStorageError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "leaf index {} not found (storage contains {} leaves)",
            self.index, self.stored
        )
    }
}

impl std::error::Error for MemoryStorageError {}

impl Storage for MemoryStorage {
    type Error = MemoryStorageError;

    async fn get_leaf(&self, index: u64) -> Result<Vec<u8>, Self::Error> {
        self.leaves
            .get(index as usize)
            .cloned()
            .ok_or(MemoryStorageError {
                index,
                stored: self.leaves.len() as u64,
            })
    }

    async fn len(&self) -> Result<u64, Self::Error> {
        Ok(self.leaves.len() as u64)
    }

    async fn get_node(
        &self,
        alg_id: u64,
        left: u64,
        height: u32,
    ) -> Result<Option<Vec<u8>>, Self::Error> {
        Ok(self.nodes.get(&(alg_id, left, height)).cloned())
    }

    async fn load_algorithm_metas(&self) -> Result<AlgorithmMetas, Self::Error> {
        Ok(self
            .algorithm_metas
            .iter()
            .map(|(&id, e)| (id, e.clone()))
            .collect())
    }

    async fn append_count(&self) -> Result<u64, Self::Error> {
        Ok(self.count)
    }

    async fn load_checkpoint_roots(&self) -> Result<Vec<(u64, Vec<u8>)>, Self::Error> {
        Ok(self
            .checkpoint_roots
            .iter()
            .map(|(&id, r)| (id, r.clone()))
            .collect())
    }

    async fn apply(&mut self, _ops: &[WriteOp<'_>]) -> Result<(), Self::Error> {
        // Deliberately unimplemented: the operation-enum write path (head's
        // ruling 2026-09-17) has no landed implementation yet on any
        // backend. Every test exercising a mutation is expected to fail
        // here until an implementer fills this in.
        unimplemented!("MemoryStorage::apply: the operation-enum write path is not implemented yet")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_memory_storage_leaves_read_side() {
        smol::block_on(async {
            let storage = MemoryStorage::new();
            assert!(storage.is_empty().await.unwrap());
            assert_eq!(storage.len().await.unwrap(), 0);
            assert_eq!(storage.append_count().await.unwrap(), 0);

            // Out of bounds retrieval on an empty store.
            assert!(storage.get_leaf(0).await.is_err());
        });
    }

    #[test]
    fn test_memory_storage_nodes_read_side() {
        smol::block_on(async {
            let storage = MemoryStorage::new();
            assert_eq!(storage.get_node(1, 42, 0).await.unwrap(), None);
        });
    }
}
