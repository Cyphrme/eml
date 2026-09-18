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
//! calls cannot express the inherited frontier nodes at all. `SeedFrontier`
//! is the smallest addition that keeps the invariant
//! "one op, one atomic write" without smuggling optionality back into the
//! other five.
//!
//! Field-name collisions are handled by small named structs ([`NodeWrite`],
//! [`AlgorithmSeed`]) instead of positional tuples: `(u64, u64, u32, &[u8])`
//! lets a caller transpose an algorithm id and a left coordinate (both
//! `u64`) with no compiler complaint; a struct with named fields does not.

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

/// One algorithm's inherited genesis state, as part of a
/// [`WriteOp::SeedFrontier`] batch: its epoch history so far (carried from
/// the sealed source) and the frontier peaks
/// [`crate::tree::NaryMerkleLog::resume`] materializes as nodes.
#[derive(Debug, Clone, Copy)]
pub struct AlgorithmSeed<'a> {
    /// The algorithm being seeded.
    pub alg_id: u64,
    /// The algorithm's epoch history as of the seal.
    pub epochs: &'a [(u64, u64)],
    /// The frontier peaks to materialize as nodes (active ranges only).
    pub nodes: &'a [NodeWrite<'a>],
}

/// One atomic storage mutation. Every field on every variant is always
/// meaningful for that variant -- there is no optional field a caller must
/// remember to leave empty, and no combination [`Storage::apply`] must
/// reject at run time because the type system already refused to construct
/// it.
#[derive(Debug, Clone, Copy)]
pub enum WriteOp<'a> {
    /// Append a raw leaf payload at log position `at`, together with any
    /// active algorithm's leaf-hash node.
    AppendLeaf {
        /// The append-only position being written (== the count before this op).
        at: u64,
        /// The raw leaf payload.
        data: &'a [u8],
        /// Per-active-algorithm leaf node(s) produced by this append.
        nodes: &'a [NodeWrite<'a>],
    },
    /// Append a structured subtree at log position `at`: no leaf payload is
    /// stored, only the per-algorithm subtree-root node(s).
    AppendSubtree {
        /// The append-only position being written (== the count before this op).
        at: u64,
        /// Per-active-algorithm subtree-root node(s) produced by this append.
        nodes: &'a [NodeWrite<'a>],
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
        }
    }
}

/// Error type for [`MemoryStorage`] operations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MemoryStorageError {
    /// The requested leaf index has no data in this store.
    LeafNotFound {
        /// The index that was requested.
        index: u64,
        /// The number of stored leaves.
        stored: u64,
    },
    /// An [`WriteOp`] handed to [`Storage::apply`] violated its own
    /// precondition: an append at a position other than the current count,
    /// a duplicate algorithm registration, or a removal/resume naming an
    /// algorithm this store has never registered.
    InvalidOperation(String),
}

impl std::fmt::Display for MemoryStorageError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::LeafNotFound { index, stored } => write!(
                f,
                "leaf index {index} not found (storage contains {stored} leaves)"
            ),
            Self::InvalidOperation(reason) => write!(f, "invalid apply operation: {reason}"),
        }
    }
}

impl std::error::Error for MemoryStorageError {}

impl Storage for MemoryStorage {
    type Error = MemoryStorageError;

    async fn get_leaf(&self, index: u64) -> Result<Vec<u8>, Self::Error> {
        self.leaves
            .get(index as usize)
            .cloned()
            .ok_or(MemoryStorageError::LeafNotFound {
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

    async fn apply(&mut self, ops: &[WriteOp<'_>]) -> Result<(), Self::Error> {
        // Validate every op's precondition against a running projection of
        // this store's state *before* mutating anything, so a rejected
        // batch leaves `self` exactly as it was (the all-or-nothing
        // guarantee `Storage::apply` documents) -- a real transaction would
        // do this properly; a two-pass validate-then-apply is sufficient
        // for an in-memory reference store with no I/O to fail partway
        // through.
        let mut projected_count = self.count;
        // Algorithms this same batch has already registered, so a later op
        // in the batch is validated against what earlier ops just did, not
        // only against `self`'s state before the batch started -- mirroring
        // `GitStorage::build::apply`'s `known()` closure, per the composer's
        // ruling that a batch is validated as a unit.
        let mut registered_this_batch: std::collections::HashSet<u64> =
            std::collections::HashSet::new();
        for op in ops {
            match op {
                WriteOp::AppendLeaf { at, .. } | WriteOp::AppendSubtree { at, .. } => {
                    if *at != projected_count {
                        return Err(MemoryStorageError::InvalidOperation(format!(
                            "append at position {at}, expected the current count {projected_count}"
                        )));
                    }
                    projected_count += 1;
                },
                WriteOp::AddAlgorithm { alg_id, .. } => {
                    if registered_this_batch.contains(alg_id)
                        || self.algorithm_metas.contains_key(alg_id)
                    {
                        return Err(MemoryStorageError::InvalidOperation(format!(
                            "algorithm {alg_id} is already registered"
                        )));
                    }
                    registered_this_batch.insert(*alg_id);
                },
                WriteOp::RemoveAlgorithm { alg_id, .. }
                | WriteOp::ResumeAlgorithm { alg_id, .. } => {
                    if !registered_this_batch.contains(alg_id)
                        && !self.algorithm_metas.contains_key(alg_id)
                    {
                        return Err(MemoryStorageError::InvalidOperation(format!(
                            "algorithm {alg_id} is not registered"
                        )));
                    }
                },
                WriteOp::SeedFrontier { size, algorithms } => {
                    if projected_count != 0 || !registered_this_batch.is_empty() {
                        return Err(MemoryStorageError::InvalidOperation(
                            "SeedFrontier requires a fresh store: append_count must be 0 and no \
                             algorithm registered by an earlier op in this batch"
                                .to_string(),
                        ));
                    }
                    if !self.algorithm_metas.is_empty() {
                        return Err(MemoryStorageError::InvalidOperation(
                            "SeedFrontier requires a fresh store: no algorithm may already be \
                             registered"
                                .to_string(),
                        ));
                    }
                    for seed in *algorithms {
                        if !registered_this_batch.insert(seed.alg_id) {
                            return Err(MemoryStorageError::InvalidOperation(format!(
                                "algorithm {} is named twice in one SeedFrontier batch",
                                seed.alg_id
                            )));
                        }
                    }
                    projected_count = *size;
                },
            }
        }

        for op in ops {
            match op {
                WriteOp::AppendLeaf { at: _, data, nodes } => {
                    self.leaves.push(data.to_vec());
                    for n in *nodes {
                        self.nodes
                            .insert((n.alg_id, n.left, n.height), n.hash.to_vec());
                    }
                    self.count += 1;
                },
                WriteOp::AppendSubtree { at: _, nodes } => {
                    for n in *nodes {
                        self.nodes
                            .insert((n.alg_id, n.left, n.height), n.hash.to_vec());
                    }
                    self.count += 1;
                },
                WriteOp::AddAlgorithm { alg_id, epochs } => {
                    self.algorithm_metas.insert(*alg_id, epochs.to_vec());
                },
                WriteOp::RemoveAlgorithm { alg_id, epochs } => {
                    self.algorithm_metas.insert(*alg_id, epochs.to_vec());
                },
                WriteOp::ResumeAlgorithm {
                    alg_id,
                    epochs,
                    nodes,
                } => {
                    self.algorithm_metas.insert(*alg_id, epochs.to_vec());
                    for n in *nodes {
                        self.nodes
                            .insert((n.alg_id, n.left, n.height), n.hash.to_vec());
                    }
                },
                WriteOp::SeedFrontier { size, algorithms } => {
                    self.count = *size;
                    for seed in *algorithms {
                        self.algorithm_metas
                            .insert(seed.alg_id, seed.epochs.to_vec());
                        for n in seed.nodes {
                            self.nodes
                                .insert((n.alg_id, n.left, n.height), n.hash.to_vec());
                        }
                    }
                },
            }
        }
        Ok(())
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
