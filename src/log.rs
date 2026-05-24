//! EML Log — the core state machine.
//!
//! Implements Definitions 6-14c of the formal model: the EML state tuple,
//! leaf value function, append (with node persistence), algorithm
//! add/remove/resume, root extraction, projection, and proof generation.

use std::collections::BTreeMap;

use crate::error::{Error, Result};
use crate::hasher::Hasher;
use crate::null::NullTable;
use crate::storage::Storage;

type BoxedFuture<'a, T> = std::pin::Pin<Box<dyn std::future::Future<Output = T> + Send + 'a>>;

// ============================================================================
// Algorithm state
// ============================================================================

/// Per-algorithm state within the EML log.
#[derive(Debug)]
pub struct AlgState {
    /// The hasher instance for this algorithm.
    pub hasher: Box<dyn Hasher>,
    /// Disjoint active epochs. Each epoch is `(start, end)` where
    /// `end == u64::MAX` means the algorithm is currently active.
    /// Epochs are in chronological order and non-overlapping.
    pub epochs: Vec<(u64, u64)>,
    /// Frontier stack: roots of complete subtrees along the right edge.
    pub stack: Vec<Vec<u8>>,
    /// Precomputed null subtree constants.
    pub null_table: NullTable,
}

impl AlgState {
    /// Whether this algorithm is currently active (not frozen).
    fn is_active(&self) -> bool {
        self.epochs.last().is_some_and(|&(_, end)| end == u64::MAX)
    }

    /// Whether leaf index `i` falls within any of this algorithm's active epochs.
    fn is_active_at(&self, i: u64) -> bool {
        self.epochs
            .iter()
            .any(|&(start, end)| start <= i && i < end)
    }

    /// The tree size for this algorithm.
    ///
    /// Active algorithms track the global tree size.
    /// Frozen algorithms stopped at their last deactivation point.
    fn tree_size(&self, global_size: u64) -> u64 {
        if self.is_active() {
            global_size
        } else {
            self.epochs.last().map_or(0, |&(_, end)| end)
        }
    }

    /// The activation index of the first epoch.
    fn first_activation(&self) -> u64 {
        self.epochs.first().map_or(0, |&(start, _)| start)
    }

    /// Whether algorithm has active content in the half-open range `[lo, hi)`.
    ///
    /// Definition 14b (Active range): true iff any epoch overlaps the interval.
    /// Generalizes `is_active_at` from a single index to an interval.
    fn active_range(&self, lo: u64, hi: u64) -> bool {
        self.epochs
            .iter()
            .any(|&(start, end)| start < hi && end > lo)
    }
}

// ============================================================================
// Count trailing ones
// ============================================================================

/// Count trailing one-bits in the binary representation of `n`.
///
/// Used by the append algorithm (Definition 8) to determine the number
/// of stack merges after pushing a new leaf.
fn count_trailing_ones(n: u64) -> u32 {
    (!n).trailing_zeros()
}

// ============================================================================
// Epoch serialization
// ============================================================================

/// Canonically serialize a list of epochs to bytes.
///
/// Format:
/// - epochs.len() as u64 big-endian (8 bytes)
/// - For each (start, end) epoch:
///   - start as u64 big-endian (8 bytes)
///   - end as u64 big-endian (8 bytes)
pub(crate) fn serialize_epochs(epochs: &[(u64, u64)]) -> Vec<u8> {
    let mut bytes = Vec::with_capacity(8 + epochs.len() * 16);
    bytes.extend_from_slice(&(epochs.len() as u64).to_be_bytes());
    for &(start, end) in epochs {
        bytes.extend_from_slice(&start.to_be_bytes());
        bytes.extend_from_slice(&end.to_be_bytes());
    }
    bytes
}

// ============================================================================
// Null prefix peaks
// ============================================================================

/// Compute the frontier stack for a tree of `K` null leaves.
///
/// Definition 10 from the formal model. The stack decomposes `K` into its
/// binary components (MMR peaks), with subtrees ordered by descending bit
/// index (MSB first = largest subtrees at stack bottom).
///
/// For K=6 (binary 110): returns [N₂(a), N₁(a)] with N₁ on top.
fn null_prefix_peaks(hasher: &dyn Hasher, null_table: &mut NullTable, k: u64) -> Vec<Vec<u8>> {
    if k == 0 {
        return Vec::new();
    }

    let mut peaks = Vec::new();
    // Iterate bits from MSB to LSB (descending order).
    let bit_width = 64 - k.leading_zeros();
    for bit in (0..bit_width).rev() {
        if k & (1 << bit) != 0 {
            let null_root = null_table.get(hasher, bit as usize).to_vec();
            peaks.push(null_root);
        }
    }
    peaks
}

// EML Log
// ============================================================================

/// Per-algorithm metadata snapshot (Definition 13).
///
/// Returned by [`Log::algorithms`]. Contains all the data an implementor
/// needs to serialize a state manifest in their chosen wire format.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AlgorithmInfo {
    /// Algorithm identifier.
    pub id: u64,
    /// Current root hash for this algorithm.
    pub root: Vec<u8>,
    /// Global index at which this algorithm was first activated (inclusive).
    pub activation_index: u64,
    /// Global index at which this algorithm was last deactivated (exclusive).
    /// `None` if the algorithm is currently active.
    pub deactivation_index: Option<u64>,
    /// Effective tree size: last deactivation if frozen, else global tree size.
    pub tree_size: u64,
    /// Complete epoch history. Each `(start, end)` is an active interval.
    /// `end == None` means the epoch is currently open (algorithm is active).
    pub epochs: Vec<(u64, Option<u64>)>,
    /// Cryptographic digest of the canonical serialization of the algorithm's
    /// epoch list (manifest commitment).
    pub manifest_hash: Vec<u8>,
}

/// An Epoch Merkle Log.
///
/// Maintains a single shared topology across multiple hash algorithms.
/// Each algorithm sees the global tree, but positions outside its active
/// window contain deterministic null constants.
///
/// # Model Mapping
///
/// This struct implements Definition 6 (EML state):
/// `S = (storage, size, act, stacks, nodes)`
///
/// Raw leaf payloads and sealed internal node hashes are persisted
/// through the [`Storage`] backend. The log retains only frontier
/// stacks in memory (O(log n) per algorithm).
#[derive(Debug)]
pub struct Log<S: Storage> {
    /// Backend for raw leaf payloads and sealed internal node hashes.
    storage: S,
    /// Per-algorithm state, keyed by algorithm ID.
    algs: BTreeMap<u64, AlgState>,
}

impl<S: Storage> Log<S> {
    /// Create a new empty EML log with the given storage backend.
    pub fn new(storage: S) -> Self {
        Self {
            storage,
            algs: BTreeMap::new(),
        }
    }

    /// Reconstruct an EML log from a populated storage backend.
    ///
    /// Reads algorithm metadata (IDs, epoch boundaries) from storage and
    /// rebuilds frontier stacks in O(log n) per algorithm by resolving
    /// subtree roots from stored nodes.
    ///
    /// The consumer provides hasher instances mapped by algorithm ID.
    /// There must be a 1:1 correspondence between persisted metadata and
    /// provided hashers.
    ///
    /// # Errors
    ///
    /// Returns [`Error::OrphanedMetadata`] if storage contains metadata for
    /// an algorithm without a corresponding hasher.
    ///
    /// Returns [`Error::UnknownMetadata`] if a hasher is provided for an
    /// algorithm with no persisted metadata.
    pub async fn from_storage(storage: S, hashers: Vec<(u64, Box<dyn Hasher>)>) -> Result<Self> {
        let metas = storage
            .load_algorithm_metas()
            .await
            .map_err(|e| Error::Storage(Box::new(e)))?;

        let mut hasher_map: BTreeMap<u64, Box<dyn Hasher>> = hashers.into_iter().collect();

        // Validate 1:1 correspondence.
        for &(alg_id, _) in &metas {
            if !hasher_map.contains_key(&alg_id) {
                return Err(Error::OrphanedMetadata(alg_id));
            }
        }
        let meta_ids: std::collections::BTreeSet<u64> = metas.iter().map(|&(id, _)| id).collect();
        for &alg_id in hasher_map.keys() {
            if !meta_ids.contains(&alg_id) {
                return Err(Error::UnknownMetadata(alg_id));
            }
        }

        let global_size = storage.len().await;

        let mut algs = BTreeMap::new();
        for (alg_id, epochs) in metas {
            let hasher = hasher_map.remove(&alg_id).expect("validated above");
            let state =
                Self::reconstruct_algorithm_state(&storage, alg_id, hasher, &epochs, global_size)
                    .await?;
            algs.insert(alg_id, state);
        }

        Ok(Self { storage, algs })
    }

    fn validate_epochs(alg_id: u64, epochs: &[(u64, u64)], global_size: u64) -> Result<()> {
        if epochs.is_empty() {
            return Err(Error::CorruptedMetadata {
                alg_id,
                reason: "epoch sequence is empty".to_string(),
            });
        }
        let mut last_end = 0;
        for (i, &(start, end)) in epochs.iter().enumerate() {
            if start > end {
                return Err(Error::CorruptedMetadata {
                    alg_id,
                    reason: format!("epoch start {start} exceeds end {end}"),
                });
            }
            if start < last_end {
                return Err(Error::CorruptedMetadata {
                    alg_id,
                    reason: format!("epoch start {start} is less than prior end {last_end}"),
                });
            }
            if end != u64::MAX && end > global_size {
                return Err(Error::CorruptedMetadata {
                    alg_id,
                    reason: format!("epoch end {end} exceeds global size {global_size}"),
                });
            }
            if end == u64::MAX && i != epochs.len() - 1 {
                return Err(Error::CorruptedMetadata {
                    alg_id,
                    reason: "open epoch (end = u64::MAX) is not the final entry".to_string(),
                });
            }
            last_end = end;
        }
        if let Some(&(start, end)) = epochs.last() {
            if end == u64::MAX && start > global_size {
                return Err(Error::CorruptedMetadata {
                    alg_id,
                    reason: format!("active epoch start {start} exceeds global size {global_size}"),
                });
            }
        }
        Ok(())
    }

    /// Reconstruct a single algorithm's state from the storage backend.
    /// Exposing this enables the caller to orchestrate concurrency however they see fit.
    pub async fn reconstruct_algorithm_state(
        storage: &S,
        alg_id: u64,
        hasher: Box<dyn Hasher>,
        epochs: &[(u64, u64)],
        global_size: u64,
    ) -> Result<AlgState> {
        Self::validate_epochs(alg_id, epochs, global_size)?;
        let mut null_table = NullTable::new(hasher.as_ref());

        // Determine this algorithm's effective tree size.
        let is_active = epochs.last().is_some_and(|&(_, end)| end == u64::MAX);
        let tree_size = if is_active {
            global_size
        } else {
            epochs.last().map_or(0, |&(_, end)| end)
        };

        // Eagerly populate null table to tree height.
        if tree_size > 0 {
            let max_height = (64 - tree_size.leading_zeros()) as usize;
            null_table.ensure_height(hasher.as_ref(), max_height);
        }

        let state = AlgState {
            hasher,
            epochs: epochs.to_vec(),
            stack: Vec::new(),
            null_table,
        };

        // Reconstruct frontier stack by decomposing tree_size into binary.
        let stack =
            Self::reconstruct_frontier_for_state(storage, &state, alg_id, tree_size).await?;

        Ok(AlgState { stack, ..state })
    }

    /// Initialize a Log from a set of pre-reconstructed algorithm states.
    pub fn from_reconstructed_states(storage: S, states: BTreeMap<u64, AlgState>) -> Self {
        Self {
            storage,
            algs: states,
        }
    }

    /// Reconstruct the frontier stack for an algorithm from stored nodes.
    fn reconstruct_frontier_for_state<'a>(
        storage: &'a S,
        state: &'a AlgState,
        alg_id: u64,
        tree_size: u64,
    ) -> BoxedFuture<'a, Result<Vec<Vec<u8>>>> {
        Box::pin(async move {
            if tree_size == 0 {
                return Ok(Vec::new());
            }

            let mut stack = Vec::new();
            let bit_width = 64 - tree_size.leading_zeros();
            let mut pos = 0u64;

            // MSB-first: largest subtrees at the bottom of the stack.
            for bit in (0..bit_width).rev() {
                if tree_size & (1 << bit) != 0 {
                    let subtree_size = 1u64 << bit;
                    let root =
                        Self::subtree_root_static(storage, state, alg_id, pos, pos + subtree_size)
                            .await?;
                    stack.push(root);
                    pos += subtree_size;
                }
            }

            Ok(stack)
        })
    }

    /// Reconstruct the frontier stack and collect mixed boundary nodes.
    fn reconstruct_frontier_and_collect_mixed<'a>(
        storage: &'a S,
        state: &'a AlgState,
        alg_id: u64,
        tree_size: u64,
        deactivation: u64,
        collected: std::sync::Arc<std::sync::Mutex<Vec<(u64, usize, Vec<u8>)>>>,
    ) -> BoxedFuture<'a, Result<Vec<Vec<u8>>>> {
        Box::pin(async move {
            if tree_size == 0 {
                return Ok(Vec::new());
            }

            let mut stack = Vec::new();
            let bit_width = 64 - tree_size.leading_zeros();
            let mut pos = 0u64;

            for bit in (0..bit_width).rev() {
                if tree_size & (1 << bit) != 0 {
                    let subtree_size = 1u64 << bit;
                    let root = Self::reconstruct_and_collect_mixed(
                        storage,
                        state,
                        alg_id,
                        pos,
                        pos + subtree_size,
                        deactivation,
                        collected.clone(),
                    )
                    .await?;
                    stack.push(root);
                    pos += subtree_size;
                }
            }

            Ok(stack)
        })
    }

    /// Recursively resolve a subtree root and collect mixed boundary nodes.
    fn reconstruct_and_collect_mixed<'a>(
        storage: &'a S,
        state: &'a AlgState,
        alg_id: u64,
        lo: u64,
        hi: u64,
        deactivation: u64,
        collected: std::sync::Arc<std::sync::Mutex<Vec<(u64, usize, Vec<u8>)>>>,
    ) -> BoxedFuture<'a, Result<Vec<u8>>> {
        Box::pin(async move {
            let size = hi - lo;

            if size == 0 {
                return Ok(state.hasher.empty());
            }
            if size == 1 {
                if state.is_active_at(lo) {
                    let data = storage
                        .get_leaf(lo)
                        .await
                        .map_err(|e| Error::Storage(Box::new(e)))?;
                    return Ok(state.hasher.leaf(&data));
                }
                return Ok(state.null_table.leaf_null().to_vec());
            }

            if !state.active_range(lo, hi) {
                if size.is_power_of_two() {
                    let h = size.trailing_zeros() as usize;
                    return Ok(state.null_table.get_precomputed(h).to_vec());
                }
                return Self::null_range_root_static(state, size);
            }

            if size.is_power_of_two() {
                let h = size.trailing_zeros() as usize;
                if let Some(hash) = storage
                    .get_node(alg_id, lo, h)
                    .await
                    .map_err(|e| Error::Storage(Box::new(e)))?
                {
                    return Ok(hash);
                }
            }

            let k = crate::proof::largest_pow2_lt(size);
            let left = Self::reconstruct_and_collect_mixed(
                storage,
                state,
                alg_id,
                lo,
                lo + k,
                deactivation,
                collected.clone(),
            )
            .await?;
            let right = Self::reconstruct_and_collect_mixed(
                storage,
                state,
                alg_id,
                lo + k,
                hi,
                deactivation,
                collected.clone(),
            )
            .await?;
            let hash = state.hasher.node(&left, &right);

            if size.is_power_of_two() && lo < deactivation && deactivation < hi {
                let h = size.trailing_zeros() as usize;
                collected.lock().unwrap().push((lo, h, hash.clone()));
            }

            Ok(hash)
        })
    }

    /// Current number of leaves in the global log.
    pub async fn size(&self) -> u64 {
        self.storage.len().await
    }

    /// Consume the log and return the underlying storage backend.
    ///
    /// Useful for passing a populated storage to [`Log::from_storage`] after
    /// a process restart, or for direct storage inspection.
    pub fn into_storage(self) -> S {
        self.storage
    }

    // ========================================================================
    // Algorithm management (Definitions 9, 10, 11)
    // ========================================================================

    /// Register a new algorithm, activating it at the current tree size.
    ///
    /// Definition 9 (Add algorithm): the algorithm's frontier stack is
    /// initialized with null prefix peaks for all prior positions.
    ///
    /// # Errors
    ///
    /// Returns [`Error::DuplicateAlgorithm`] if `alg_id` is already registered.
    pub async fn add_algorithm(&mut self, alg_id: u64, hasher: Box<dyn Hasher>) -> Result<()> {
        if self.algs.contains_key(&alg_id) {
            return Err(Error::DuplicateAlgorithm(alg_id));
        }

        let activation = self.size().await;
        let epochs = vec![(activation, u64::MAX)];

        // Persist metadata BEFORE committing in-memory state.
        self.storage
            .store_algorithm_meta(alg_id, &epochs)
            .await
            .map_err(|e| Error::Storage(Box::new(e)))?;

        let mut null_table = NullTable::new(hasher.as_ref());
        let stack = null_prefix_peaks(hasher.as_ref(), &mut null_table, activation);

        // Eagerly populate null table to current tree height so that
        // proof generation (which takes &self) never needs mutation.
        if activation > 0 {
            let max_height = (64 - activation.leading_zeros()) as usize;
            null_table.ensure_height(hasher.as_ref(), max_height);
        }

        self.algs.insert(
            alg_id,
            AlgState {
                hasher,
                epochs,
                stack,
                null_table,
            },
        );

        Ok(())
    }

    /// Deactivate (freeze) an algorithm at the current tree size.
    ///
    /// Definition 11 (Remove algorithm): sets the deactivation boundary.
    /// The algorithm's frontier stack becomes immutable; future appends
    /// do not update it.
    ///
    /// # Errors
    ///
    /// Returns [`Error::UnknownAlgorithm`] if `alg_id` is not registered.
    /// Returns [`Error::FrozenAlgorithm`] if already deactivated.
    pub async fn remove_algorithm(&mut self, alg_id: u64) -> Result<()> {
        let current_size = self.size().await;
        let state = self
            .algs
            .get_mut(&alg_id)
            .ok_or(Error::UnknownAlgorithm(alg_id))?;

        if !state.is_active() {
            return Err(Error::FrozenAlgorithm(alg_id));
        }

        // Compute new epochs, persist, then commit in-memory.
        let mut new_epochs = state.epochs.clone();
        if let Some(last) = new_epochs.last_mut() {
            last.1 = current_size;
        }

        self.storage
            .store_algorithm_meta(alg_id, &new_epochs)
            .await
            .map_err(|e| Error::Storage(Box::new(e)))?;

        self.algs.get_mut(&alg_id).unwrap().epochs = new_epochs;
        Ok(())
    }

    /// Reactivate a frozen algorithm at the current tree size.
    ///
    /// The frozen frontier stack is reconstructed for the target tree size
    /// `n` by decomposing `n` into its binary representation and resolving
    /// each perfect subtree root via [`subtree_root`]: stored nodes for
    /// active ranges, `NullTable` for null ranges, and recursive binary
    /// splits for mixed boundary subtrees. A new active epoch
    /// `(current_size, ∞)` is appended.
    ///
    /// Complexity: O(log n) hash operations, where n = current tree size.
    ///
    /// # Performance Note
    ///
    /// Mixed internal nodes at the deactivation boundary (subtrees spanning
    /// both real-data and null-gap positions) are computed on the fly during
    /// frontier reconstruction but are **not persisted** to storage.
    /// Subsequent proof generation that traverses these boundary nodes will
    /// recompute them via `subtree_root`'s recursive binary split — at most
    /// O(log n) extra hashes per proof, which does not change the asymptotic
    /// proof cost.
    ///
    /// If profiling reveals this as a measurable overhead (e.g., with many
    /// resume cycles creating multiple boundaries), a post-resume persistence
    /// pass could walk the single mixed spine and store each internal node.
    ///
    /// # Errors
    ///
    /// Returns [`Error::UnknownAlgorithm`] if `alg_id` is not registered.
    /// Returns [`Error::AlgorithmActive`] if the algorithm is already active.
    pub async fn resume_algorithm(&mut self, alg_id: u64) -> Result<()> {
        let current_size = self.storage.len().await;

        // Validate state and extract parameters.
        let state = self
            .algs
            .get(&alg_id)
            .ok_or(Error::UnknownAlgorithm(alg_id))?;

        if state.is_active() {
            return Err(Error::AlgorithmActive(alg_id));
        }

        let deactivation = state.epochs.last().unwrap().1;
        let gap = current_size - deactivation;

        // Compute new epochs and persist BEFORE committing in-memory state.
        let mut new_epochs = state.epochs.clone();
        new_epochs.push((current_size, u64::MAX));

        self.storage
            .store_algorithm_meta(alg_id, &new_epochs)
            .await
            .map_err(|e| Error::Storage(Box::new(e)))?;

        if gap > 0 {
            // Ensure null table covers the target tree height.
            {
                let state = self.algs.get_mut(&alg_id).unwrap();
                let max_height = (64 - current_size.leading_zeros()) as usize;
                state
                    .null_table
                    .ensure_height(state.hasher.as_ref(), max_height);
            }

            // Reconstruct the frontier from scratch for the target tree size.
            // During reconstruction, any computed boundary/mixed subtrees of power-of-two size
            // are collected.
            let state = &self.algs[&alg_id];
            let collected = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
            let new_stack = Self::reconstruct_frontier_and_collect_mixed(
                &self.storage,
                state,
                alg_id,
                current_size,
                deactivation,
                collected.clone(),
            )
            .await?;

            // Persist the collected mixed/boundary nodes to storage in a batch write.
            let nodes_to_store = {
                let mut guard = collected.lock().unwrap();
                std::mem::take(&mut *guard)
            };
            let batch_nodes: Vec<(u64, u64, usize, &[u8])> = nodes_to_store
                .iter()
                .map(|&(lo, h, ref hash)| (alg_id, lo, h, hash.as_slice()))
                .collect();
            self.storage
                .write_batch(&[], &batch_nodes)
                .await
                .map_err(|e| Error::Storage(Box::new(e)))?;

            self.algs.get_mut(&alg_id).unwrap().stack = new_stack;
        }

        // Eagerly populate null table to current tree height.
        {
            let state = self.algs.get_mut(&alg_id).unwrap();
            let max_height = (64 - current_size.leading_zeros()) as usize;
            state
                .null_table
                .ensure_height(state.hasher.as_ref(), max_height);
        }

        self.algs.get_mut(&alg_id).unwrap().epochs = new_epochs;
        Ok(())
    }

    /// Check whether an algorithm is currently active.
    ///
    /// Returns `None` if the algorithm is not registered.
    #[must_use]
    pub fn is_active(&self, alg_id: u64) -> Option<bool> {
        self.algs.get(&alg_id).map(|s| s.is_active())
    }

    /// Get the tree size for a specific algorithm.
    ///
    /// Active algorithms return the global tree size.
    /// Frozen algorithms return their deactivation point.
    ///
    /// # Errors
    ///
    /// Returns [`Error::UnknownAlgorithm`] if `alg_id` is not registered.
    pub async fn tree_size(&self, alg_id: u64) -> Result<u64> {
        let size = self.size().await;
        self.algs
            .get(&alg_id)
            .map(|s| s.tree_size(size))
            .ok_or(Error::UnknownAlgorithm(alg_id))
    }

    // ========================================================================
    // Append (Definition 8)
    // ========================================================================

    /// Append a new leaf payload to the log.
    ///
    /// Definition 8 (Append): pushes the leaf hash (or null constant) onto
    /// each active algorithm's frontier stack, then merges complete pairs
    /// by counting trailing ones in the pre-increment size. Sealed parent
    /// nodes are persisted into storage for O(log n) proof generation.
    ///
    /// Frozen algorithms are not updated.
    ///
    /// Returns the 0-based leaf index.
    ///
    /// # Errors
    ///
    /// Returns [`Error::NoActiveAlgorithms`] if no algorithms are active.
    pub async fn append(&mut self, data: &[u8]) -> Result<u64> {
        let size_before = self.size().await;
        self.append_batch(&[data]).await?;
        Ok(size_before)
    }

    /// Append a batch of leaf payloads to the EML log.
    ///
    /// Performs in-memory Merkle tree mutations and commits all new leaves and nodes
    /// in a single batch write to the storage engine (using `write_batch`), achieving
    /// atomic transactions and optimal I/O throughput in database implementations.
    ///
    /// Returns the global tree size *after* the appends.
    pub async fn append_batch(&mut self, data_items: &[&[u8]]) -> Result<u64> {
        if data_items.is_empty() {
            return Ok(self.size().await);
        }
        if !self.algs.values().any(|s| s.is_active()) {
            return Err(Error::NoActiveAlgorithms);
        }

        let mut leaves = Vec::with_capacity(data_items.len());
        let mut nodes = Vec::new();
        let start_index = self.size().await;

        for (offset, &data) in data_items.iter().enumerate() {
            let index = start_index + offset as u64;
            leaves.push((index, data));

            let merge_count = count_trailing_ones(index);

            for (&alg_id, state) in self.algs.iter_mut() {
                if !state.is_active() {
                    continue;
                }

                let digest = if state.is_active_at(index) {
                    state.hasher.leaf(data)
                } else {
                    state.null_table.leaf_null().to_vec()
                };

                state.stack.push(digest);

                for j in 1..=merge_count {
                    let right = state.stack.pop().expect("stack underflow in merge");
                    let left = state.stack.pop().expect("stack underflow in merge");
                    let parent = state.hasher.node(&left, &right);

                    let height = j as usize;
                    let left_pos = index + 1 - (1u64 << height);
                    nodes.push((alg_id, left_pos, height, parent.clone()));

                    state.stack.push(parent);
                }

                // Eagerly populate null table to current tree height.
                let tree_size = index + 1;
                let max_height = (64 - tree_size.leading_zeros()) as usize;
                state
                    .null_table
                    .ensure_height(state.hasher.as_ref(), max_height);
            }
        }

        // Commit leaves and nodes in a single call.
        let raw_nodes: Vec<(u64, u64, usize, &[u8])> = nodes
            .iter()
            .map(|n| (n.0, n.1, n.2, n.3.as_slice()))
            .collect();
        self.storage
            .write_batch(&leaves, &raw_nodes)
            .await
            .map_err(|e| Error::Storage(Box::new(e)))?;

        Ok(start_index + data_items.len() as u64)
    }

    // ========================================================================
    // Root extraction (Definition 12)
    // ========================================================================

    /// Compute the current root hash for a specific algorithm.
    ///
    /// Definition 12 (Per-algorithm root): folds the frontier stack
    /// right-to-left via `node(a, left, acc)`.
    ///
    /// # Errors
    ///
    /// Returns [`Error::UnknownAlgorithm`] if `alg_id` is not registered.
    pub fn root(&self, alg_id: u64) -> Result<Vec<u8>> {
        let state = self
            .algs
            .get(&alg_id)
            .ok_or(Error::UnknownAlgorithm(alg_id))?;

        if state.stack.is_empty() {
            return Ok(state.hasher.empty());
        }

        // Fold right-to-left: the rightmost stack entry is the accumulator seed.
        let mut iter = state.stack.iter().rev();
        let first = iter
            .next()
            .expect("non-empty stack has at least one element")
            .clone();
        let root = iter.fold(first, |acc, left| state.hasher.node(left, &acc));

        Ok(root)
    }

    /// Returns an iterator over all registered algorithm IDs.
    pub fn algorithm_ids(&self) -> impl Iterator<Item = u64> + '_ {
        self.algs.keys().copied()
    }

    /// Returns the first activation index for an algorithm.
    ///
    /// # Errors
    ///
    /// Returns [`Error::UnknownAlgorithm`] if `alg_id` is not registered.
    pub fn activation_index(&self, alg_id: u64) -> Result<u64> {
        self.algs
            .get(&alg_id)
            .map(|s| s.first_activation())
            .ok_or(Error::UnknownAlgorithm(alg_id))
    }

    /// Returns the last deactivation index for an algorithm.
    ///
    /// Returns `None` in the inner `Option` if the algorithm is currently active.
    ///
    /// # Errors
    ///
    /// Returns [`Error::UnknownAlgorithm`] if `alg_id` is not registered.
    pub fn deactivation_index(&self, alg_id: u64) -> Result<Option<u64>> {
        self.algs
            .get(&alg_id)
            .map(|s| {
                if s.is_active() {
                    None
                } else {
                    s.epochs.last().map(|&(_, end)| end)
                }
            })
            .ok_or(Error::UnknownAlgorithm(alg_id))
    }

    /// Returns the full epoch history for an algorithm.
    ///
    /// Each epoch is `(start, end)` where `end == None` means active.
    ///
    /// # Errors
    ///
    /// Returns [`Error::UnknownAlgorithm`] if `alg_id` is not registered.
    pub fn epochs(&self, alg_id: u64) -> Result<Vec<(u64, Option<u64>)>> {
        self.algs
            .get(&alg_id)
            .map(|s| {
                s.epochs
                    .iter()
                    .map(|&(start, end)| {
                        if end == u64::MAX {
                            (start, None)
                        } else {
                            (start, Some(end))
                        }
                    })
                    .collect()
            })
            .ok_or(Error::UnknownAlgorithm(alg_id))
    }

    // ========================================================================
    // EML Manifest (Definition 13)
    // ========================================================================

    /// Produce a snapshot of all registered algorithms' state.
    ///
    /// Definition 13 (EML Manifest): returns the data needed to construct
    /// a state manifest. Each [`AlgorithmInfo`] contains the algorithm's
    /// root hash, activation/deactivation boundaries, and tree size.
    ///
    /// The serialization format is left to the implementor — EML provides
    /// the raw data; the consumer chooses the wire encoding.
    pub async fn algorithms(&self) -> Vec<AlgorithmInfo> {
        let global_size = self.size().await;
        self.algs
            .iter()
            .map(|(&id, state)| {
                let ts = state.tree_size(global_size);
                let root = if state.stack.is_empty() {
                    state.hasher.empty()
                } else {
                    let mut iter = state.stack.iter().rev();
                    let first = iter
                        .next()
                        .expect("non-empty stack has at least one element")
                        .clone();
                    iter.fold(first, |acc, left| state.hasher.node(left, &acc))
                };
                let serialized = serialize_epochs(&state.epochs);
                let manifest_hash = state.hasher.hash(&serialized);

                AlgorithmInfo {
                    id,
                    root,
                    activation_index: state.epochs.first().map(|e| e.0).unwrap_or(0),
                    deactivation_index: state
                        .epochs
                        .last()
                        .and_then(|e| if e.1 == u64::MAX { None } else { Some(e.1) }),
                    tree_size: ts,
                    epochs: state
                        .epochs
                        .iter()
                        .map(|&(start, end)| {
                            (start, if end == u64::MAX { None } else { Some(end) })
                        })
                        .collect(),
                    manifest_hash,
                }
            })
            .collect()
    }

    /// Returns the stack length for a specific algorithm (for testing invariants).
    #[cfg(test)]
    fn stack_len(&self, alg_id: u64) -> Option<usize> {
        self.algs.get(&alg_id).map(|s| s.stack.len())
    }

    /// Test accessor: compute subtree root over `[lo, hi)` for `alg_id`.
    ///
    /// Delegates to `subtree_root` (Definition 14c) without requiring
    /// callers to hold an `AlgState` reference.
    #[cfg(test)]
    pub(crate) async fn test_subtree_root(&self, alg_id: u64, lo: u64, hi: u64) -> Result<Vec<u8>> {
        let state = self
            .algs
            .get(&alg_id)
            .ok_or(Error::UnknownAlgorithm(alg_id))?;
        Self::subtree_root_static(&self.storage, state, alg_id, lo, hi).await
    }

    // ========================================================================
    // Subtree root query (Definition 14c)
    // ========================================================================

    /// Compute the root hash of the subtree covering leaves `[lo, hi)` for
    /// algorithm `alg_id`.
    ///
    /// Definition 14c (Subtree root): dispatches through stored node lookups,
    /// NullTable for inactive ranges, and recursive binary splits for ranges
    /// not directly cached.
    ///
    /// This is the O(log n) mechanism that replaces projection-based proof
    /// generation.
    fn subtree_root_static<'a>(
        storage: &'a S,
        state: &'a AlgState,
        alg_id: u64,
        lo: u64,
        hi: u64,
    ) -> BoxedFuture<'a, Result<Vec<u8>>> {
        Box::pin(async move {
            let size = hi - lo;

            // Base cases.
            if size == 0 {
                return Ok(state.hasher.empty());
            }
            if size == 1 {
                // Single leaf: compute V(a, lo).
                if state.is_active_at(lo) {
                    let data = storage
                        .get_leaf(lo)
                        .await
                        .map_err(|e| Error::Storage(Box::new(e)))?;
                    return Ok(state.hasher.leaf(&data));
                }
                return Ok(state.null_table.leaf_null().to_vec());
            }

            // Null range optimization: if no epoch overlaps [lo, hi), the entire
            // subtree is null-valued.
            if !state.active_range(lo, hi) {
                if size.is_power_of_two() {
                    // Power-of-2 null range: direct NullTable lookup.
                    let h = size.trailing_zeros() as usize;
                    return Ok(state.null_table.get_precomputed(h).to_vec());
                }
                // Non-power-of-2 null range: decompose into power-of-2 subtrees.
                return Self::null_range_root_static(state, size);
            }

            // Stored node lookup: only valid for power-of-2 aligned ranges.
            if size.is_power_of_two() {
                let h = size.trailing_zeros() as usize;
                if let Some(hash) = storage
                    .get_node(alg_id, lo, h)
                    .await
                    .map_err(|e| Error::Storage(Box::new(e)))?
                {
                    return Ok(hash);
                }
            }

            // RFC 9162 binary split.
            let k = crate::proof::largest_pow2_lt(size);
            let left = Self::subtree_root_static(storage, state, alg_id, lo, lo + k).await?;
            let right = Self::subtree_root_static(storage, state, alg_id, lo + k, hi).await?;
            Ok(state.hasher.node(&left, &right))
        })
    }

    /// Compute the root of `size` consecutive null leaves for algorithm `a`.
    ///
    /// Definition 14d (Null range root): decomposes a non-power-of-2 null
    /// range into power-of-2 subtrees whose roots are NullTable lookups.
    /// Complexity: O(popcount(size)) hash operations.
    fn null_range_root_static(state: &AlgState, size: u64) -> Result<Vec<u8>> {
        debug_assert!(size > 0, "null_range_root requires size > 0");

        if size == 1 {
            return Ok(state.null_table.leaf_null().to_vec());
        }

        // Decompose: largest power-of-2 subtree on the left, remainder on right.
        let k_bits = 63 - (size.leading_zeros() as u64);
        let k = 1u64 << k_bits;

        let left_root = state.null_table.get_precomputed(k_bits as usize).to_vec();

        let remainder = size - k;
        if remainder == 0 {
            return Ok(left_root);
        }

        let right_root = Self::null_range_root_static(state, remainder)?;
        Ok(state.hasher.node(&left_root, &right_root))
    }

    // ========================================================================
    // Projection (Definition 14) — Specification Oracle
    // ========================================================================

    /// Compute the projected leaf hash sequence for an algorithm.
    ///
    /// Definition 14: for each global index `i` in `[0, tree_size(a))`,
    /// the projected leaf is `leaf(a, data[i])` if `active(a, i)`, else
    /// `N₀(a)` (the null leaf constant).
    ///
    /// **Oracle designation:** This is an O(n) specification oracle used
    /// exclusively by test code for equational law verification. Production
    /// proof generation uses `subtree_root` (Definition 14c).
    ///
    /// # Errors
    ///
    /// Returns [`Error::UnknownAlgorithm`] if `alg_id` is not registered.
    #[cfg(test)]
    pub async fn project(&self, alg_id: u64) -> Result<Vec<Vec<u8>>> {
        let state = self
            .algs
            .get(&alg_id)
            .ok_or(Error::UnknownAlgorithm(alg_id))?;

        let ts = state.tree_size(self.size().await);
        let mut leaves = Vec::with_capacity(ts as usize);
        for i in 0..ts {
            let leaf_hash = if state.is_active_at(i) {
                let data = self
                    .storage
                    .get_leaf(i)
                    .await
                    .map_err(|e| Error::Storage(Box::new(e)))?;
                state.hasher.leaf(&data)
            } else {
                state.null_table.leaf_null().to_vec()
            };
            leaves.push(leaf_hash);
        }
        Ok(leaves)
    }

    // ========================================================================
    // Proof generation (Definitions 15-16 — Operational)
    // ========================================================================

    /// Generate an inclusion proof for leaf `index` under algorithm `alg_id`.
    ///
    /// Definition 15 (Inclusion proof — operational): uses range-based PATH
    /// algorithm with `subtree_root` for O(log n) sibling resolution.
    ///
    /// # Errors
    ///
    /// Returns [`Error::UnknownAlgorithm`] if `alg_id` is not registered.
    /// Returns [`Error::IndexOutOfBounds`] if `index >= tree_size(alg_id)`.
    pub async fn inclusion_proof(
        &self,
        alg_id: u64,
        index: u64,
    ) -> Result<crate::proof::InclusionProof> {
        let state = self
            .algs
            .get(&alg_id)
            .ok_or(Error::UnknownAlgorithm(alg_id))?;

        let ts = state.tree_size(self.size().await);
        if ts == 0 || index >= ts {
            return Err(Error::IndexOutOfBounds {
                index,
                tree_size: ts,
            });
        }

        let mut path = Vec::with_capacity(64);
        self.path(state, alg_id, index, 0, ts, &mut path).await?;

        Ok(crate::proof::InclusionProof {
            index,
            tree_size: ts,
            path,
        })
    }

    /// RFC 9162 PATH algorithm (§2.1.3) using `subtree_root`.
    ///
    /// Recursively computes sibling hashes from leaf `m` within `[lo, hi)`.
    fn path<'a>(
        &'a self,
        state: &'a AlgState,
        alg_id: u64,
        m: u64,
        lo: u64,
        hi: u64,
        path: &'a mut Vec<Vec<u8>>,
    ) -> BoxedFuture<'a, Result<()>> {
        Box::pin(async move {
            let size = hi - lo;
            if size <= 1 {
                return Ok(());
            }

            let k = crate::proof::largest_pow2_lt(size);
            if m - lo < k {
                // Target is in the left subtree; right subtree is the sibling.
                self.path(state, alg_id, m, lo, lo + k, path).await?;
                let sib =
                    Self::subtree_root_static(&self.storage, state, alg_id, lo + k, hi).await?;
                path.push(sib);
            } else {
                // Target is in the right subtree; left subtree is the sibling.
                self.path(state, alg_id, m, lo + k, hi, path).await?;
                let sib =
                    Self::subtree_root_static(&self.storage, state, alg_id, lo, lo + k).await?;
                path.push(sib);
            }
            Ok(())
        })
    }

    /// Generate a consistency proof from `old_size` to the current tree
    /// for algorithm `alg_id`.
    ///
    /// Definition 16 (Consistency proof — operational): uses range-based
    /// SUBPROOF algorithm with `subtree_root` for O(log n) sibling resolution.
    ///
    /// # Errors
    ///
    /// Returns [`Error::UnknownAlgorithm`] if `alg_id` is not registered.
    /// Returns [`Error::IndexOutOfBounds`] if `old_size` is out of range.
    pub async fn consistency_proof(
        &self,
        alg_id: u64,
        old_size: u64,
    ) -> Result<crate::proof::ConsistencyProof> {
        let state = self
            .algs
            .get(&alg_id)
            .ok_or(Error::UnknownAlgorithm(alg_id))?;

        let ts = state.tree_size(self.size().await);
        if old_size == 0 || old_size >= ts {
            return Err(Error::IndexOutOfBounds {
                index: old_size,
                tree_size: ts,
            });
        }

        let mut path = Vec::with_capacity(64);
        self.subproof(state, alg_id, old_size, 0, ts, true, &mut path)
            .await?;

        Ok(crate::proof::ConsistencyProof {
            old_size,
            new_size: ts,
            path,
        })
    }

    /// RFC 9162 SUBPROOF algorithm (§2.1.4) using `subtree_root`.
    ///
    /// Recursively computes the intermediate hashes proving that the first
    /// `m` leaves (relative to `lo`) form a prefix of `[lo, hi)`.
    #[allow(clippy::too_many_arguments)]
    fn subproof<'a>(
        &'a self,
        state: &'a AlgState,
        alg_id: u64,
        m: u64,
        lo: u64,
        hi: u64,
        b: bool,
        path: &'a mut Vec<Vec<u8>>,
    ) -> BoxedFuture<'a, Result<()>> {
        Box::pin(async move {
            let size = hi - lo;
            if m == size {
                if !b {
                    let r = Self::subtree_root_static(&self.storage, state, alg_id, lo, hi).await?;
                    path.push(r);
                }
                return Ok(());
            }

            let k = crate::proof::largest_pow2_lt(size);
            if m <= k {
                self.subproof(state, alg_id, m, lo, lo + k, b, path).await?;
                let r = Self::subtree_root_static(&self.storage, state, alg_id, lo + k, hi).await?;
                path.push(r);
            } else {
                self.subproof(state, alg_id, m - k, lo + k, hi, false, path)
                    .await?;
                let r = Self::subtree_root_static(&self.storage, state, alg_id, lo, lo + k).await?;
                path.push(r);
            }
            Ok(())
        })
    }
}

impl Default for Log<crate::storage::MemoryStorage> {
    fn default() -> Self {
        Self::new(crate::storage::MemoryStorage::new())
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::storage::MemoryStorage;
    use crate::test_hashers::{AltHasher, Sha256Hasher};

    /// Batch-compute the Merkle tree root via the canonical RFC 9162 mth.
    fn batch_root(hasher: &dyn Hasher, leaf_hashes: &[Vec<u8>]) -> Vec<u8> {
        crate::proof::mth(hasher, leaf_hashes)
    }

    // ---- A-EQUIV-EML: incremental equals batch ----

    #[test]
    fn a_equiv_single_algorithm() {
        smol::block_on(async {
            let mut log = Log::new(MemoryStorage::new());
            log.add_algorithm(0, Box::new(Sha256Hasher)).await.unwrap();

            for i in 0..16u8 {
                log.append(&[i]).await.unwrap();

                let incremental = log.root(0).unwrap();
                let projected = log.project(0).await.unwrap();
                let batch = batch_root(&Sha256Hasher, &projected);
                assert_eq!(incremental, batch, "A-EQUIV-EML failed at size {}", i + 1);
            }
        });
    }

    #[test]
    fn a_equiv_mid_stream_algorithm() {
        smol::block_on(async {
            let mut log = Log::new(MemoryStorage::new());
            log.add_algorithm(0, Box::new(Sha256Hasher)).await.unwrap();

            // Append 4 leaves with only alg 0.
            for i in 0..4u8 {
                log.append(&[i]).await.unwrap();
            }

            // Add alg 1 mid-stream at index 4.
            log.add_algorithm(1, Box::new(AltHasher)).await.unwrap();

            // Append 4 more leaves with both algs active.
            for i in 4..8u8 {
                log.append(&[i]).await.unwrap();
            }

            // Verify A-EQUIV for both algorithms.
            for alg_id in [0, 1] {
                let incremental = log.root(alg_id).unwrap();
                let projected = log.project(alg_id).await.unwrap();
                let hasher: &dyn Hasher = if alg_id == 0 {
                    &Sha256Hasher
                } else {
                    &AltHasher
                };
                let batch = batch_root(hasher, &projected);
                assert_eq!(incremental, batch, "A-EQUIV-EML failed for alg {alg_id}");
            }
        });
    }

    // ---- A-STACK-EML: popcount invariant ----

    #[test]
    fn a_stack_popcount_invariant() {
        smol::block_on(async {
            let mut log = Log::new(MemoryStorage::new());
            log.add_algorithm(0, Box::new(Sha256Hasher)).await.unwrap();

            for i in 0..20u8 {
                log.append(&[i]).await.unwrap();
                let expected = (log.size().await).count_ones() as usize;
                assert_eq!(
                    log.stack_len(0).unwrap(),
                    expected,
                    "A-STACK-EML failed at size {}",
                    log.size().await
                );
            }
        });
    }

    #[test]
    fn a_stack_frozen_algorithm() {
        smol::block_on(async {
            let mut log = Log::new(MemoryStorage::new());
            log.add_algorithm(0, Box::new(Sha256Hasher)).await.unwrap();

            for i in 0..6u8 {
                log.append(&[i]).await.unwrap();
            }

            // Freeze at size 6.
            log.remove_algorithm(0).await.unwrap();
            let frozen_stack_len = log.stack_len(0).unwrap();
            let expected = 6u64.count_ones() as usize; // popcount(6) = 2
            assert_eq!(frozen_stack_len, expected);

            // Further appends don't change the frozen stack.
            log.add_algorithm(1, Box::new(AltHasher)).await.unwrap();
            for i in 6..10u8 {
                log.append(&[i]).await.unwrap();
            }
            assert_eq!(log.stack_len(0).unwrap(), frozen_stack_len);
        });
    }

    // ---- T-BOUND: temporal binding ----

    #[test]
    fn t_bound_null_prefix_differs_from_real_leaf() {
        smol::block_on(async {
            let mut log = Log::new(MemoryStorage::new());
            log.add_algorithm(0, Box::new(Sha256Hasher)).await.unwrap();

            // Append 4 leaves.
            for i in 0..4u8 {
                log.append(&[i]).await.unwrap();
            }

            // Add alg 1 at index 4 — indices 0..4 are null for alg 1.
            log.add_algorithm(1, Box::new(AltHasher)).await.unwrap();

            // Append 4 more.
            for i in 4..8u8 {
                log.append(&[i]).await.unwrap();
            }

            // The projected leaf at index 0 for alg 1 should be N₀, not leaf(data[0]).
            let state = log.algs.get(&1).unwrap();
            let null_leaf = state.null_table.leaf_null();
            let leaf0_data = log.storage.get_leaf(0).await.unwrap();
            let real_leaf = state.hasher.leaf(&leaf0_data);

            assert_ne!(
                null_leaf,
                real_leaf.as_slice(),
                "T-BOUND: null prefix position must differ from real leaf hash"
            );
        });
    }

    // ---- ALG-IND: algorithm independence ----

    #[test]
    fn alg_ind_different_algorithms_different_roots() {
        smol::block_on(async {
            let mut log = Log::new(MemoryStorage::new());
            log.add_algorithm(0, Box::new(Sha256Hasher)).await.unwrap();
            log.add_algorithm(1, Box::new(AltHasher)).await.unwrap();

            for i in 0..8u8 {
                log.append(&[i]).await.unwrap();
            }

            let root0 = log.root(0).unwrap();
            let root1 = log.root(1).unwrap();
            assert_ne!(
                root0, root1,
                "ALG-IND: different algorithms must produce different roots"
            );
        });
    }

    // ---- Error cases ----

    #[test]
    fn error_duplicate_algorithm() {
        smol::block_on(async {
            let mut log = Log::new(MemoryStorage::new());
            log.add_algorithm(0, Box::new(Sha256Hasher)).await.unwrap();
            let err = log
                .add_algorithm(0, Box::new(Sha256Hasher))
                .await
                .unwrap_err();
            assert_eq!(err, Error::DuplicateAlgorithm(0));
        });
    }

    #[test]
    fn error_unknown_algorithm() {
        smol::block_on(async {
            let log = Log::new(MemoryStorage::new());
            let err = log.root(99).unwrap_err();
            assert_eq!(err, Error::UnknownAlgorithm(99));
        });
    }

    #[test]
    fn error_no_active_algorithms() {
        smol::block_on(async {
            let mut log = Log::new(MemoryStorage::new());
            let err = log.append(b"data").await.unwrap_err();
            assert_eq!(err, Error::NoActiveAlgorithms);
        });
    }

    #[test]
    fn error_double_freeze() {
        smol::block_on(async {
            let mut log = Log::new(MemoryStorage::new());
            log.add_algorithm(0, Box::new(Sha256Hasher)).await.unwrap();
            log.append(b"data").await.unwrap();
            log.remove_algorithm(0).await.unwrap();
            let err = log.remove_algorithm(0).await.unwrap_err();
            assert_eq!(err, Error::FrozenAlgorithm(0));
        });
    }

    // ---- Empty tree ----

    #[test]
    fn empty_tree_root() {
        smol::block_on(async {
            let mut log = Log::new(MemoryStorage::new());
            log.add_algorithm(0, Box::new(Sha256Hasher)).await.unwrap();
            let root = log.root(0).unwrap();
            assert_eq!(root, Sha256Hasher.empty());
        });
    }

    // ---- Frozen algorithm root stability ----

    #[test]
    fn frozen_root_is_stable() {
        smol::block_on(async {
            let mut log = Log::new(MemoryStorage::new());
            log.add_algorithm(0, Box::new(Sha256Hasher)).await.unwrap();

            for i in 0..5u8 {
                log.append(&[i]).await.unwrap();
            }

            let root_before = log.root(0).unwrap();
            log.remove_algorithm(0).await.unwrap();
            let root_after = log.root(0).unwrap();

            assert_eq!(root_before, root_after, "root must not change on freeze");

            // Further appends to other algorithms don't change frozen root.
            log.add_algorithm(1, Box::new(AltHasher)).await.unwrap();
            for i in 5..10u8 {
                log.append(&[i]).await.unwrap();
            }
            let root_still = log.root(0).unwrap();
            assert_eq!(root_before, root_still, "frozen root must remain stable");
        });
    }

    // ---- A-EQUIV-EML for non-power-of-two sizes ----

    #[test]
    fn a_equiv_non_power_of_two() {
        smol::block_on(async {
            // Test sizes that exercise the incomplete-tree fold path.
            for size in [1, 3, 5, 7, 9, 11, 13, 15, 17, 19] {
                let mut log = Log::new(MemoryStorage::new());
                log.add_algorithm(0, Box::new(Sha256Hasher)).await.unwrap();

                for i in 0..size as u8 {
                    log.append(&[i]).await.unwrap();
                }

                let incremental = log.root(0).unwrap();
                let projected = log.project(0).await.unwrap();
                let batch = batch_root(&Sha256Hasher, &projected);
                assert_eq!(incremental, batch, "A-EQUIV failed at size {size}");
            }
        });
    }

    // ---- I-SOUND-EML: inclusion proof soundness ----

    #[test]
    fn i_sound_single_algorithm() {
        smol::block_on(async {
            let mut log = Log::new(MemoryStorage::new());
            log.add_algorithm(0, Box::new(Sha256Hasher)).await.unwrap();

            for i in 0..12u8 {
                log.append(&[i]).await.unwrap();
            }

            let root = log.root(0).unwrap();
            let projected = log.project(0).await.unwrap();

            for idx in 0..12u64 {
                let proof = log.inclusion_proof(0, idx).await.unwrap();
                let leaf_hash = &projected[idx as usize];
                assert!(
                    crate::proof::verify_inclusion(&Sha256Hasher, leaf_hash, &proof, &root),
                    "I-SOUND-EML failed at index {idx}"
                );
            }
        });
    }

    #[test]
    fn i_sound_mid_stream_algorithm() {
        smol::block_on(async {
            let mut log = Log::new(MemoryStorage::new());
            log.add_algorithm(0, Box::new(Sha256Hasher)).await.unwrap();

            for i in 0..4u8 {
                log.append(&[i]).await.unwrap();
            }

            // Add alg 1 mid-stream.
            log.add_algorithm(1, Box::new(AltHasher)).await.unwrap();

            for i in 4..12u8 {
                log.append(&[i]).await.unwrap();
            }

            // Verify inclusion proofs for alg 1 (null prefix at 0..4, real at 4..12).
            let root = log.root(1).unwrap();
            let projected = log.project(1).await.unwrap();

            for idx in 0..12u64 {
                let proof = log.inclusion_proof(1, idx).await.unwrap();
                let leaf_hash = &projected[idx as usize];
                assert!(
                    crate::proof::verify_inclusion(&AltHasher, leaf_hash, &proof, &root),
                    "I-SOUND-EML (mid-stream) failed at index {idx}"
                );
            }
        });
    }

    // ---- K-SOUND-EML: consistency proof soundness ----

    #[test]
    fn k_sound_single_algorithm() {
        smol::block_on(async {
            let mut log = Log::new(MemoryStorage::new());
            log.add_algorithm(0, Box::new(Sha256Hasher)).await.unwrap();

            // Build up to size 8, checking consistency at each step.
            let mut roots: Vec<Vec<u8>> = Vec::new();
            for i in 0..8u8 {
                log.append(&[i]).await.unwrap();
                roots.push(log.root(0).unwrap());
            }

            let current_root = log.root(0).unwrap();

            for old_size in 1..8u64 {
                let proof = log.consistency_proof(0, old_size).await.unwrap();
                let old_root = &roots[(old_size - 1) as usize];
                assert!(
                    crate::proof::verify_consistency(
                        &Sha256Hasher,
                        &proof,
                        old_root,
                        &current_root
                    ),
                    "K-SOUND-EML failed for old_size={old_size}"
                );
            }
        });
    }

    // ---- T-BOUND: proof-level temporal binding ----

    #[test]
    fn t_bound_inclusion_proof_at_null_position() {
        smol::block_on(async {
            let mut log = Log::new(MemoryStorage::new());
            log.add_algorithm(0, Box::new(Sha256Hasher)).await.unwrap();

            for i in 0..4u8 {
                log.append(&[i]).await.unwrap();
            }

            // Add alg 1 at index 4 — indices 0..4 are null for alg 1.
            log.add_algorithm(1, Box::new(AltHasher)).await.unwrap();

            for i in 4..8u8 {
                log.append(&[i]).await.unwrap();
            }

            let root = log.root(1).unwrap();

            // Get the inclusion proof at a null-prefix position.
            let proof = log.inclusion_proof(1, 0).await.unwrap();

            // The proof DOES verify with the null leaf hash (this is correct —
            // the tree genuinely contains N₀ at position 0).
            let null_leaf = AltHasher.null();
            assert!(
                crate::proof::verify_inclusion(&AltHasher, &null_leaf, &proof, &root),
                "null leaf should verify at null position"
            );

            // But no real payload can produce a valid proof at that position.
            // T-BOUND: ∄ d. verify_inclusion(leaf(a, d), proof, root) = true
            for d in [b"any".as_slice(), b"data", b"", &[0], &[1], &[2], &[3]] {
                let forged_leaf = AltHasher.leaf(d);
                assert!(
                    !crate::proof::verify_inclusion(&AltHasher, &forged_leaf, &proof, &root),
                    "T-BOUND violated: real leaf verified at null position for data {:?}",
                    d
                );
            }
        });
    }

    // ---- Proof error cases ----

    #[test]
    fn inclusion_proof_out_of_bounds() {
        smol::block_on(async {
            let mut log = Log::new(MemoryStorage::new());
            log.add_algorithm(0, Box::new(Sha256Hasher)).await.unwrap();
            log.append(b"data").await.unwrap();

            let err = log.inclusion_proof(0, 1).await.unwrap_err();
            assert_eq!(
                err,
                Error::IndexOutOfBounds {
                    index: 1,
                    tree_size: 1
                }
            );
        });
    }

    #[test]
    fn consistency_proof_bounds() {
        smol::block_on(async {
            let mut log = Log::new(MemoryStorage::new());
            log.add_algorithm(0, Box::new(Sha256Hasher)).await.unwrap();
            for i in 0..4u8 {
                log.append(&[i]).await.unwrap();
            }

            // old_size = 0 is invalid.
            let err = log.consistency_proof(0, 0).await.unwrap_err();
            assert_eq!(
                err,
                Error::IndexOutOfBounds {
                    index: 0,
                    tree_size: 4
                }
            );

            // old_size >= tree_size is invalid.
            let err = log.consistency_proof(0, 4).await.unwrap_err();
            assert_eq!(
                err,
                Error::IndexOutOfBounds {
                    index: 4,
                    tree_size: 4
                }
            );
        });
    }

    // ---- EML Manifest (Definition 13) ----

    #[test]
    fn algorithms_returns_manifest_data() {
        smol::block_on(async {
            let mut log = Log::new(MemoryStorage::new());
            log.add_algorithm(0, Box::new(Sha256Hasher)).await.unwrap();

            for i in 0..4u8 {
                log.append(&[i]).await.unwrap();
            }

            // Add alg 1, then freeze alg 0.
            log.add_algorithm(1, Box::new(AltHasher)).await.unwrap();
            log.remove_algorithm(0).await.unwrap();

            for i in 4..8u8 {
                log.append(&[i]).await.unwrap();
            }

            let infos = log.algorithms().await;
            assert_eq!(infos.len(), 2);

            // Alg 0: frozen at index 4, activated at 0.
            let a0 = infos.iter().find(|a| a.id == 0).unwrap();
            assert_eq!(a0.activation_index, 0);
            assert_eq!(a0.deactivation_index, Some(4));
            assert_eq!(a0.tree_size, 4);
            assert_eq!(a0.root, log.root(0).unwrap());

            let expected_a0_serialized = serialize_epochs(&[(0, 4)]);
            let expected_a0_hash = Sha256Hasher.hash(&expected_a0_serialized);
            assert_eq!(a0.manifest_hash, expected_a0_hash);

            // Alg 1: active, activated at 4.
            let a1 = infos.iter().find(|a| a.id == 1).unwrap();
            assert_eq!(a1.activation_index, 4);
            assert_eq!(a1.deactivation_index, None);
            assert_eq!(a1.tree_size, 8); // global tree size
            assert_eq!(a1.root, log.root(1).unwrap());

            let expected_a1_serialized = serialize_epochs(&[(4, u64::MAX)]);
            let expected_a1_hash = AltHasher.hash(&expected_a1_serialized);
            assert_eq!(a1.manifest_hash, expected_a1_hash);
        });
    }

    // ====================================================================
    // Reactivation tests
    // ====================================================================

    #[test]
    fn resume_basic_a_equiv() {
        smol::block_on(async {
            // Add alg 0 at genesis, append 4, freeze, append 4 more, resume, append 4.
            // Alg 1 (keeper) stays active throughout to permit appends.
            let mut log = Log::new(MemoryStorage::new());
            log.add_algorithm(0, Box::new(Sha256Hasher)).await.unwrap();
            log.add_algorithm(1, Box::new(AltHasher)).await.unwrap();

            for i in 0..4u8 {
                log.append(&[i]).await.unwrap();
            }
            log.remove_algorithm(0).await.unwrap();
            for i in 4..8u8 {
                log.append(&[i]).await.unwrap();
            }
            log.resume_algorithm(0).await.unwrap();
            for i in 8..12u8 {
                log.append(&[i]).await.unwrap();
            }

            // A-EQUIV: incremental root must equal batch root.
            let root = log.root(0).unwrap();
            let projected = log.project(0).await.unwrap();

            let batch_root = crate::proof::mth(&Sha256Hasher, &projected);
            assert_eq!(root, batch_root, "A-EQUIV violated after resume");
        });
    }

    #[test]
    fn resume_a_stack_invariant() {
        smol::block_on(async {
            let mut log = Log::new(MemoryStorage::new());
            log.add_algorithm(0, Box::new(Sha256Hasher)).await.unwrap();
            log.add_algorithm(1, Box::new(AltHasher)).await.unwrap();

            for i in 0..3u8 {
                log.append(&[i]).await.unwrap();
            }
            log.remove_algorithm(0).await.unwrap();
            for i in 3..8u8 {
                log.append(&[i]).await.unwrap();
            }
            log.resume_algorithm(0).await.unwrap();
            for i in 8..13u8 {
                log.append(&[i]).await.unwrap();
            }

            // A-STACK: stack length == popcount(tree_size)
            let ts = log.tree_size(0).await.unwrap();
            let expected_len = ts.count_ones() as usize;
            assert_eq!(
                log.stack_len(0).unwrap(),
                expected_len,
                "A-STACK violated after resume: tree_size={ts}"
            );
        });
    }

    #[test]
    fn resume_error_active_algorithm() {
        smol::block_on(async {
            let mut log = Log::new(MemoryStorage::new());
            log.add_algorithm(0, Box::new(Sha256Hasher)).await.unwrap();
            log.append(b"a").await.unwrap();

            let err = log.resume_algorithm(0).await.unwrap_err();
            assert_eq!(err, Error::AlgorithmActive(0));
        });
    }

    #[test]
    fn resume_error_unknown_algorithm() {
        smol::block_on(async {
            let mut log = Log::new(MemoryStorage::new());
            log.add_algorithm(0, Box::new(Sha256Hasher)).await.unwrap();

            let err = log.resume_algorithm(99).await.unwrap_err();
            assert_eq!(err, Error::UnknownAlgorithm(99));
        });
    }

    #[test]
    fn resume_inclusion_proof_soundness() {
        smol::block_on(async {
            let mut log = Log::new(MemoryStorage::new());
            log.add_algorithm(0, Box::new(Sha256Hasher)).await.unwrap();
            log.add_algorithm(1, Box::new(AltHasher)).await.unwrap();

            // Epoch 1: leaves 0..4
            for i in 0..4u8 {
                log.append(&[i]).await.unwrap();
            }
            log.remove_algorithm(0).await.unwrap();

            // Gap: leaves 4..8 (null for alg 0)
            for i in 4..8u8 {
                log.append(&[i]).await.unwrap();
            }
            log.resume_algorithm(0).await.unwrap();

            // Epoch 2: leaves 8..12
            for i in 8..12u8 {
                log.append(&[i]).await.unwrap();
            }

            let root = log.root(0).unwrap();
            let projected = log.project(0).await.unwrap();

            // I-SOUND: proofs verify for all active positions.
            for &idx in &[0u64, 1, 2, 3, 8, 9, 10, 11] {
                let proof = log.inclusion_proof(0, idx).await.unwrap();
                assert!(
                    crate::verify_inclusion(&Sha256Hasher, &projected[idx as usize], &proof, &root),
                    "I-SOUND failed at active index {idx}"
                );
            }

            // Null positions (4..8) also produce valid proofs (over null leaf).
            for idx in 4..8u64 {
                let proof = log.inclusion_proof(0, idx).await.unwrap();
                assert!(
                    crate::verify_inclusion(&Sha256Hasher, &projected[idx as usize], &proof, &root),
                    "proof at null gap position {idx} failed"
                );
            }
        });
    }

    #[test]
    fn resume_consistency_proof_soundness() {
        smol::block_on(async {
            let mut log = Log::new(MemoryStorage::new());
            log.add_algorithm(0, Box::new(Sha256Hasher)).await.unwrap();
            log.add_algorithm(1, Box::new(AltHasher)).await.unwrap();

            for i in 0..4u8 {
                log.append(&[i]).await.unwrap();
            }
            let root_at_4 = log.root(0).unwrap();

            log.remove_algorithm(0).await.unwrap();
            for i in 4..8u8 {
                log.append(&[i]).await.unwrap();
            }
            log.resume_algorithm(0).await.unwrap();
            for i in 8..12u8 {
                log.append(&[i]).await.unwrap();
            }

            // K-SOUND: consistency from size 4 to current.
            let proof = log.consistency_proof(0, 4).await.unwrap();
            let root_now = log.root(0).unwrap();
            assert!(
                crate::verify_consistency(&Sha256Hasher, &proof, &root_at_4, &root_now),
                "K-SOUND failed after resume"
            );
        });
    }

    #[test]
    fn resume_consistency_across_gap() {
        smol::block_on(async {
            // Epoch 1: [0,4), gap: [4,8), epoch 2: [8,12).
            // Test consistency for EVERY old_size 1..12, including mid-gap positions.
            let mut log = Log::new(MemoryStorage::new());
            log.add_algorithm(0, Box::new(Sha256Hasher)).await.unwrap();
            log.add_algorithm(1, Box::new(AltHasher)).await.unwrap();

            for i in 0..4u8 {
                log.append(&[i]).await.unwrap();
            }
            log.remove_algorithm(0).await.unwrap();
            for i in 4..8u8 {
                log.append(&[i]).await.unwrap();
            }
            log.resume_algorithm(0).await.unwrap();
            for i in 8..12u8 {
                log.append(&[i]).await.unwrap();
            }

            let root_now = log.root(0).unwrap();
            let projected = log.project(0).await.unwrap();

            for old_size in 1..12u64 {
                let old_root = crate::proof::mth(&Sha256Hasher, &projected[..old_size as usize]);
                let proof = log.consistency_proof(0, old_size).await.unwrap();
                assert!(
                    crate::verify_consistency(&Sha256Hasher, &proof, &old_root, &root_now),
                    "K-SOUND across gap failed for old_size={old_size}"
                );
            }
        });
    }

    #[test]
    fn resume_epochs_metadata() {
        smol::block_on(async {
            let mut log = Log::new(MemoryStorage::new());
            log.add_algorithm(0, Box::new(Sha256Hasher)).await.unwrap();
            log.add_algorithm(1, Box::new(AltHasher)).await.unwrap();

            for i in 0..4u8 {
                log.append(&[i]).await.unwrap();
            }
            log.remove_algorithm(0).await.unwrap();
            for i in 4..8u8 {
                log.append(&[i]).await.unwrap();
            }
            log.resume_algorithm(0).await.unwrap();

            let epochs = log.epochs(0).unwrap();
            assert_eq!(epochs.len(), 2);
            assert_eq!(epochs[0], (0, Some(4)));
            assert_eq!(epochs[1], (8, None));

            assert_eq!(log.activation_index(0).unwrap(), 0);
            assert_eq!(log.deactivation_index(0).unwrap(), None); // currently active
        });
    }

    #[test]
    fn resume_large_gap_o_log_g() {
        smol::block_on(async {
            // Stress test: gap of 2^16 = 65536 null leaves.
            // With O(G) this would require 65536 iterations; with O(log G)
            // via reconstruct_frontier it completes in ~16 subtree_root calls.
            let mut log = Log::new(MemoryStorage::new());
            log.add_algorithm(0, Box::new(Sha256Hasher)).await.unwrap();

            // Epoch 1: 8 active leaves.
            for i in 0..8u8 {
                log.append(&[i]).await.unwrap();
            }
            log.remove_algorithm(0).await.unwrap();

            // Gap: 2^16 leaves appended while alg 0 is frozen.
            // Need a second algorithm to accept appends.
            log.add_algorithm(1, Box::new(AltHasher)).await.unwrap();
            let gap_size: u64 = 1 << 16;
            for i in 0..gap_size {
                log.append(&(i as u32).to_le_bytes()).await.unwrap();
            }

            // Resume alg 0 across the large gap.
            log.resume_algorithm(0).await.unwrap();

            // Epoch 2: 4 more active leaves.
            for i in 0..4u8 {
                log.append(&[200 + i]).await.unwrap();
            }

            // A-EQUIV: root must match projection oracle.
            let root = log.root(0).unwrap();
            let projected = log.project(0).await.unwrap();
            let batch_root = crate::proof::mth(&Sha256Hasher, &projected);
            assert_eq!(root, batch_root, "A-EQUIV violated after large-gap resume");

            // A-STACK: stack length == popcount(tree_size).
            let ts = log.tree_size(0).await.unwrap();
            let expected_len = ts.count_ones() as usize;
            assert_eq!(
                log.stack_len(0).unwrap(),
                expected_len,
                "A-STACK violated after large-gap resume: tree_size={ts}"
            );
        });
    }

    #[test]
    fn resume_immediate_no_gap() {
        smol::block_on(async {
            // Resume immediately after freeze (gap = 0).
            let mut log = Log::new(MemoryStorage::new());
            log.add_algorithm(0, Box::new(Sha256Hasher)).await.unwrap();

            for i in 0..4u8 {
                log.append(&[i]).await.unwrap();
            }
            let root_before = log.root(0).unwrap();
            log.remove_algorithm(0).await.unwrap();
            log.resume_algorithm(0).await.unwrap();

            // Root should be unchanged — zero-gap fast-forward is identity.
            let root_after = log.root(0).unwrap();
            assert_eq!(root_before, root_after, "zero-gap resume changed root");
        });
    }

    #[derive(Debug)]
    struct TrackingStorage {
        inner: MemoryStorage,
        batch_write_calls: std::sync::Arc<std::sync::atomic::AtomicUsize>,
    }

    impl Storage for TrackingStorage {
        type Error = <MemoryStorage as Storage>::Error;

        async fn store_leaf(
            &mut self,
            index: u64,
            data: &[u8],
        ) -> std::result::Result<(), Self::Error> {
            self.inner.store_leaf(index, data).await
        }

        async fn get_leaf(&self, index: u64) -> std::result::Result<Vec<u8>, Self::Error> {
            self.inner.get_leaf(index).await
        }

        async fn len(&self) -> u64 {
            self.inner.len().await
        }

        async fn store_node(
            &mut self,
            alg_id: u64,
            left: u64,
            height: usize,
            hash: &[u8],
        ) -> std::result::Result<(), Self::Error> {
            self.inner.store_node(alg_id, left, height, hash).await
        }

        async fn get_node(
            &self,
            alg_id: u64,
            left: u64,
            height: usize,
        ) -> std::result::Result<Option<Vec<u8>>, Self::Error> {
            self.inner.get_node(alg_id, left, height).await
        }

        async fn store_algorithm_meta(
            &mut self,
            alg_id: u64,
            epochs: &[(u64, u64)],
        ) -> std::result::Result<(), Self::Error> {
            self.inner.store_algorithm_meta(alg_id, epochs).await
        }

        async fn load_algorithm_metas(
            &self,
        ) -> std::result::Result<crate::storage::AlgorithmMetas, Self::Error> {
            self.inner.load_algorithm_metas().await
        }

        async fn write_batch(
            &mut self,
            leaves: &[(u64, &[u8])],
            nodes: &[(u64, u64, usize, &[u8])],
        ) -> std::result::Result<(), Self::Error> {
            self.batch_write_calls
                .fetch_add(1, std::sync::atomic::Ordering::SeqCst);
            self.inner.write_batch(leaves, nodes).await
        }
    }

    #[test]
    fn resume_persists_mixed_nodes() {
        smol::block_on(async {
            let batch_write_calls = std::sync::Arc::new(std::sync::atomic::AtomicUsize::new(0));
            let tracking_storage = TrackingStorage {
                inner: MemoryStorage::new(),
                batch_write_calls: batch_write_calls.clone(),
            };

            let mut log = Log::new(tracking_storage);
            log.add_algorithm(0, Box::new(Sha256Hasher)).await.unwrap();

            // Epoch 1 active: 3 leaves (0, 1, 2).
            for i in 0..3u8 {
                log.append(&[i]).await.unwrap();
            }
            log.remove_algorithm(0).await.unwrap();

            // Gap: 5 leaves (3, 4, 5, 6, 7).
            // Need alt algorithm to accept appends.
            log.add_algorithm(1, Box::new(AltHasher)).await.unwrap();
            for i in 3..8u8 {
                log.append(&[i]).await.unwrap();
            }

            // Assert that batch writes occurred during single-element appends (since append
            // delegates to append_batch).
            let writes_before_resume = batch_write_calls.load(std::sync::atomic::Ordering::SeqCst);
            assert_eq!(
                writes_before_resume, 8,
                "Expected exactly 8 write_batch calls during single-element appends"
            );

            // Resume alg 0: total size = 8.
            log.resume_algorithm(0).await.unwrap();

            // Assert that exactly ONE additional write_batch call occurred for persisting mixed
            // nodes.
            let writes_after_resume = batch_write_calls.load(std::sync::atomic::Ordering::SeqCst);
            assert_eq!(
                writes_after_resume,
                writes_before_resume + 1,
                "resume_algorithm should call write_batch exactly once to persist all mixed nodes"
            );

            // Verify stored mixed nodes.
            // Under size 8 and deactivation 3, mixed nodes are:
            // - [0, 8) height 3
            // - [0, 4) height 2
            // - [2, 4) height 1
            // Active node [0, 2) height 1 is also persisted (from initial appends).
            let storage = log.into_storage().inner;
            assert!(
                storage.nodes.contains_key(&(0, 0, 3)),
                "mixed node [0, 8) height 3 not persisted"
            );
            assert!(
                storage.nodes.contains_key(&(0, 0, 2)),
                "mixed node [0, 4) height 2 not persisted"
            );
            assert!(
                storage.nodes.contains_key(&(0, 2, 1)),
                "mixed node [2, 4) height 1 not persisted"
            );
            assert!(
                storage.nodes.contains_key(&(0, 0, 1)),
                "active node [0, 2) height 1 missing"
            );

            // Reference check: Verify the node hashes are canonical and identical to the expected
            // EML tree.
            let h0 = Sha256Hasher.leaf(&[0]);
            let h1 = Sha256Hasher.leaf(&[1]);
            let h2 = Sha256Hasher.leaf(&[2]);
            let hn = Sha256Hasher.null();

            let n_0_2 = Sha256Hasher.node(&h0, &h1);
            let n_2_4 = Sha256Hasher.node(&h2, &hn);
            let n_4_6 = Sha256Hasher.node(&hn, &hn);
            let n_6_8 = Sha256Hasher.node(&hn, &hn);

            let n_0_4 = Sha256Hasher.node(&n_0_2, &n_2_4);
            let n_4_8 = Sha256Hasher.node(&n_4_6, &n_6_8);

            let n_0_8 = Sha256Hasher.node(&n_0_4, &n_4_8);

            assert_eq!(
                storage.nodes.get(&(0, 0, 3)),
                Some(&n_0_8),
                "Hash mismatch for mixed node [0, 8) height 3"
            );
            assert_eq!(
                storage.nodes.get(&(0, 0, 2)),
                Some(&n_0_4),
                "Hash mismatch for mixed node [0, 4) height 2"
            );
            assert_eq!(
                storage.nodes.get(&(0, 2, 1)),
                Some(&n_2_4),
                "Hash mismatch for mixed node [2, 4) height 1"
            );
        });
    }

    #[test]
    fn resume_elide_multi_epoch() {
        smol::block_on(async {
            // Build a scenario with a gap in the middle.
            // Epoch 1: [0, 4), gap: [4, 8), epoch 2: [8, 16).
            let mut log = Log::new(MemoryStorage::new());
            log.add_algorithm(0, Box::new(Sha256Hasher)).await.unwrap();
            log.add_algorithm(1, Box::new(AltHasher)).await.unwrap();

            for i in 0..4u8 {
                log.append(&[i]).await.unwrap();
            }
            log.remove_algorithm(0).await.unwrap();
            for i in 4..8u8 {
                log.append(&[i]).await.unwrap();
            }
            log.resume_algorithm(0).await.unwrap();
            for i in 8..16u8 {
                log.append(&[i]).await.unwrap();
            }

            let epochs = log.epochs(0).unwrap();
            let root = log.root(0).unwrap();

            // Proof for leaf in epoch 2 (index 10).
            let full_proof = log.inclusion_proof(0, 10).await.unwrap();
            let projected = log.project(0).await.unwrap();
            assert!(crate::verify_inclusion(
                &Sha256Hasher,
                &projected[10],
                &full_proof,
                &root
            ));

            let elided = crate::elide_inclusion_proof(&full_proof, &epochs);
            let rehydrated = crate::rehydrate_inclusion_proof(&elided, &Sha256Hasher);
            assert_eq!(rehydrated, full_proof, "multi-epoch elide roundtrip failed");
            assert!(crate::verify_inclusion(
                &Sha256Hasher,
                &projected[10],
                &rehydrated,
                &root
            ));
        });
    }

    // ====================================================================
    // from_storage: cold reconstruction tests
    // ====================================================================

    /// Round-trip: build a log, extract storage, reconstruct, verify roots match.
    #[test]
    fn from_storage_single_algorithm() {
        smol::block_on(async {
            let mut log = Log::new(MemoryStorage::new());
            log.add_algorithm(0, Box::new(Sha256Hasher)).await.unwrap();

            for i in 0..20u8 {
                log.append(&[i]).await.unwrap();
            }

            let original_root = log.root(0).unwrap();
            let original_size = log.size().await;
            let original_algos = log.algorithms().await;

            let storage = log.into_storage();
            let reconstructed = Log::from_storage(storage, vec![(0, Box::new(Sha256Hasher))])
                .await
                .unwrap();

            assert_eq!(reconstructed.size().await, original_size);
            assert_eq!(reconstructed.root(0).unwrap(), original_root);
            assert_eq!(reconstructed.algorithms().await, original_algos);
        });
    }

    /// Multi-algorithm round-trip with one active and one frozen algorithm.
    #[test]
    fn from_storage_multi_algorithm_frozen_active() {
        smol::block_on(async {
            let mut log = Log::new(MemoryStorage::new());
            log.add_algorithm(0, Box::new(Sha256Hasher)).await.unwrap();
            log.add_algorithm(1, Box::new(Sha256Hasher)).await.unwrap();

            for i in 0..10u8 {
                log.append(&[i]).await.unwrap();
            }

            // Freeze algorithm 1.
            log.remove_algorithm(1).await.unwrap();

            for i in 10..20u8 {
                log.append(&[i]).await.unwrap();
            }

            let root0 = log.root(0).unwrap();
            let root1 = log.root(1).unwrap();
            let algos = log.algorithms().await;

            let storage = log.into_storage();
            let reconstructed = Log::from_storage(
                storage,
                vec![(0, Box::new(Sha256Hasher)), (1, Box::new(Sha256Hasher))],
            )
            .await
            .unwrap();

            assert_eq!(reconstructed.root(0).unwrap(), root0);
            assert_eq!(reconstructed.root(1).unwrap(), root1);
            assert_eq!(reconstructed.algorithms().await, algos);
        });
    }

    /// Resume-after-gap round-trip: algorithm deactivated, gap grows, resumed.
    #[test]
    fn from_storage_resume_after_gap() {
        smol::block_on(async {
            let mut log = Log::new(MemoryStorage::new());
            log.add_algorithm(0, Box::new(Sha256Hasher)).await.unwrap();

            for i in 0..4u8 {
                log.append(&[i]).await.unwrap();
            }
            log.remove_algorithm(0).await.unwrap();

            // Add a second algorithm to keep appends going.
            log.add_algorithm(1, Box::new(Sha256Hasher)).await.unwrap();
            for i in 4..8u8 {
                log.append(&[i]).await.unwrap();
            }

            log.resume_algorithm(0).await.unwrap();
            for i in 8..16u8 {
                log.append(&[i]).await.unwrap();
            }

            let root0 = log.root(0).unwrap();
            let root1 = log.root(1).unwrap();
            let algos = log.algorithms().await;

            let storage = log.into_storage();
            let reconstructed = Log::from_storage(
                storage,
                vec![(0, Box::new(Sha256Hasher)), (1, Box::new(Sha256Hasher))],
            )
            .await
            .unwrap();

            assert_eq!(reconstructed.root(0).unwrap(), root0);
            assert_eq!(reconstructed.root(1).unwrap(), root1);
            assert_eq!(reconstructed.algorithms().await, algos);
        });
    }

    /// After reconstruction, continued appends must produce identical state
    /// as a log that was never interrupted.
    #[test]
    fn from_storage_continued_appends() {
        smol::block_on(async {
            // Build original log with 10 leaves.
            let mut original = Log::new(MemoryStorage::new());
            original
                .add_algorithm(0, Box::new(Sha256Hasher))
                .await
                .unwrap();
            for i in 0..10u8 {
                original.append(&[i]).await.unwrap();
            }

            // Reconstruct at leaf 10.
            let storage = original.into_storage();
            let mut reconstructed = Log::from_storage(storage, vec![(0, Box::new(Sha256Hasher))])
                .await
                .unwrap();

            // Build a reference log with the same 10 leaves.
            let mut reference = Log::new(MemoryStorage::new());
            reference
                .add_algorithm(0, Box::new(Sha256Hasher))
                .await
                .unwrap();
            for i in 0..10u8 {
                reference.append(&[i]).await.unwrap();
            }

            // Append 10 more leaves to both.
            for i in 10..20u8 {
                reconstructed.append(&[i]).await.unwrap();
                reference.append(&[i]).await.unwrap();
            }

            assert_eq!(reconstructed.root(0).unwrap(), reference.root(0).unwrap());
            assert_eq!(reconstructed.size().await, reference.size().await);
        });
    }

    /// Error: metadata exists but no hasher provided.
    #[test]
    fn from_storage_error_orphaned_metadata() {
        smol::block_on(async {
            let mut log = Log::new(MemoryStorage::new());
            log.add_algorithm(0, Box::new(Sha256Hasher)).await.unwrap();
            log.append(b"data").await.unwrap();

            let storage = log.into_storage();
            let result = Log::from_storage(storage, vec![]).await;
            assert_eq!(result.unwrap_err(), Error::OrphanedMetadata(0));
        });
    }

    /// Error: hasher provided for non-existent algorithm.
    #[test]
    fn from_storage_error_unknown_metadata() {
        smol::block_on(async {
            let mut log = Log::new(MemoryStorage::new());
            log.add_algorithm(0, Box::new(Sha256Hasher)).await.unwrap();
            log.append(b"data").await.unwrap();

            let storage = log.into_storage();
            let result = Log::from_storage(
                storage,
                vec![(0, Box::new(Sha256Hasher)), (99, Box::new(Sha256Hasher))],
            )
            .await;
            assert_eq!(result.unwrap_err(), Error::UnknownMetadata(99));
        });
    }

    /// Error: metadata is corrupted (invalid epoch boundaries).
    #[test]
    fn from_storage_error_corrupted_metadata() {
        smol::block_on(async {
            let mut storage = MemoryStorage::new();
            // Store invalid epochs where start > end (10 > 5).
            storage.store_algorithm_meta(0, &[(10, 5)]).await.unwrap();

            let result = Log::from_storage(storage, vec![(0, Box::new(Sha256Hasher))]).await;
            assert!(matches!(
                result.unwrap_err(),
                Error::CorruptedMetadata {
                    alg_id: 0,
                    ref reason
                } if reason.contains("epoch start 10 exceeds end 5")
            ));
        });
    }

    /// Edge case: reconstruction of an empty log with no algorithms.
    #[test]
    fn from_storage_empty_log() {
        smol::block_on(async {
            let log = Log::new(MemoryStorage::new());
            let storage = log.into_storage();
            let reconstructed = Log::<MemoryStorage>::from_storage(storage, vec![])
                .await
                .unwrap();
            assert_eq!(reconstructed.size().await, 0);
            assert!(reconstructed.algorithms().await.is_empty());
        });
    }

    /// Various tree sizes to exercise different bit patterns in frontier
    /// reconstruction (powers of two, odd sizes, etc.).
    #[test]
    fn from_storage_various_sizes() {
        smol::block_on(async {
            for n in [1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 33, 63, 64, 100] {
                let mut log = Log::new(MemoryStorage::new());
                log.add_algorithm(0, Box::new(Sha256Hasher)).await.unwrap();
                for i in 0..n {
                    log.append(&(i as u64).to_le_bytes()).await.unwrap();
                }

                let original_root = log.root(0).unwrap();
                let storage = log.into_storage();
                let reconstructed = Log::from_storage(storage, vec![(0, Box::new(Sha256Hasher))])
                    .await
                    .unwrap();

                assert_eq!(
                    reconstructed.root(0).unwrap(),
                    original_root,
                    "root mismatch for n={n}"
                );
            }
        });
    }
}
