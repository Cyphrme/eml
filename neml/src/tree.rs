//! Unified n-ary Merkle append-only log state machine.

use crate::error::Result;
use crate::hasher::Hasher;
use crate::mr::{evaluate, nary_mr};
use crate::schedule::reduction_count;
use crate::storage::Storage;
use crate::subtree::Subtree;

/// Configuration for the n-ary Merkle tree.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TreeConfig {
    /// Arity for log-level nodes (k >= 2).
    /// Controls the base-k carry reduction schedule.
    pub log_arity: usize,
}

impl Default for TreeConfig {
    fn default() -> Self {
        Self { log_arity: 2 }
    }
}

/// State of a registered hashing algorithm.
#[derive(Debug)]
pub struct AlgState {
    /// Hasher instance.
    pub hasher: Box<dyn Hasher>,
    /// Epoch intervals: half-open `[start, end)`.
    /// `end == u64::MAX` represents an active (open) epoch.
    pub epochs: Vec<(u64, u64)>,
    /// Frontier stack: holds hashes of completed subtrees.
    pub frontier: Vec<Vec<u8>>,
    /// Coordinates of each frontier node: `(left_index, height)`.
    pub frontier_coords: Vec<(u64, u32)>,
}

impl Clone for AlgState {
    fn clone(&self) -> Self {
        Self {
            hasher: self.hasher.clone_box(),
            epochs: self.epochs.clone(),
            frontier: self.frontier.clone(),
            frontier_coords: self.frontier_coords.clone(),
        }
    }
}

impl AlgState {
    /// Whether this algorithm is currently active (not frozen).
    pub fn is_active(&self) -> bool {
        self.epochs.last().is_some_and(|&(_, end)| end == u64::MAX)
    }

    /// Whether leaf/subtree index `i` falls within any of this algorithm's active epochs.
    pub fn is_active_at(&self, i: u64) -> bool {
        self.epochs
            .iter()
            .any(|&(start, end)| start <= i && i < end)
    }

    /// The tree size for this algorithm.
    ///
    /// Active algorithms track the global tree size.
    /// Frozen algorithms stopped at their last deactivation point.
    pub fn tree_size(&self, global_size: u64) -> u64 {
        if self.is_active() {
            global_size
        } else {
            self.epochs.last().map_or(0, |&(_, end)| end)
        }
    }

    /// The activation index of the first epoch.
    pub fn first_activation(&self) -> u64 {
        self.epochs.first().map_or(0, |&(start, _)| start)
    }

    /// Whether algorithm has active content in the half-open range `[lo, hi)`.
    ///
    /// Definition 14b (Active range): true iff any epoch overlaps the interval.
    pub fn active_range(&self, lo: u64, hi: u64) -> bool {
        self.epochs
            .iter()
            .any(|&(start, end)| start < hi && end > lo)
    }

    /// Whether the range `[lo, hi)` is fully contained within the active epochs.
    pub fn fully_active(&self, lo: u64, hi: u64) -> bool {
        self.epochs
            .iter()
            .any(|&(start, end)| start <= lo && hi <= end)
    }
}

/// An n-ary Merkle Append-Only Log.
#[derive(Debug, Clone)]
pub struct NaryMerkleLog<S: Storage> {
    storage: S,
    config: TreeConfig,
    algs: std::collections::HashMap<u64, AlgState>,
    /// Number of leaves appended (Flat Log Mode).
    size: u64,
    /// Number of subtrees appended.
    subtree_count: u64,
}

impl<S: Storage> NaryMerkleLog<S> {
    /// Create a new empty n-ary Merkle log.
    ///
    /// # Errors
    ///
    /// Returns a storage error or validation error if the initialization fails.
    pub async fn new(
        storage: S,
        hasher: Box<dyn Hasher>,
        config: TreeConfig,
    ) -> Result<Self, S::Error> {
        if config.log_arity < 2 || config.log_arity > 256 {
            return Err(crate::error::Error::CorruptedMetadata {
                alg_id: 0,
                reason: format!(
                    "invalid log_arity: must be between 2 and 256, got {}",
                    config.log_arity
                ),
            });
        }
        let mut log = Self {
            storage,
            config,
            algs: std::collections::HashMap::new(),
            size: 0,
            subtree_count: 0,
        };
        // Eagerly register algorithm 0 as active from index 0
        log.add_algorithm(0, hasher).await?;
        Ok(log)
    }

    /// Reconstruct an existing Merkle log from storage using the default configuration.
    ///
    /// # Errors
    ///
    /// Returns a storage error or validation error if the reconstruction fails.
    pub async fn from_storage(
        storage: S,
        hashers: Vec<(u64, Box<dyn Hasher>)>,
    ) -> Result<Self, S::Error> {
        Self::from_storage_with_config(storage, hashers, TreeConfig::default()).await
    }

    /// Reconstruct an existing Merkle log from storage with a specific configuration.
    ///
    /// # Errors
    ///
    /// Returns a storage error or validation error if the reconstruction fails.
    pub async fn from_storage_with_config(
        storage: S,
        hashers: Vec<(u64, Box<dyn Hasher>)>,
        config: TreeConfig,
    ) -> Result<Self, S::Error> {
        if config.log_arity < 2 || config.log_arity > 256 {
            return Err(crate::error::Error::CorruptedMetadata {
                alg_id: 0,
                reason: format!(
                    "invalid log_arity: must be between 2 and 256, got {}",
                    config.log_arity
                ),
            });
        }

        let metas = storage
            .load_algorithm_metas()
            .await
            .map_err(crate::error::Error::Storage)?;

        let mut hasher_map: std::collections::HashMap<u64, Box<dyn Hasher>> =
            hashers.into_iter().collect();

        // Validate 1:1 correspondence and duplicate IDs.
        let mut seen = std::collections::HashSet::new();
        for &(alg_id, _) in &metas {
            if !seen.insert(alg_id) {
                return Err(crate::error::Error::DuplicateAlgorithm(alg_id));
            }
            if !hasher_map.contains_key(&alg_id) {
                return Err(crate::error::Error::OrphanedMetadata(alg_id));
            }
        }
        let meta_ids: std::collections::HashSet<u64> = metas.iter().map(|&(id, _)| id).collect();
        for &alg_id in hasher_map.keys() {
            if !meta_ids.contains(&alg_id) {
                return Err(crate::error::Error::UnknownMetadata(alg_id));
            }
        }

        let global_size = Self::determine_global_size(&storage, &metas).await?;

        let mut algs = std::collections::HashMap::new();
        let k = config.log_arity as u64;
        for (alg_id, epochs) in metas {
            let hasher = hasher_map
                .remove(&alg_id)
                .ok_or_else(|| crate::error::Error::OrphanedMetadata(alg_id))?;
            let state = Self::reconstruct_algorithm_state(
                &storage,
                alg_id,
                hasher,
                &epochs,
                global_size,
                k,
            )
            .await?;
            algs.insert(alg_id, state);
        }

        // Determine if we are in Flat Log Mode or Subtree Log Mode.
        let is_state_mode = storage.len().await > 0;
        let size = if is_state_mode { global_size } else { 0 };
        let subtree_count = if is_state_mode { 0 } else { global_size };

        Ok(Self {
            storage,
            config,
            algs,
            size,
            subtree_count,
        })
    }

    /// Probe storage to find the current global size.
    async fn determine_global_size(
        storage: &S,
        metas: &[(u64, Vec<(u64, u64)>)],
    ) -> Result<u64, S::Error> {
        let leaf_len = storage.len().await;
        if leaf_len > 0 {
            return Ok(leaf_len);
        }

        let mut max_frozen_end = 0;
        let mut active_algs = Vec::new();
        for &(alg_id, ref epochs) in metas {
            if let Some(&(start, end)) = epochs.last() {
                if end == u64::MAX {
                    active_algs.push((alg_id, start));
                } else if end > max_frozen_end {
                    max_frozen_end = end;
                }
            }
        }

        if active_algs.is_empty() {
            return Ok(max_frozen_end);
        }

        // Probe active algorithm to determine size.
        let (alg_id, start) = active_algs[0];
        let mut low = start;
        let mut high = start;
        loop {
            if storage
                .get_node(alg_id, high, 0)
                .await
                .map_err(crate::error::Error::Storage)?
                .is_none()
            {
                break;
            }
            if high == 0 {
                high = 1;
            } else {
                if let Some(new_high) = high.checked_mul(2) {
                    high = new_high;
                } else {
                    high = u64::MAX;
                    break;
                }
            }
        }

        let mut size = low;
        while low < high {
            let mid = low + (high - low) / 2;
            if storage
                .get_node(alg_id, mid, 0)
                .await
                .map_err(crate::error::Error::Storage)?
                .is_some()
            {
                size = mid + 1;
                low = mid + 1;
            } else {
                high = mid;
            }
        }
        Ok(size)
    }

    /// Reconstruct algorithm state from storage.
    async fn reconstruct_algorithm_state(
        storage: &S,
        alg_id: u64,
        hasher: Box<dyn Hasher>,
        epochs: &[(u64, u64)],
        global_size: u64,
        k: u64,
    ) -> Result<AlgState, S::Error> {
        Self::validate_epochs(alg_id, epochs, global_size)?;

        let is_active = epochs.last().is_some_and(|&(_, end)| end == u64::MAX);
        let tree_size = if is_active {
            global_size
        } else {
            epochs.last().map_or(0, |&(_, end)| end)
        };

        let mut state = AlgState {
            hasher,
            epochs: epochs.to_vec(),
            frontier: Vec::new(),
            frontier_coords: Vec::new(),
        };

        if tree_size == 0 {
            return Ok(state);
        }

        let coords = frontier_for_size(tree_size, k);
        let mut frontier = Vec::with_capacity(coords.len());
        for &(left, height) in &coords {
            let cap = k.pow(height);
            let hash = if !state.active_range(left, left + cap) {
                state.hasher.null()
            } else {
                storage
                    .get_node(alg_id, left, height)
                    .await
                    .map_err(crate::error::Error::Storage)?
                    .ok_or_else(|| {
                        crate::error::Error::CorruptedMetadata {
                            alg_id,
                            reason: format!(
                                "missing frontier node for algorithm {} at left {} height {}",
                                alg_id, left, height
                            ),
                        }
                    })?
            };
            frontier.push(hash);
        }

        state.frontier = frontier;
        state.frontier_coords = coords;

        Ok(state)
    }

    fn validate_epochs(
        alg_id: u64,
        epochs: &[(u64, u64)],
        global_size: u64,
    ) -> Result<(), S::Error> {
        if epochs.is_empty() {
            return Err(crate::error::Error::CorruptedMetadata {
                alg_id,
                reason: "epoch sequence is empty".to_string(),
            });
        }
        let mut last_end = 0;
        for (i, &(start, end)) in epochs.iter().enumerate() {
            if start > end {
                return Err(crate::error::Error::CorruptedMetadata {
                    alg_id,
                    reason: format!("epoch start {start} exceeds end {end}"),
                });
            }
            if start < last_end {
                return Err(crate::error::Error::CorruptedMetadata {
                    alg_id,
                    reason: format!("epoch start {start} is less than prior end {last_end}"),
                });
            }
            if end != u64::MAX && end > global_size {
                return Err(crate::error::Error::CorruptedMetadata {
                    alg_id,
                    reason: format!("epoch end {end} exceeds global size {global_size}"),
                });
            }
            if end == u64::MAX && i != epochs.len() - 1 {
                return Err(crate::error::Error::CorruptedMetadata {
                    alg_id,
                    reason: "open epoch (end = u64::MAX) is not the final entry".to_string(),
                });
            }
            last_end = end;
        }
        if let Some(&(start, end)) = epochs.last() {
            if end == u64::MAX && start > global_size {
                return Err(crate::error::Error::CorruptedMetadata {
                    alg_id,
                    reason: format!("active epoch start {start} exceeds global size {global_size}"),
                });
            }
        }
        Ok(())
    }

    /// Retrieve the tree configuration.
    #[must_use]
    pub fn config(&self) -> &TreeConfig {
        &self.config
    }

    /// Retrieve the number of leaves stored.
    #[must_use]
    pub fn size(&self) -> u64 {
        self.size
    }

    /// Retrieve the number of subtrees stored.
    #[must_use]
    pub fn subtree_count(&self) -> u64 {
        self.subtree_count
    }

    /// Access the frontier stack of the default algorithm (0).
    #[must_use]
    pub fn frontier(&self) -> &[Vec<u8>] {
        self.frontier_for(0).unwrap_or(&[])
    }

    /// Access the frontier stack of a specific algorithm.
    #[must_use]
    pub fn frontier_for(&self, alg_id: u64) -> Option<&[Vec<u8>]> {
        self.algs.get(&alg_id).map(|s| s.frontier.as_slice())
    }

    /// Consume the log and return the underlying storage backend.
    #[must_use]
    pub fn into_storage(self) -> S {
        self.storage
    }

    /// Borrow the underlying storage backend.
    #[must_use]
    pub fn storage(&self) -> &S {
        &self.storage
    }

    /// Borrow the underlying storage backend mutably.
    pub fn storage_mut(&mut self) -> &mut S {
        &mut self.storage
    }

    /// Register a new algorithm, activating it at the current tree size.
    pub async fn add_algorithm(
        &mut self,
        alg_id: u64,
        hasher: Box<dyn Hasher>,
    ) -> Result<(), S::Error> {
        if self.algs.contains_key(&alg_id) {
            return Err(crate::error::Error::DuplicateAlgorithm(alg_id));
        }

        let current_size = if self.size > 0 {
            self.size
        } else {
            self.subtree_count
        };

        let epochs = vec![(current_size, u64::MAX)];

        // Persist metadata BEFORE committing in-memory state.
        self.storage
            .store_algorithm_meta(alg_id, &epochs)
            .await
            .map_err(crate::error::Error::Storage)?;

        let k = self.config.log_arity as u64;
        let coords = frontier_for_size(current_size, k);
        let stack = vec![hasher.null(); coords.len()];

        self.algs.insert(
            alg_id,
            AlgState {
                hasher,
                epochs,
                frontier: stack,
                frontier_coords: coords,
            },
        );

        Ok(())
    }

    /// Deactivate (freeze) an algorithm at the current tree size.
    pub async fn remove_algorithm(&mut self, alg_id: u64) -> Result<(), S::Error> {
        let current_size = if self.size > 0 {
            self.size
        } else {
            self.subtree_count
        };

        let state = self
            .algs
            .get_mut(&alg_id)
            .ok_or(crate::error::Error::UnknownAlgorithm(alg_id))?;

        if !state.is_active() {
            return Err(crate::error::Error::FrozenAlgorithm(alg_id));
        }

        let mut new_epochs = state.epochs.clone();
        if let Some(last) = new_epochs.last_mut() {
            last.1 = current_size;
        }

        self.storage
            .store_algorithm_meta(alg_id, &new_epochs)
            .await
            .map_err(crate::error::Error::Storage)?;

        state.epochs = new_epochs;
        Ok(())
    }

    /// Reactivate a frozen algorithm at the current tree size.
    pub async fn resume_algorithm(&mut self, alg_id: u64) -> Result<(), S::Error> {
        let current_size = if self.size > 0 {
            self.size
        } else {
            self.subtree_count
        };

        let mut new_epochs = {
            let state = self
                .algs
                .get(&alg_id)
                .ok_or(crate::error::Error::UnknownAlgorithm(alg_id))?;

            if state.is_active() {
                return Err(crate::error::Error::AlgorithmActive(alg_id));
            }

            state.epochs.clone()
        };

        new_epochs.push((current_size, u64::MAX));

        let k = self.config.log_arity as u64;
        let coords = frontier_for_size(current_size, k);
        let mut frontier = Vec::with_capacity(coords.len());

        let temp_state = {
            let state = &self.algs[&alg_id];
            AlgState {
                hasher: state.hasher.clone_box(),
                epochs: new_epochs.clone(),
                frontier: Vec::new(),
                frontier_coords: Vec::new(),
            }
        };

        let mut mixed_to_store = Vec::new();
        for &(left, height) in &coords {
            let cap = k.pow(height);
            let (hash, mixed) = Self::reconstruct_subtree_root(
                &self.storage,
                alg_id,
                &temp_state,
                left,
                left + cap,
                k,
                true,
            )
            .await?;
            frontier.push(hash);
            mixed_to_store.extend(mixed);
        }

        let nodes_ref: Vec<(u64, u64, u32, &[u8])> = mixed_to_store
            .iter()
            .map(|&(left, height, ref hash)| (alg_id, left, height, hash.as_slice()))
            .collect();

        self.storage
            .write_batch(&[], &nodes_ref)
            .await
            .map_err(crate::error::Error::Storage)?;

        self.storage
            .store_algorithm_meta(alg_id, &new_epochs)
            .await
            .map_err(crate::error::Error::Storage)?;

        let state = self
            .algs
            .get_mut(&alg_id)
            .ok_or(crate::error::Error::UnknownAlgorithm(alg_id))?;
        state.epochs = new_epochs;
        state.frontier = frontier;
        state.frontier_coords = coords;

        Ok(())
    }

    /// Recursively resolve a subtree root and collect mixed boundary nodes.
    #[allow(clippy::type_complexity)]
    fn reconstruct_subtree_root<'a>(
        storage: &'a S,
        alg_id: u64,
        state: &'a AlgState,
        lo: u64,
        hi: u64,
        k: u64,
        store_mixed: bool,
    ) -> std::pin::Pin<
        Box<
            dyn std::future::Future<Output = Result<(Vec<u8>, Vec<(u64, u32, Vec<u8>)>), S::Error>>
                + Send
                + 'a,
        >,
    >
    where
        S: 'a,
    {
        Box::pin(async move {
            let size = hi - lo;
            if size == 0 {
                return Ok((state.hasher.empty(), Vec::new()));
            }
            if size == 1 {
                if state.is_active_at(lo) {
                    if storage.len().await == 0 {
                        if let Some(hash) = storage
                            .get_node(alg_id, lo, 0)
                            .await
                            .map_err(crate::error::Error::Storage)?
                        {
                            return Ok((hash, Vec::new()));
                        } else {
                            return Ok((state.hasher.null(), Vec::new()));
                        }
                    } else {
                        let data = storage
                            .get_leaf(lo)
                            .await
                            .map_err(crate::error::Error::Storage)?;
                        return Ok((state.hasher.leaf(&data), Vec::new()));
                    }
                }
                return Ok((state.hasher.null(), Vec::new()));
            }

            if !state.active_range(lo, hi) {
                return Ok((state.hasher.null(), Vec::new()));
            }

            let is_power_of_k = {
                let mut temp = size;
                while temp % k == 0 {
                    temp /= k;
                }
                temp == 1
            };

            if is_power_of_k {
                let height = {
                    let mut h = 0;
                    let mut temp = size;
                    while temp > 1 {
                        temp /= k;
                        h += 1;
                    }
                    h as u32
                };
                if state.fully_active(lo, hi) {
                    if let Some(hash) = storage
                        .get_node(alg_id, lo, height)
                        .await
                        .map_err(crate::error::Error::Storage)?
                    {
                        return Ok((hash, Vec::new()));
                    }
                }

                let child_size = size / k;
                let mut child_hashes = Vec::with_capacity(k as usize);
                let mut mixed_nodes = Vec::new();
                for j in 0..k {
                    let c_lo = lo + j * child_size;
                    let c_hi = lo + (j + 1) * child_size;
                    let (child_hash, child_mixed) = Self::reconstruct_subtree_root(
                        storage,
                        alg_id,
                        state,
                        c_lo,
                        c_hi,
                        k,
                        store_mixed,
                    )
                    .await?;
                    child_hashes.push(child_hash);
                    mixed_nodes.extend(child_mixed);
                }
                let child_refs: Vec<&[u8]> = child_hashes.iter().map(|c| c.as_slice()).collect();
                let hash = nary_mr(state.hasher.as_ref(), &child_refs);

                if store_mixed {
                    mixed_nodes.push((lo, height, hash.clone()));
                }
                Ok((hash, mixed_nodes))
            } else {
                let coords = frontier_for_size(size, k);
                let mut component_hashes = Vec::with_capacity(coords.len());
                let mut mixed_nodes = Vec::new();
                for &(part_left, part_height) in &coords {
                    let cap = k.pow(part_height);
                    let c_lo = lo + part_left;
                    let c_hi = c_lo + cap;
                    let (part_root, part_mixed) = Self::reconstruct_subtree_root(
                        storage,
                        alg_id,
                        state,
                        c_lo,
                        c_hi,
                        k,
                        store_mixed,
                    )
                    .await?;
                    component_hashes.push(part_root);
                    mixed_nodes.extend(part_mixed);
                }

                let mut current = component_hashes;
                let k_usize = k as usize;
                while current.len() > k_usize {
                    let split_idx = current.len() - k_usize;
                    let right_elements = &current[split_idx..];
                    let refs: Vec<&[u8]> = right_elements.iter().map(|v| v.as_slice()).collect();
                    let merged = nary_mr(state.hasher.as_ref(), &refs);
                    current.truncate(split_idx);
                    current.push(merged);
                }
                let refs: Vec<&[u8]> = current.iter().map(|v| v.as_slice()).collect();
                Ok((nary_mr(state.hasher.as_ref(), &refs), mixed_nodes))
            }
        })
    }

    /// Append a single leaf to the log (Flat Log Mode).
    pub async fn append_leaf(&mut self, data: &[u8]) -> Result<(), S::Error> {
        if self.subtree_count > 0 {
            return Err(crate::error::Error::CorruptedMetadata {
                alg_id: 0,
                reason: "cannot append leaf in Subtree Log Mode".to_string(),
            });
        }

        if self.size >= (1u64 << 47) {
            return Err(crate::error::Error::CorruptedMetadata {
                alg_id: 0,
                reason: "log capacity exceeded (max 2^47 items)".to_string(),
            });
        }

        if !self.algs.values().any(|s| s.is_active()) {
            return Err(crate::error::Error::NoActiveAlgorithms);
        }

        let mut temp_algs = self.algs.clone();
        let mut batch_leaves = Vec::new();
        let mut batch_nodes = Vec::new();

        batch_leaves.push((self.size, data));

        for (&alg_id, state) in &mut temp_algs {
            if !state.is_active() {
                continue;
            }

            let digest = if state.is_active_at(self.size) {
                let leaf_hash = state.hasher.leaf(data);
                batch_nodes.push((alg_id, self.size, 0, leaf_hash.clone()));
                leaf_hash
            } else {
                state.hasher.null()
            };

            state.frontier.push(digest);
            state.frontier_coords.push((self.size, 0));

            let merges = reduction_count(self.size, self.config.log_arity as u64);
            for _ in 0..merges {
                let mut children = Vec::with_capacity(self.config.log_arity);
                let mut coords = Vec::with_capacity(self.config.log_arity);
                for _ in 0..self.config.log_arity {
                    children.push(state.frontier.pop().ok_or_else(|| {
                        crate::error::Error::CorruptedMetadata {
                            alg_id,
                            reason: "frontier stack underflow during reduction".to_string(),
                        }
                    })?);
                    coords.push(state.frontier_coords.pop().ok_or_else(|| {
                        crate::error::Error::CorruptedMetadata {
                            alg_id,
                            reason: "frontier_coords stack underflow during reduction".to_string(),
                        }
                    })?);
                }
                children.reverse();
                coords.reverse();
                let child_refs: Vec<&[u8]> = children.iter().map(|c| c.as_slice()).collect();
                let parent = nary_mr(state.hasher.as_ref(), &child_refs);

                let parent_left_index = coords[0].0;
                let parent_height = coords[0].1 + 1;

                if parent != state.hasher.null() {
                    batch_nodes.push((alg_id, parent_left_index, parent_height, parent.clone()));
                }

                state.frontier.push(parent);
                state
                    .frontier_coords
                    .push((parent_left_index, parent_height));
            }
        }

        let nodes_ref: Vec<(u64, u64, u32, &[u8])> = batch_nodes
            .iter()
            .map(|&(alg_id, left, height, ref hash)| (alg_id, left, height, hash.as_slice()))
            .collect();

        self.storage
            .write_batch(&batch_leaves, &nodes_ref)
            .await
            .map_err(crate::error::Error::Storage)?;

        self.algs = temp_algs;
        self.size += 1;
        Ok(())
    }

    /// Append a structured subtree to the log (Subtree Log Mode).
    pub async fn append_subtree(&mut self, subtree: &Subtree) -> Result<(), S::Error> {
        if self.subtree_count >= (1u64 << 47) {
            return Err(crate::error::Error::CorruptedMetadata {
                alg_id: 0,
                reason: "log capacity exceeded (max 2^47 items)".to_string(),
            });
        }

        if !self.algs.values().any(|s| s.is_active()) {
            return Err(crate::error::Error::NoActiveAlgorithms);
        }

        let mut temp_algs = self.algs.clone();
        let mut batch_nodes = Vec::new();

        for (&alg_id, state) in &mut temp_algs {
            if !state.is_active() {
                continue;
            }

            let digest = if state.is_active_at(self.subtree_count) {
                let root_hash = evaluate(state.hasher.as_ref(), subtree);
                batch_nodes.push((alg_id, self.subtree_count, 0, root_hash.clone()));
                root_hash
            } else {
                state.hasher.null()
            };

            state.frontier.push(digest);
            state.frontier_coords.push((self.subtree_count, 0));

            let merges = reduction_count(self.subtree_count, self.config.log_arity as u64);
            for _ in 0..merges {
                let mut children = Vec::with_capacity(self.config.log_arity);
                let mut coords = Vec::with_capacity(self.config.log_arity);
                for _ in 0..self.config.log_arity {
                    children.push(state.frontier.pop().ok_or_else(|| {
                        crate::error::Error::CorruptedMetadata {
                            alg_id,
                            reason: "frontier stack underflow during reduction".to_string(),
                        }
                    })?);
                    coords.push(state.frontier_coords.pop().ok_or_else(|| {
                        crate::error::Error::CorruptedMetadata {
                            alg_id,
                            reason: "frontier_coords stack underflow during reduction".to_string(),
                        }
                    })?);
                }
                children.reverse();
                coords.reverse();
                let child_refs: Vec<&[u8]> = children.iter().map(|c| c.as_slice()).collect();
                let parent = nary_mr(state.hasher.as_ref(), &child_refs);

                let parent_left_index = coords[0].0;
                let parent_height = coords[0].1 + 1;

                if parent != state.hasher.null() {
                    batch_nodes.push((alg_id, parent_left_index, parent_height, parent.clone()));
                }

                state.frontier.push(parent);
                state
                    .frontier_coords
                    .push((parent_left_index, parent_height));
            }
        }

        let nodes_ref: Vec<(u64, u64, u32, &[u8])> = batch_nodes
            .iter()
            .map(|&(alg_id, left, height, ref hash)| (alg_id, left, height, hash.as_slice()))
            .collect();

        self.storage
            .write_batch(&[], &nodes_ref)
            .await
            .map_err(crate::error::Error::Storage)?;

        self.algs = temp_algs;
        self.subtree_count += 1;
        Ok(())
    }

    /// Compute the current root hash of the default algorithm (0).
    #[must_use]
    pub fn root(&self) -> Vec<u8> {
        self.root_for(0).unwrap_or_else(|_| Vec::new())
    }

    /// Compute the current root hash for a specific algorithm.
    pub fn root_for(&self, alg_id: u64) -> Result<Vec<u8>, S::Error> {
        let state = self
            .algs
            .get(&alg_id)
            .ok_or(crate::error::Error::UnknownAlgorithm(alg_id))?;

        if state.frontier.is_empty() {
            return Ok(state.hasher.empty());
        }
        if state.frontier.len() == 1 {
            return Ok(state.frontier[0].clone());
        }
        let k = self.config.log_arity;
        let mut current = state.frontier.clone();
        while current.len() > k {
            let split_idx = current.len() - k;
            let right_elements = &current[split_idx..];
            let refs: Vec<&[u8]> = right_elements.iter().map(|v| v.as_slice()).collect();
            let merged = nary_mr(state.hasher.as_ref(), &refs);
            current.truncate(split_idx);
            current.push(merged);
        }
        let refs: Vec<&[u8]> = current.iter().map(|v| v.as_slice()).collect();
        Ok(nary_mr(state.hasher.as_ref(), &refs))
    }

    /// Retrieve a node hash from storage, or return the null constant if it's inactive.
    async fn get_node_hash(
        &self,
        alg_id: u64,
        left: u64,
        height: u32,
    ) -> Result<Vec<u8>, S::Error> {
        let state = self
            .algs
            .get(&alg_id)
            .ok_or(crate::error::Error::UnknownAlgorithm(alg_id))?;
        let k = self.config.log_arity as u64;
        let cap = match k.checked_pow(height) {
            Some(c) => c,
            None => return Ok(state.hasher.null()),
        };
        let limit = match left.checked_add(cap) {
            Some(val) => val,
            None => return Ok(state.hasher.null()),
        };
        if !state.active_range(left, limit) {
            return Ok(state.hasher.null());
        }
        if let Some(hash) = self
            .storage
            .get_node(alg_id, left, height)
            .await
            .map_err(crate::error::Error::Storage)?
        {
            Ok(hash)
        } else if state.fully_active(left, limit) {
            Err(crate::error::Error::CorruptedMetadata {
                alg_id,
                reason: format!(
                    "missing internal node for algorithm {} at left {} height {}",
                    alg_id, left, height
                ),
            })
        } else {
            Ok(state.hasher.null())
        }
    }

    /// Generate an inclusion proof for the item at `index` in a tree of size `tree_size`.
    pub async fn inclusion_proof(
        &self,
        index: u64,
        tree_size: u64,
    ) -> Result<Option<crate::proof::InclusionProof>, S::Error> {
        self.inclusion_proof_for(0, index, tree_size).await
    }

    /// Generate an inclusion proof for a specific algorithm.
    pub async fn inclusion_proof_for(
        &self,
        alg_id: u64,
        index: u64,
        tree_size: u64,
    ) -> Result<Option<crate::proof::InclusionProof>, S::Error> {
        let state = self
            .algs
            .get(&alg_id)
            .ok_or(crate::error::Error::UnknownAlgorithm(alg_id))?;

        let max_size = state.tree_size(if self.size > 0 {
            self.size
        } else {
            self.subtree_count
        });

        if tree_size == 0 || index >= tree_size || tree_size > max_size {
            return Ok(None);
        }

        let k = self.config.log_arity as u64;
        let coords = frontier_for_size(tree_size, k);

        let mut target_f_idx = None;
        for (f_idx, &(left, height)) in coords.iter().enumerate() {
            let cap = k.pow(height);
            if index >= left && index < left + cap {
                target_f_idx = Some((f_idx, left, height));
                break;
            }
        }

        let (f_idx, left, height) = match target_f_idx {
            Some(val) => val,
            None => return Ok(None),
        };

        let mut path = Vec::new();
        self.log_level_bisection_path_to_height(alg_id, left, height, index, 0, &mut path)
            .await?;
        path.reverse();

        let mut hashes = Vec::with_capacity(coords.len());
        for &(l, h) in &coords {
            let hash = self.get_node_hash(alg_id, l, h).await?;
            hashes.push(hash);
        }

        struct MergeNode {
            hash: Vec<u8>,
            path: Vec<crate::proof::ProofStep>,
        }

        let mut current: Vec<MergeNode> = hashes
            .into_iter()
            .map(|h| MergeNode {
                hash: h,
                path: Vec::new(),
            })
            .collect();

        let mut target_idx = f_idx;
        let k_usize = self.config.log_arity;
        while current.len() > k_usize {
            let split_idx = current.len() - k_usize;

            let refs: Vec<&[u8]> = current[split_idx..]
                .iter()
                .map(|n| n.hash.as_slice())
                .collect();
            let merged_hash = nary_mr(state.hasher.as_ref(), &refs);

            let mut target_path = Vec::new();
            let mut is_target_merged = false;
            if target_idx >= split_idx {
                let mut siblings = Vec::with_capacity(k_usize - 1);
                for (j, item) in current.iter().enumerate().skip(split_idx) {
                    if j != target_idx {
                        siblings.push(item.hash.clone());
                    }
                }
                let step = crate::proof::ProofStep {
                    siblings,
                    position: target_idx - split_idx,
                };
                let mut p = std::mem::take(&mut current[target_idx].path);
                p.push(step);
                target_path = p;
                is_target_merged = true;
            }

            if is_target_merged {
                current.truncate(split_idx);
                current.push(MergeNode {
                    hash: merged_hash,
                    path: target_path,
                });
                target_idx = split_idx;
            } else {
                current.truncate(split_idx);
                current.push(MergeNode {
                    hash: merged_hash,
                    path: Vec::new(),
                });
            }
        }

        if current.len() > 1 {
            let mut siblings = Vec::with_capacity(current.len() - 1);
            for (j, item) in current.iter().enumerate() {
                if j != target_idx {
                    siblings.push(item.hash.clone());
                }
            }
            let step = crate::proof::ProofStep {
                siblings,
                position: target_idx,
            };
            current[target_idx].path.push(step);
        }

        path.extend(std::mem::take(&mut current[target_idx].path));

        Ok(Some(crate::proof::InclusionProof {
            index,
            tree_size,
            log_arity: self.config.log_arity as u64,
            path,
        }))
    }

    /// Generate a consistency proof between `old_size` and `new_size`.
    pub async fn consistency_proof(
        &self,
        old_size: u64,
        new_size: u64,
    ) -> Result<Option<crate::proof::ConsistencyProof>, S::Error> {
        self.consistency_proof_for(0, old_size, new_size).await
    }

    /// Generate a consistency proof for a specific algorithm.
    pub async fn consistency_proof_for(
        &self,
        alg_id: u64,
        old_size: u64,
        new_size: u64,
    ) -> Result<Option<crate::proof::ConsistencyProof>, S::Error> {
        let state = self
            .algs
            .get(&alg_id)
            .ok_or(crate::error::Error::UnknownAlgorithm(alg_id))?;

        let max_size = state.tree_size(if self.size > 0 {
            self.size
        } else {
            self.subtree_count
        });

        if old_size == 0 || old_size >= new_size || new_size > max_size {
            return Ok(None);
        }

        let k = self.config.log_arity as u64;
        let old_coords = frontier_for_size(old_size, k);
        let &(boundary_left, boundary_height) =
            old_coords
                .last()
                .ok_or_else(|| crate::error::Error::CorruptedMetadata {
                    alg_id,
                    reason: "empty old_coords for non-zero old_size".to_string(),
                })?;

        let start_hash = self
            .get_node_hash(alg_id, boundary_left, boundary_height)
            .await?;

        let new_coords = frontier_for_size(new_size, k);
        let mut target_new_f_idx = None;
        for (f_idx, &(new_left, new_height)) in new_coords.iter().enumerate() {
            let cap = k.pow(new_height);
            if boundary_left >= new_left && boundary_left < new_left + cap {
                target_new_f_idx = Some((f_idx, new_left, new_height));
                break;
            }
        }

        let (f_idx, left, height) = match target_new_f_idx {
            Some(val) => val,
            None => return Ok(None),
        };

        if height < boundary_height {
            return Ok(None);
        }

        let mut path = Vec::new();
        self.log_level_bisection_path_to_height(
            alg_id,
            left,
            height,
            boundary_left,
            boundary_height,
            &mut path,
        )
        .await?;
        path.reverse();

        let mut hashes = Vec::with_capacity(new_coords.len());
        for &(l, h) in &new_coords {
            let hash = self.get_node_hash(alg_id, l, h).await?;
            hashes.push(hash);
        }

        struct MergeNode {
            hash: Vec<u8>,
            path: Vec<crate::proof::ProofStep>,
        }

        let mut current: Vec<MergeNode> = hashes
            .into_iter()
            .map(|h| MergeNode {
                hash: h,
                path: Vec::new(),
            })
            .collect();

        let mut target_idx = f_idx;
        let k_usize = self.config.log_arity;
        while current.len() > k_usize {
            let split_idx = current.len() - k_usize;

            let refs: Vec<&[u8]> = current[split_idx..]
                .iter()
                .map(|n| n.hash.as_slice())
                .collect();
            let merged_hash = nary_mr(state.hasher.as_ref(), &refs);

            let mut target_path = Vec::new();
            let mut is_target_merged = false;
            if target_idx >= split_idx {
                let mut siblings = Vec::with_capacity(k_usize - 1);
                for (j, item) in current.iter().enumerate().skip(split_idx) {
                    if j != target_idx {
                        siblings.push(item.hash.clone());
                    }
                }
                let step = crate::proof::ProofStep {
                    siblings,
                    position: target_idx - split_idx,
                };
                let mut p = std::mem::take(&mut current[target_idx].path);
                p.push(step);
                target_path = p;
                is_target_merged = true;
            }

            if is_target_merged {
                current.truncate(split_idx);
                current.push(MergeNode {
                    hash: merged_hash,
                    path: target_path,
                });
                target_idx = split_idx;
            } else {
                current.truncate(split_idx);
                current.push(MergeNode {
                    hash: merged_hash,
                    path: Vec::new(),
                });
            }
        }

        if current.len() > 1 {
            let mut siblings = Vec::with_capacity(current.len() - 1);
            for (j, item) in current.iter().enumerate() {
                if j != target_idx {
                    siblings.push(item.hash.clone());
                }
            }
            let step = crate::proof::ProofStep {
                siblings,
                position: target_idx,
            };
            current[target_idx].path.push(step);
        }

        path.extend(std::mem::take(&mut current[target_idx].path));

        Ok(Some(crate::proof::ConsistencyProof {
            old_size,
            new_size,
            log_arity: k,
            start_hash,
            path,
        }))
    }

    async fn log_level_bisection_path_to_height(
        &self,
        alg_id: u64,
        left_index: u64,
        height: u32,
        target_index: u64,
        target_height: u32,
        path: &mut Vec<crate::proof::ProofStep>,
    ) -> Result<(), S::Error> {
        let mut curr_left = left_index;
        let mut curr_height = height;
        let k = self.config.log_arity as u64;

        while curr_height > target_height {
            let child_capacity = k.pow(curr_height - 1);
            let child_idx = (target_index - curr_left) / child_capacity;

            let mut siblings = Vec::with_capacity(self.config.log_arity - 1);
            for j in 0..self.config.log_arity {
                let j_u64 = j as u64;
                if j_u64 == child_idx {
                    continue;
                }
                let c_left = curr_left + j_u64 * child_capacity;
                let hash = self.get_node_hash(alg_id, c_left, curr_height - 1).await?;
                siblings.push(hash);
            }

            path.push(crate::proof::ProofStep {
                siblings,
                position: child_idx as usize,
            });

            curr_left += child_idx * child_capacity;
            curr_height -= 1;
        }
        Ok(())
    }

    /// Compute the current combined root hash of the default algorithm (0).
    pub async fn combined_root(&self) -> Vec<u8> {
        self.combined_root_for(0)
            .await
            .unwrap_or_else(|_| Vec::new())
    }

    /// Compute the current combined root hash for a specific algorithm.
    pub async fn combined_root_for(&self, alg_id: u64) -> Result<Vec<u8>, S::Error> {
        let tip_size = if self.size > 0 {
            self.size
        } else {
            self.subtree_count
        };
        self.combined_root_at(alg_id, tip_size).await
    }

    /// Compute the combined root hash for a specific algorithm at a historical tree size.
    pub async fn combined_root_at(&self, alg_id: u64, size: u64) -> Result<Vec<u8>, S::Error> {
        let state = self
            .algs
            .get(&alg_id)
            .ok_or(crate::error::Error::UnknownAlgorithm(alg_id))?;

        if size == 0 {
            return Ok(state.hasher.empty());
        }

        // 1. Gather active algorithms at the given historical size
        let mut active_algs = Vec::new();
        for (&id, alg_state) in &self.algs {
            if size > 0 && alg_state.is_active_at(size - 1) {
                active_algs.push(id);
            }
        }
        active_algs.sort_unstable();

        if active_algs.is_empty() {
            return Err(crate::error::Error::NoActiveAlgorithms);
        }

        // Ensure the requested algorithm is active at this size
        if !active_algs.contains(&alg_id) {
            return Err(crate::error::Error::FrozenAlgorithm(alg_id));
        }

        if active_algs.len() == 1 {
            // Singleton Promotion
            return self.root_for_at(active_algs[0], size).await;
        }

        // 2. Concatenate sorted active roots at size
        let mut buf = Vec::new();
        for &id in &active_algs {
            let r = self.root_for_at(id, size).await?;
            buf.extend_from_slice(&id.to_be_bytes());
            buf.extend_from_slice(&(r.len() as u64).to_be_bytes());
            buf.extend_from_slice(&r);
        }

        // 3. Hash the combined buffer using the target algorithm's hasher
        Ok(state.hasher.hash(&buf))
    }

    /// Retrieve the raw root hash for a specific algorithm at a historical tree size.
    pub async fn root_for_at(&self, alg_id: u64, size: u64) -> Result<Vec<u8>, S::Error> {
        let state = self
            .algs
            .get(&alg_id)
            .ok_or(crate::error::Error::UnknownAlgorithm(alg_id))?;

        let current_global_size = if self.size > 0 {
            self.size
        } else {
            self.subtree_count
        };

        if size > current_global_size {
            return Err(crate::error::Error::IndexOutOfBounds {
                index: size,
                tree_size: current_global_size,
            });
        }

        let alg_size = if size <= state.first_activation() {
            0
        } else if state.is_active_at(size - 1) {
            size
        } else {
            state
                .epochs
                .iter()
                .filter(|&&(_, end)| end < size)
                .map(|&(_, end)| end)
                .max()
                .unwrap_or(0)
        };

        if alg_size == 0 {
            return Ok(state.hasher.empty());
        }

        let k = self.config.log_arity;
        let coords = frontier_for_size(alg_size, k as u64);

        let mut frontier = Vec::with_capacity(coords.len());
        for &(left, height) in &coords {
            let hash = self.get_node_hash(alg_id, left, height).await?;
            frontier.push(hash);
        }

        if frontier.is_empty() {
            return Ok(state.hasher.empty());
        }
        if frontier.len() == 1 {
            return Ok(frontier[0].clone());
        }

        let mut current = frontier;
        while current.len() > k {
            let split_idx = current.len() - k;
            let right_elements = &current[split_idx..];
            let refs: Vec<&[u8]> = right_elements.iter().map(|v| v.as_slice()).collect();
            let merged = nary_mr(state.hasher.as_ref(), &refs);
            current.truncate(split_idx);
            current.push(merged);
        }
        let refs: Vec<&[u8]> = current.iter().map(|v| v.as_slice()).collect();
        Ok(nary_mr(state.hasher.as_ref(), &refs))
    }

    /// Verify that the trees for all active algorithms have not diverged
    /// from the underlying leaf data stored in the database.
    pub async fn verify_non_divergence(
        &self,
        checkpoint_size: Option<u64>,
        trusted_roots: &[(u64, Vec<u8>)],
    ) -> Result<bool, S::Error> {
        let start = checkpoint_size.unwrap_or(0);
        let end = if self.size > 0 {
            self.size
        } else {
            self.subtree_count
        };
        if start > end {
            return Ok(false);
        }

        // 1. If starting from a checkpoint, verify tree consistency first
        if start > 0 {
            for (&id, state) in &self.algs {
                let check_start = std::cmp::max(start, state.first_activation());
                if check_start < end {
                    let get_alg_size = |s_val: u64| {
                        if s_val <= state.first_activation() {
                            0
                        } else if state.is_active_at(s_val - 1) {
                            s_val
                        } else {
                            state
                                .epochs
                                .iter()
                                .filter(|&&(_, end)| end < s_val)
                                .map(|&(_, end)| end)
                                .max()
                                .unwrap_or(0)
                        }
                    };

                    let old_alg_size = get_alg_size(check_start);
                    let new_alg_size = get_alg_size(end);

                    let old_root = if old_alg_size == 0 {
                        state.hasher.empty()
                    } else {
                        // Trust boundary closed: retrieve starting root from trusted checkpoint
                        // parameter
                        let mut found = None;
                        for &(tid, ref r) in trusted_roots {
                            if tid == id {
                                found = Some(r.clone());
                                break;
                            }
                        }
                        found.ok_or(crate::error::Error::UnknownAlgorithm(id))?
                    };
                    let new_root = self.root_for_at(id, end).await?;

                    if old_alg_size < new_alg_size && old_alg_size > 0 {
                        // Verify consistency using standard O(log N) verification from old_alg_size
                        // to new_alg_size
                        if let Some(proof) = self
                            .consistency_proof_for(id, old_alg_size, new_alg_size)
                            .await?
                        {
                            if !crate::proof::verify_consistency(
                                state.hasher.as_ref(),
                                &proof,
                                &old_root,
                                &new_root,
                            ) {
                                return Ok(false);
                            }
                        } else {
                            return Ok(false);
                        }
                    } else if old_alg_size == new_alg_size {
                        // Ensure the root has not changed for frozen algorithms
                        if !crate::proof::constant_time_eq(&old_root, &new_root) {
                            return Ok(false);
                        }
                    }
                }
            }
        }

        // Helper helper to fold a frontier to its root.
        fn fold_frontier(hasher: &dyn Hasher, frontier: &[Vec<u8>], k: usize) -> Vec<u8> {
            if frontier.is_empty() {
                return hasher.empty();
            }
            if frontier.len() == 1 {
                return frontier[0].clone();
            }
            let mut current = frontier.to_vec();
            while current.len() > k {
                let split_idx = current.len() - k;
                let right_elements = &current[split_idx..];
                let refs: Vec<&[u8]> = right_elements.iter().map(|v| v.as_slice()).collect();
                let merged = nary_mr(hasher, &refs);
                current.truncate(split_idx);
                current.push(merged);
            }
            let refs: Vec<&[u8]> = current.iter().map(|v| v.as_slice()).collect();
            nary_mr(hasher, &refs)
        }

        // Reconstruct frontier stacks at checkpoint size and verify starting boundaries
        let mut alg_frontiers = std::collections::HashMap::new();
        for (&alg_id, state) in &self.algs {
            if !state.is_active() {
                let deact_index = state.epochs.last().map_or(0, |&(_, end)| end);
                if deact_index < end {
                    if self
                        .storage
                        .get_node(alg_id, deact_index, 0)
                        .await
                        .map_err(crate::error::Error::Storage)?
                        .is_some()
                    {
                        return Ok(false); // Tampered: nodes exist beyond deactivation point!
                    }
                }
            }

            let mut frontier = Vec::new();
            let mut frontier_coords = Vec::new();
            let k = self.config.log_arity;

            let alg_size_at_start = if start <= state.first_activation() {
                0
            } else if state.is_active_at(start - 1) {
                start
            } else {
                state
                    .epochs
                    .iter()
                    .filter(|&&(_, e)| e < start)
                    .map(|&(_, e)| e)
                    .max()
                    .unwrap_or(0)
            };

            if alg_size_at_start > 0 {
                let coords = frontier_for_size(alg_size_at_start, k as u64);
                for &(left, height) in &coords {
                    let hash = self.get_node_hash(alg_id, left, height).await?;
                    frontier.push(hash);
                    frontier_coords.push((left, height));
                }
            }

            if start > 0 {
                let folded = fold_frontier(state.hasher.as_ref(), &frontier, k);
                let mut expected_root = None;
                for &(tid, ref r) in trusted_roots {
                    if tid == alg_id {
                        expected_root = Some(r.clone());
                        break;
                    }
                }

                let expected_root = match expected_root {
                    Some(r) => r,
                    None => {
                        if alg_size_at_start == 0 {
                            state.hasher.empty()
                        } else {
                            return Err(crate::error::Error::UnknownAlgorithm(alg_id));
                        }
                    },
                };

                if !crate::proof::constant_time_eq(&folded, &expected_root) {
                    return Ok(false); // Starting state mismatch!
                }
            }

            alg_frontiers.insert(alg_id, (frontier, frontier_coords, alg_size_at_start));
        }

        // Stream leaf payloads from storage and rebuild stacks incrementally
        for i in start..end {
            let data = if self.size > 0 {
                match self.storage.get_leaf(i).await {
                    Ok(d) => Some(d),
                    Err(e) => return Err(crate::error::Error::Storage(e)),
                }
            } else {
                None
            };

            for (&alg_id, state) in &self.algs {
                let (frontier, frontier_coords, alg_size) = alg_frontiers
                    .get_mut(&alg_id)
                    .ok_or(crate::error::Error::UnknownAlgorithm(alg_id))?;

                let deact_index = if state.is_active() {
                    u64::MAX
                } else {
                    state.epochs.last().map_or(0, |&(_, end)| end)
                };

                if i >= deact_index {
                    continue;
                }

                let is_active = state.is_active_at(i);

                let digest = if is_active {
                    if let Some(ref d) = data {
                        state.hasher.leaf(d)
                    } else {
                        self.get_node_hash(alg_id, i, 0).await?
                    }
                } else {
                    state.hasher.null()
                };

                // Check leaf/subtree hash tampering
                let stored_leaf_hash = self.get_node_hash(alg_id, i, 0).await?;
                if !crate::proof::constant_time_eq(&digest, &stored_leaf_hash) {
                    return Ok(false); // Leaf/subtree root hash mismatch!
                }

                frontier.push(digest);
                frontier_coords.push((i, 0));
                *alg_size += 1;

                let merges = reduction_count(*alg_size - 1, self.config.log_arity as u64);
                for _ in 0..merges {
                    if frontier.len() < self.config.log_arity {
                        return Ok(false); // Frontier underflow!
                    }
                    let mut children = Vec::with_capacity(self.config.log_arity);
                    let mut coords = Vec::with_capacity(self.config.log_arity);
                    for _ in 0..self.config.log_arity {
                        children.push(frontier.pop().ok_or_else(|| {
                            crate::error::Error::CorruptedMetadata {
                                alg_id,
                                reason: "frontier underflow".to_string(),
                            }
                        })?);
                        coords.push(frontier_coords.pop().ok_or_else(|| {
                            crate::error::Error::CorruptedMetadata {
                                alg_id,
                                reason: "frontier_coords underflow".to_string(),
                            }
                        })?);
                    }
                    children.reverse();
                    coords.reverse();

                    let child_refs: Vec<&[u8]> = children.iter().map(|c| c.as_slice()).collect();
                    let parent = nary_mr(state.hasher.as_ref(), &child_refs);

                    let parent_left_index = coords[0].0;
                    let parent_height = coords[0].1 + 1;

                    let stored_parent = self
                        .get_node_hash(alg_id, parent_left_index, parent_height)
                        .await?;
                    if !crate::proof::constant_time_eq(&parent, &stored_parent) {
                        return Ok(false); // Internal node hash mismatch!
                    }

                    frontier.push(parent);
                    frontier_coords.push((parent_left_index, parent_height));
                }
            }
        }

        // Verify final recomputed roots match the current logger roots
        for (&alg_id, state) in &self.algs {
            let (frontier, ..) = &alg_frontiers[&alg_id];
            let folded = fold_frontier(state.hasher.as_ref(), frontier, self.config.log_arity);
            let final_root = self.root_for_at(alg_id, end).await?;
            if !crate::proof::constant_time_eq(&folded, &final_root) {
                return Ok(false); // Final root mismatch!
            }
        }

        Ok(true)
    }
}

/// Reconstruct the coordinates (left_index, height) of the frontier for a given tree size.
pub fn frontier_for_size(n: u64, k: u64) -> Vec<(u64, u32)> {
    if k < 2 {
        return Vec::new();
    }
    let mut frontier = Vec::new();
    let mut curr_left = 0;
    let mut temp_n = n;
    while temp_n > 0 {
        let mut height = 0;
        let mut cap: u64 = 1;
        while let Some(next_cap) = cap.checked_mul(k) {
            if next_cap <= temp_n {
                cap = next_cap;
                height += 1;
            } else {
                break;
            }
        }
        frontier.push((curr_left, height));
        curr_left += cap;
        temp_n -= cap;
    }
    frontier
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::storage::MemoryStorage;

    #[derive(Debug)]
    struct TestHasher;
    impl Hasher for TestHasher {
        fn leaf(&self, data: &[u8]) -> Vec<u8> {
            data.to_vec()
        }

        fn node(&self, children: &[&[u8]]) -> Vec<u8> {
            children.concat()
        }

        fn empty(&self) -> Vec<u8> {
            Vec::new()
        }

        fn null(&self) -> Vec<u8> {
            crate::generate_nums_null(self, 32)
        }

        fn hash(&self, data: &[u8]) -> Vec<u8> {
            data.to_vec()
        }

        fn clone_box(&self) -> Box<dyn Hasher> {
            Box::new(TestHasher)
        }
    }

    #[test]
    fn test_structural_node_id_storage() {
        smol::block_on(async {
            let storage = MemoryStorage::new();
            let config = TreeConfig { log_arity: 2 };
            let mut log = NaryMerkleLog::new(storage, Box::new(TestHasher), config)
                .await
                .unwrap();

            log.append_leaf(b"a").await.unwrap();
            log.append_leaf(b"b").await.unwrap();

            let storage_ref = log.storage();
            let node_hash = storage_ref.get_node(0, 0, 1).await.unwrap();
            assert!(
                node_hash.is_some(),
                "node at coordinate (0, 1) should be stored"
            );
        });
    }
}
