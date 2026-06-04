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
}

/// An n-ary Merkle Append-Only Log.
#[derive(Debug, Clone)]
pub struct NaryMerkleLog<S: Storage> {
    storage: S,
    config: TreeConfig,
    algs: std::collections::HashMap<u64, AlgState>,
    /// Number of leaves appended (flat state tree mode).
    size: u64,
    /// Number of subtrees (commits) appended.
    commit_count: u64,
}

impl<S: Storage> NaryMerkleLog<S> {
    /// Create a new empty n-ary Merkle log.
    #[must_use]
    pub fn new(storage: S, hasher: Box<dyn Hasher>, config: TreeConfig) -> Self {
        assert!(config.log_arity >= 2, "log arity must be >= 2");
        let mut log = Self {
            storage,
            config,
            algs: std::collections::HashMap::new(),
            size: 0,
            commit_count: 0,
        };
        // Eagerly register algorithm 0 as active from index 0
        log.add_algorithm(0, hasher).unwrap_or_else(|_| {
            panic!("failed to initialize default algorithm");
        });
        log
    }

    /// Reconstruct an existing Merkle log from storage using the default configuration.
    ///
    /// # Errors
    ///
    /// Returns a storage error or validation error if the reconstruction fails.
    pub fn from_storage(
        storage: S,
        hashers: Vec<(u64, Box<dyn Hasher>)>,
    ) -> Result<Self, S::Error> {
        Self::from_storage_with_config(storage, hashers, TreeConfig::default())
    }

    /// Reconstruct an existing Merkle log from storage with a specific configuration.
    ///
    /// # Errors
    ///
    /// Returns a storage error or validation error if the reconstruction fails.
    pub fn from_storage_with_config(
        storage: S,
        hashers: Vec<(u64, Box<dyn Hasher>)>,
        config: TreeConfig,
    ) -> Result<Self, S::Error> {
        let metas = storage
            .load_algorithm_metas()
            .map_err(crate::error::Error::Storage)?;

        let mut hasher_map: std::collections::HashMap<u64, Box<dyn Hasher>> =
            hashers.into_iter().collect();

        // Validate 1:1 correspondence.
        for &(alg_id, _) in &metas {
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

        let global_size = Self::determine_global_size(&storage, &metas)?;

        let mut algs = std::collections::HashMap::new();
        let k = config.log_arity as u64;
        for (alg_id, epochs) in metas {
            let hasher = hasher_map.remove(&alg_id).expect("validated 1:1");
            let state = Self::reconstruct_algorithm_state(
                &storage,
                alg_id,
                hasher,
                &epochs,
                global_size,
                k,
            )?;
            algs.insert(alg_id, state);
        }

        // Determine if we are in Commit Tree Mode or State Tree Mode.
        let is_state_mode = storage.len() > 0;
        let size = if is_state_mode { global_size } else { 0 };
        let commit_count = if is_state_mode { 0 } else { global_size };

        Ok(Self {
            storage,
            config,
            algs,
            size,
            commit_count,
        })
    }

    /// Probe storage to find the current global size.
    fn determine_global_size(
        storage: &S,
        metas: &[(u64, Vec<(u64, u64)>)],
    ) -> Result<u64, S::Error> {
        let leaf_len = storage.len();
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
            let node_id = high << 16;
            if storage
                .get_node(alg_id, node_id)
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
            let node_id = mid << 16;
            if storage
                .get_node(alg_id, node_id)
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
    fn reconstruct_algorithm_state(
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
                let node_id = (left << 16) | (height as u64 & 0xFFFF);
                storage
                    .get_node(alg_id, node_id)
                    .map_err(crate::error::Error::Storage)?
                    .unwrap_or_else(|| state.hasher.null())
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

    /// Retrieve the number of commits/subtrees stored.
    #[must_use]
    pub fn commit_count(&self) -> u64 {
        self.commit_count
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
    pub fn add_algorithm(&mut self, alg_id: u64, hasher: Box<dyn Hasher>) -> Result<(), S::Error> {
        if self.algs.contains_key(&alg_id) {
            return Err(crate::error::Error::DuplicateAlgorithm(alg_id));
        }

        let current_size = if self.size > 0 {
            self.size
        } else {
            self.commit_count
        };

        let epochs = vec![(current_size, u64::MAX)];

        // Persist metadata BEFORE committing in-memory state.
        self.storage
            .store_algorithm_meta(alg_id, &epochs)
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
    pub fn remove_algorithm(&mut self, alg_id: u64) -> Result<(), S::Error> {
        let current_size = if self.size > 0 {
            self.size
        } else {
            self.commit_count
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
            .map_err(crate::error::Error::Storage)?;

        state.epochs = new_epochs;
        Ok(())
    }

    /// Reactivate a frozen algorithm at the current tree size.
    pub fn resume_algorithm(&mut self, alg_id: u64) -> Result<(), S::Error> {
        let current_size = if self.size > 0 {
            self.size
        } else {
            self.commit_count
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

        for &(left, height) in &coords {
            let cap = k.pow(height);
            let hash = Self::reconstruct_subtree_root(
                &mut self.storage,
                alg_id,
                &temp_state,
                left,
                left + cap,
                k,
                true,
            )?;
            frontier.push(hash);
        }

        self.storage
            .store_algorithm_meta(alg_id, &new_epochs)
            .map_err(crate::error::Error::Storage)?;

        let state = self.algs.get_mut(&alg_id).unwrap();
        state.epochs = new_epochs;
        state.frontier = frontier;
        state.frontier_coords = coords;

        Ok(())
    }

    /// Recursively resolve a subtree root and collect mixed boundary nodes.
    fn reconstruct_subtree_root(
        storage: &mut S,
        alg_id: u64,
        state: &AlgState,
        lo: u64,
        hi: u64,
        k: u64,
        store_mixed: bool,
    ) -> Result<Vec<u8>, S::Error> {
        let size = hi - lo;
        if size == 0 {
            return Ok(state.hasher.empty());
        }
        if size == 1 {
            if state.is_active_at(lo) {
                if storage.len() == 0 {
                    let node_id = lo << 16;
                    if let Some(hash) = storage
                        .get_node(alg_id, node_id)
                        .map_err(crate::error::Error::Storage)?
                    {
                        return Ok(hash);
                    } else {
                        return Ok(state.hasher.null());
                    }
                } else {
                    let data = storage.get_leaf(lo).map_err(crate::error::Error::Storage)?;
                    return Ok(state.hasher.leaf(&data));
                }
            }
            return Ok(state.hasher.null());
        }

        if !state.active_range(lo, hi) {
            return Ok(state.hasher.null());
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
            let node_id = (lo << 16) | (height as u64 & 0xFFFF);
            if let Some(hash) = storage
                .get_node(alg_id, node_id)
                .map_err(crate::error::Error::Storage)?
            {
                return Ok(hash);
            }

            let child_size = size / k;
            let mut child_hashes = Vec::with_capacity(k as usize);
            for j in 0..k {
                let c_lo = lo + j * child_size;
                let c_hi = lo + (j + 1) * child_size;
                let child_hash = Self::reconstruct_subtree_root(
                    storage,
                    alg_id,
                    state,
                    c_lo,
                    c_hi,
                    k,
                    store_mixed,
                )?;
                child_hashes.push(child_hash);
            }
            let child_refs: Vec<&[u8]> = child_hashes.iter().map(|c| c.as_slice()).collect();
            let hash = nary_mr(state.hasher.as_ref(), &child_refs);

            if store_mixed {
                storage
                    .store_node(alg_id, node_id, &hash)
                    .map_err(crate::error::Error::Storage)?;
            }
            Ok(hash)
        } else {
            let coords = frontier_for_size(size, k);
            let mut component_hashes = Vec::with_capacity(coords.len());
            for &(part_left, part_height) in &coords {
                let cap = k.pow(part_height);
                let c_lo = lo + part_left;
                let c_hi = c_lo + cap;
                let part_root = Self::reconstruct_subtree_root(
                    storage,
                    alg_id,
                    state,
                    c_lo,
                    c_hi,
                    k,
                    store_mixed,
                )?;
                component_hashes.push(part_root);
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
            Ok(nary_mr(state.hasher.as_ref(), &refs))
        }
    }

    /// Append a single leaf to the log (State Tree Mode).
    pub fn append_leaf(&mut self, data: &[u8]) -> Result<(), S::Error> {
        if !self.algs.values().any(|s| s.is_active()) {
            return Err(crate::error::Error::NoActiveAlgorithms);
        }

        // Store the leaf payload first
        self.storage
            .store_leaf(self.size, data)
            .map_err(crate::error::Error::Storage)?;

        for (&alg_id, state) in &mut self.algs {
            if !state.is_active() {
                continue;
            }

            let digest = if state.is_active_at(self.size) {
                let leaf_hash = state.hasher.leaf(data);
                let node_id = self.size << 16;
                self.storage
                    .store_node(alg_id, node_id, &leaf_hash)
                    .map_err(crate::error::Error::Storage)?;
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
                    children.push(
                        state
                            .frontier
                            .pop()
                            .expect("frontier stack underflow during reduction"),
                    );
                    coords.push(
                        state
                            .frontier_coords
                            .pop()
                            .expect("frontier_coords stack underflow during reduction"),
                    );
                }
                children.reverse();
                coords.reverse();
                let child_refs: Vec<&[u8]> = children.iter().map(|c| c.as_slice()).collect();
                let parent = nary_mr(state.hasher.as_ref(), &child_refs);

                let parent_left_index = coords[0].0;
                let parent_height = coords[0].1 + 1;
                let node_id = (parent_left_index << 16) | (parent_height as u64 & 0xFFFF);

                if parent != state.hasher.null() {
                    self.storage
                        .store_node(alg_id, node_id, &parent)
                        .map_err(crate::error::Error::Storage)?;
                }

                state.frontier.push(parent);
                state
                    .frontier_coords
                    .push((parent_left_index, parent_height));
            }
        }

        self.size += 1;
        Ok(())
    }

    /// Append a structured subtree to the log (Commit Tree Mode).
    pub fn append_subtree(&mut self, subtree: &Subtree) -> Result<(), S::Error> {
        if !self.algs.values().any(|s| s.is_active()) {
            return Err(crate::error::Error::NoActiveAlgorithms);
        }

        for (&alg_id, state) in &mut self.algs {
            if !state.is_active() {
                continue;
            }

            let digest = if state.is_active_at(self.commit_count) {
                let root_hash = evaluate(state.hasher.as_ref(), subtree);
                let node_id = self.commit_count << 16;
                self.storage
                    .store_node(alg_id, node_id, &root_hash)
                    .map_err(crate::error::Error::Storage)?;
                root_hash
            } else {
                state.hasher.null()
            };

            state.frontier.push(digest);
            state.frontier_coords.push((self.commit_count, 0));

            let merges = reduction_count(self.commit_count, self.config.log_arity as u64);
            for _ in 0..merges {
                let mut children = Vec::with_capacity(self.config.log_arity);
                let mut coords = Vec::with_capacity(self.config.log_arity);
                for _ in 0..self.config.log_arity {
                    children.push(
                        state
                            .frontier
                            .pop()
                            .expect("frontier stack underflow during reduction"),
                    );
                    coords.push(
                        state
                            .frontier_coords
                            .pop()
                            .expect("frontier_coords stack underflow during reduction"),
                    );
                }
                children.reverse();
                coords.reverse();
                let child_refs: Vec<&[u8]> = children.iter().map(|c| c.as_slice()).collect();
                let parent = nary_mr(state.hasher.as_ref(), &child_refs);

                let parent_left_index = coords[0].0;
                let parent_height = coords[0].1 + 1;
                let node_id = (parent_left_index << 16) | (parent_height as u64 & 0xFFFF);

                if parent != state.hasher.null() {
                    self.storage
                        .store_node(alg_id, node_id, &parent)
                        .map_err(crate::error::Error::Storage)?;
                }

                state.frontier.push(parent);
                state
                    .frontier_coords
                    .push((parent_left_index, parent_height));
            }
        }

        self.commit_count += 1;
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
    fn get_node_hash(&self, alg_id: u64, left: u64, height: u32) -> Result<Vec<u8>, S::Error> {
        let state = self
            .algs
            .get(&alg_id)
            .ok_or(crate::error::Error::UnknownAlgorithm(alg_id))?;
        let k = self.config.log_arity as u64;
        let cap = k.pow(height);
        if !state.active_range(left, left + cap) {
            return Ok(state.hasher.null());
        }
        let node_id = (left << 16) | (height as u64 & 0xFFFF);
        if let Some(hash) = self
            .storage
            .get_node(alg_id, node_id)
            .map_err(crate::error::Error::Storage)?
        {
            Ok(hash)
        } else {
            Ok(state.hasher.null())
        }
    }

    /// Generate an inclusion proof for the item at `index` in a tree of size `tree_size`.
    pub fn inclusion_proof(
        &self,
        index: u64,
        tree_size: u64,
    ) -> Result<Option<crate::proof::InclusionProof>, S::Error> {
        self.inclusion_proof_for(0, index, tree_size)
    }

    /// Generate an inclusion proof for a specific algorithm.
    pub fn inclusion_proof_for(
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
            self.commit_count
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
        self.log_level_bisection_path_to_height(alg_id, left, height, index, 0, &mut path)?;
        path.reverse();

        let mut hashes = Vec::with_capacity(coords.len());
        for &(l, h) in &coords {
            let hash = self.get_node_hash(alg_id, l, h)?;
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
            path,
        }))
    }

    /// Generate a consistency proof between `old_size` and `new_size`.
    pub fn consistency_proof(
        &self,
        old_size: u64,
        new_size: u64,
    ) -> Result<Option<crate::proof::ConsistencyProof>, S::Error> {
        self.consistency_proof_for(0, old_size, new_size)
    }

    /// Generate a consistency proof for a specific algorithm.
    pub fn consistency_proof_for(
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
            self.commit_count
        });

        if old_size == 0 || old_size >= new_size || new_size > max_size {
            return Ok(None);
        }

        let k = self.config.log_arity as u64;
        let old_coords = frontier_for_size(old_size, k);
        let &(boundary_left, boundary_height) = old_coords
            .last()
            .expect("old_coords cannot be empty since old_size > 0");

        let start_hash = self.get_node_hash(alg_id, boundary_left, boundary_height)?;

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
        )?;
        path.reverse();

        let mut hashes = Vec::with_capacity(new_coords.len());
        for &(l, h) in &new_coords {
            let hash = self.get_node_hash(alg_id, l, h)?;
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

    fn log_level_bisection_path_to_height(
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
                let hash = self.get_node_hash(alg_id, c_left, curr_height - 1)?;
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
}

/// Reconstruct the coordinates (left_index, height) of the frontier for a given tree size.
pub fn frontier_for_size(n: u64, k: u64) -> Vec<(u64, u32)> {
    let mut frontier = Vec::new();
    let mut curr_left = 0;
    let mut temp_n = n;
    while temp_n > 0 {
        let mut height = 0;
        let mut cap = 1;
        while cap * k <= temp_n {
            cap *= k;
            height += 1;
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
            vec![2]
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
        let storage = MemoryStorage::new();
        let config = TreeConfig { log_arity: 2 };
        let mut log = NaryMerkleLog::new(storage, Box::new(TestHasher), config);

        log.append_leaf(b"a").unwrap();
        log.append_leaf(b"b").unwrap();

        let storage_ref = log.storage();
        let node_hash = storage_ref.get_node(0, 1).unwrap();
        assert!(
            node_hash.is_some(),
            "node at ID 1 (left_index 0, height 1) should be stored"
        );
    }
}
