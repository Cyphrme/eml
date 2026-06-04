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

/// An n-ary Merkle Append-Only Log.
#[derive(Debug)]
pub struct NaryMerkleLog<S: Storage> {
    storage: S,
    hasher: Box<dyn Hasher>,
    config: TreeConfig,
    /// Frontier stack: holds hashes of completed subtrees along the right edge.
    frontier: Vec<Vec<u8>>,
    /// Coordinates of each frontier node: (left_index, height)
    frontier_coords: Vec<(u64, u32)>,
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
        Self {
            storage,
            hasher,
            config,
            frontier: Vec::new(),
            frontier_coords: Vec::new(),
            size: 0,
            commit_count: 0,
        }
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

    /// Access the frontier stack.
    #[must_use]
    pub fn frontier(&self) -> &[Vec<u8>] {
        &self.frontier
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

    /// Append a single leaf to the log (State Tree Mode).
    ///
    /// # Errors
    ///
    /// Returns a storage error if persisting the leaf or an internal node fails.
    pub fn append_leaf(&mut self, data: &[u8]) -> Result<(), S::Error> {
        let leaf_hash = self.hasher.leaf(data);
        self.storage
            .store_leaf(self.size, data)
            .map_err(crate::error::Error::Storage)?;
        let node_id = self.size << 16;
        self.storage
            .store_node(0, node_id, &leaf_hash)
            .map_err(crate::error::Error::Storage)?;
        self.frontier.push(leaf_hash);
        self.frontier_coords.push((self.size, 0));

        let merges = reduction_count(self.size, self.config.log_arity as u64);
        for _ in 0..merges {
            let mut children = Vec::with_capacity(self.config.log_arity);
            let mut coords = Vec::with_capacity(self.config.log_arity);
            for _ in 0..self.config.log_arity {
                children.push(
                    self.frontier
                        .pop()
                        .expect("frontier stack underflow during reduction"),
                );
                coords.push(
                    self.frontier_coords
                        .pop()
                        .expect("frontier_coords stack underflow during reduction"),
                );
            }
            children.reverse();
            coords.reverse();
            let child_refs: Vec<&[u8]> = children.iter().map(|c| c.as_slice()).collect();
            let parent = nary_mr(&*self.hasher, &child_refs);

            let parent_left_index = coords[0].0;
            let parent_height = coords[0].1 + 1;
            let node_id = (parent_left_index << 16) | (parent_height as u64 & 0xFFFF);

            self.storage
                .store_node(0, node_id, &parent)
                .map_err(crate::error::Error::Storage)?;

            self.frontier.push(parent);
            self.frontier_coords
                .push((parent_left_index, parent_height));
        }

        self.size += 1;
        Ok(())
    }

    /// Append a structured subtree to the log (Commit Tree Mode).
    ///
    /// # Errors
    ///
    /// Returns a storage error if persisting an internal node fails.
    pub fn append_subtree(&mut self, subtree: &Subtree) -> Result<(), S::Error> {
        let root_hash = evaluate(&*self.hasher, subtree);
        let node_id = self.commit_count << 16;
        self.storage
            .store_node(0, node_id, &root_hash)
            .map_err(crate::error::Error::Storage)?;
        self.frontier.push(root_hash);
        self.frontier_coords.push((self.commit_count, 0));

        let merges = reduction_count(self.commit_count, self.config.log_arity as u64);
        for _ in 0..merges {
            let mut children = Vec::with_capacity(self.config.log_arity);
            let mut coords = Vec::with_capacity(self.config.log_arity);
            for _ in 0..self.config.log_arity {
                children.push(
                    self.frontier
                        .pop()
                        .expect("frontier stack underflow during reduction"),
                );
                coords.push(
                    self.frontier_coords
                        .pop()
                        .expect("frontier_coords stack underflow during reduction"),
                );
            }
            children.reverse();
            coords.reverse();
            let child_refs: Vec<&[u8]> = children.iter().map(|c| c.as_slice()).collect();
            let parent = nary_mr(&*self.hasher, &child_refs);

            let parent_left_index = coords[0].0;
            let parent_height = coords[0].1 + 1;
            let node_id = (parent_left_index << 16) | (parent_height as u64 & 0xFFFF);

            self.storage
                .store_node(0, node_id, &parent)
                .map_err(crate::error::Error::Storage)?;

            self.frontier.push(parent);
            self.frontier_coords
                .push((parent_left_index, parent_height));
        }

        self.commit_count += 1;
        Ok(())
    }

    /// Compute the current root hash of the tree.
    #[must_use]
    pub fn root(&self) -> Vec<u8> {
        if self.frontier.is_empty() {
            return self.hasher.empty();
        }
        if self.frontier.len() == 1 {
            return self.frontier[0].clone();
        }
        let k = self.config.log_arity;
        let mut current = self.frontier.clone();
        while current.len() > k {
            let split_idx = current.len() - k;
            let right_elements = &current[split_idx..];
            let refs: Vec<&[u8]> = right_elements.iter().map(|v| v.as_slice()).collect();
            let merged = nary_mr(&*self.hasher, &refs);
            current.truncate(split_idx);
            current.push(merged);
        }
        let refs: Vec<&[u8]> = current.iter().map(|v| v.as_slice()).collect();
        nary_mr(&*self.hasher, &refs)
    }

    /// Generate an inclusion proof for the item at `index` in a tree of size `tree_size`.
    ///
    /// In State Tree Mode, `index` is the leaf index.
    /// In Commit Tree Mode, `index` is the commit index.
    ///
    /// # Errors
    ///
    /// Returns a storage error if fetching node hashes from the storage backend fails.
    pub fn inclusion_proof(
        &self,
        index: u64,
        tree_size: u64,
    ) -> Result<Option<crate::proof::InclusionProof>, S::Error> {
        let max_size = if self.size > 0 {
            self.size
        } else {
            self.commit_count
        };

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
        self.log_level_bisection_path_to_height(left, height, index, 0, &mut path)?;
        path.reverse();

        let mut hashes = Vec::with_capacity(coords.len());
        for &(l, h) in &coords {
            let node_id = (l << 16) | (h as u64 & 0xFFFF);
            let hash = self
                .storage
                .get_node(0, node_id)
                .map_err(crate::error::Error::Storage)?
                .expect("frontier node hash not found in storage");
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
            let merged_hash = nary_mr(&*self.hasher, &refs);

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
    ///
    /// # Errors
    ///
    /// Returns a storage error if fetching node hashes from the storage backend fails.
    pub fn consistency_proof(
        &self,
        old_size: u64,
        new_size: u64,
    ) -> Result<Option<crate::proof::ConsistencyProof>, S::Error> {
        let max_size = if self.size > 0 {
            self.size
        } else {
            self.commit_count
        };

        if old_size == 0 || old_size >= new_size || new_size > max_size {
            return Ok(None);
        }

        let k = self.config.log_arity as u64;
        let old_coords = frontier_for_size(old_size, k);
        let &(boundary_left, boundary_height) = old_coords
            .last()
            .expect("old_coords cannot be empty since old_size > 0");

        let node_id = (boundary_left << 16) | (boundary_height as u64 & 0xFFFF);
        let start_hash = self
            .storage
            .get_node(0, node_id)
            .map_err(crate::error::Error::Storage)?
            .expect("boundary root hash not found in storage");

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
            left,
            height,
            boundary_left,
            boundary_height,
            &mut path,
        )?;
        path.reverse();

        let mut hashes = Vec::with_capacity(new_coords.len());
        for &(l, h) in &new_coords {
            let node_id = (l << 16) | (h as u64 & 0xFFFF);
            let hash = self
                .storage
                .get_node(0, node_id)
                .map_err(crate::error::Error::Storage)?
                .expect("frontier node hash not found in storage");
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
            let merged_hash = nary_mr(&*self.hasher, &refs);

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
                let node_id = (c_left << 16) | ((curr_height - 1) as u64 & 0xFFFF);
                let hash = self
                    .storage
                    .get_node(0, node_id)
                    .map_err(crate::error::Error::Storage)?
                    .expect("sibling node hash not found in storage");
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
fn frontier_for_size(n: u64, k: u64) -> Vec<(u64, u32)> {
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
