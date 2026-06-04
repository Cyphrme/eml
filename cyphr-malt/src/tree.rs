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
            self.frontier_coords.push((parent_left_index, parent_height));
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
            self.frontier_coords.push((parent_left_index, parent_height));
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
        assert!(node_hash.is_some(), "node at ID 1 (left_index 0, height 1) should be stored");
    }
}
