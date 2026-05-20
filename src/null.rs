//! Null constant table (Definitions 1-2, §3 of the formal model).
//!
//! The null constant table precomputes `Nₕ(a)` for heights `0..H` where
//! `H = ⌈log₂(n)⌉`. This requires `O(H)` hash operations and `O(H)` storage.
//!
//! Each entry is deterministic: `Nₕ(a)` is uniquely determined by `(a, h)`.

use crate::Hasher;

/// Precomputed null subtree constants for a single algorithm.
///
/// `table[0] = N₀(a) = H_a(0x02)`
/// `table[h] = Nₕ(a) = H_a(0x01 ‖ Nₕ₋₁(a) ‖ Nₕ₋₁(a))`
///
/// The table grows lazily as the tree height increases.
#[derive(Debug, Clone)]
pub struct NullTable {
    table: Vec<Vec<u8>>,
}

impl NullTable {
    /// Create a new null table with the base constant `N₀(a)`.
    pub fn new(hasher: &dyn Hasher) -> Self {
        let n0 = hasher.null();
        Self { table: vec![n0] }
    }

    /// Get `Nₕ(a)`, extending the table if necessary.
    ///
    /// This is Definition 2 from the formal model:
    /// `Nₕ(a) = node(a, Nₕ₋₁(a), Nₕ₋₁(a))`
    pub fn get(&mut self, hasher: &dyn Hasher, height: usize) -> &[u8] {
        while self.table.len() <= height {
            let prev = &self.table[self.table.len() - 1];
            let next = hasher.node(prev, prev);
            self.table.push(next);
        }
        &self.table[height]
    }

    /// Ensure the table is pre-populated to at least the given height.
    ///
    /// Call this before immutable operations that need null constants
    /// at a known maximum height (e.g., proof generation).
    pub fn ensure_height(&mut self, hasher: &dyn Hasher, height: usize) {
        if self.table.len() <= height {
            self.get(hasher, height);
        }
    }

    /// Get `Nₕ(a)` from the pre-populated table without mutation.
    ///
    /// # Panics
    ///
    /// Panics if `height` exceeds the pre-populated range. Call
    /// [`ensure_height`](Self::ensure_height) first.
    #[must_use]
    pub fn get_precomputed(&self, height: usize) -> &[u8] {
        &self.table[height]
    }

    /// Get `N₀(a)` — the null leaf constant.
    #[must_use]
    pub fn leaf_null(&self) -> &[u8] {
        &self.table[0]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Minimal test hasher that concatenates with prefixes.
    #[derive(Debug)]
    struct ConcatHasher;

    impl Hasher for ConcatHasher {
        fn leaf(&self, data: &[u8]) -> Vec<u8> {
            let mut v = vec![0x00];
            v.extend_from_slice(data);
            v
        }

        fn node(&self, left: &[u8], right: &[u8]) -> Vec<u8> {
            let mut v = vec![0x01];
            v.extend_from_slice(left);
            v.extend_from_slice(right);
            v
        }

        fn empty(&self) -> Vec<u8> {
            vec![]
        }

        fn null(&self) -> Vec<u8> {
            vec![0x02]
        }
    }

    #[test]
    fn null_table_determinism() {
        let h = ConcatHasher;
        let mut t1 = NullTable::new(&h);
        let mut t2 = NullTable::new(&h);

        // N-DET: same (a, h) → same result
        for height in 0..5 {
            assert_eq!(t1.get(&h, height), t2.get(&h, height));
        }
    }

    #[test]
    fn null_table_base_is_null_prefix() {
        let h = ConcatHasher;
        let t = NullTable::new(&h);
        // N₀(a) = H_a(0x02)
        assert_eq!(t.leaf_null(), &[0x02]);
    }

    #[test]
    fn null_table_recursive_construction() {
        let h = ConcatHasher;
        let mut t = NullTable::new(&h);

        // N₁(a) = node(a, N₀(a), N₀(a)) = [0x01, 0x02, 0x02]
        let n1 = t.get(&h, 1).to_vec();
        assert_eq!(n1, vec![0x01, 0x02, 0x02]);

        // N₂(a) = node(a, N₁(a), N₁(a))
        let n2 = t.get(&h, 2).to_vec();
        let expected = {
            let mut v = vec![0x01];
            v.extend_from_slice(&n1);
            v.extend_from_slice(&n1);
            v
        };
        assert_eq!(n2, expected);
    }

    #[test]
    fn domain_separation() {
        let h = ConcatHasher;
        let t = NullTable::new(&h);

        // D-SEP: null ≠ leaf for any data
        let leaf_empty = h.leaf(b"");
        let leaf_data = h.leaf(b"hello");
        let null = t.leaf_null();

        assert_ne!(null, leaf_empty.as_slice());
        assert_ne!(null, leaf_data.as_slice());

        // D-SEP: null ≠ node for any children
        let node = h.node(b"left", b"right");
        assert_ne!(null, node.as_slice());
    }
}
