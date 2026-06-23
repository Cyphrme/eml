//! `cyphr-tree` — the [`emt`] mutable tree instantiated at **k=2, no prefix**.
//!
//! This is the L3 instantiation: it fixes the proof-spine arity to 2 and pairs
//! the EMT with a concrete unprefixed SHA-256 hasher, so an application gets a
//! ready mutable tree in a few lines. With the append-only cyphr-log it composes
//! Cyphr's single Principal Tree (a mutable outer tree with an embedded
//! append-only commit log, joined by the kernel's opaque embedding) — that
//! composition lives at the application layer, not here; this crate only
//! supplies the outer mutable tree.
//!
//! ```
//! use cyphr_tree::CyphrTree;
//!
//! let mut tree = CyphrTree::new();
//! tree.set(0, b"genesis".to_vec()).unwrap();
//! tree.set(1, b"second".to_vec()).unwrap();
//! let root = tree.root().expect("a non-empty tree has a root");
//! assert_eq!(tree.get(0), Some(b"genesis".as_slice()));
//! # let _ = root;
//! ```

use emt::{Config, Emt};
pub use emt::{Error, ProofStep, Result, Sealed};
use sha2::{Digest, Sha256};

/// The fixed proof-spine arity of the cyphr tree.
const ARITY: u64 = 2;

/// The single algorithm slot used by the convenience surface.
const ALG: u64 = 0;

/// Unprefixed SHA-256 — the cyphr tree's hash. No domain-separation prefix:
/// a promoted (lone-child) node must be byte-identical to a plain node, which a
/// leaf/node prefix would break.
#[derive(Debug, Clone, Copy)]
struct Sha256Hasher;

impl emt::Hasher for Sha256Hasher {
    fn leaf(&self, data: &[u8]) -> Vec<u8> {
        Sha256::digest(data).to_vec()
    }

    fn node(&self, children: &[&[u8]]) -> Vec<u8> {
        let mut h = Sha256::new();
        for child in children {
            h.update(child);
        }
        h.finalize().to_vec()
    }

    fn empty(&self) -> Vec<u8> {
        Sha256::digest(b"").to_vec()
    }

    fn hash(&self, data: &[u8]) -> Vec<u8> {
        Sha256::digest(data).to_vec()
    }

    fn clone_box(&self) -> Box<dyn emt::Hasher> {
        Box::new(*self)
    }
}

/// A mutable tree at k=2 over unprefixed SHA-256.
///
/// A thin ergonomic wrapper over [`emt::Emt`]: one fixed algorithm, one fixed
/// arity. For multi-algorithm trees or a different hash, drive [`emt::Emt`]
/// directly.
#[derive(Debug)]
pub struct CyphrTree {
    inner: Emt,
}

impl CyphrTree {
    /// A new empty tree.
    #[must_use]
    pub fn new() -> Self {
        let mut inner = Emt::new(Config { arity: ARITY }).expect("k=2 is in range");
        inner
            .register_algorithm(ALG, Box::new(Sha256Hasher))
            .expect("a fresh tree has no algorithm registered");
        Self { inner }
    }

    /// Set the payload of cell `index`; see [`emt::Emt::set`] for the dense-index
    /// contract. (Metadata is left empty; drive [`emt::Emt`] directly to carry
    /// the opaque metadata channel.)
    pub fn set(&mut self, index: u64, payload: Vec<u8>) -> Result<()> {
        self.inner.set(index, payload, Vec::new())
    }

    /// Read the payload of cell `index`.
    #[must_use]
    pub fn get(&self, index: u64) -> Option<&[u8]> {
        self.inner.get(index)
    }

    /// The number of cells.
    #[must_use]
    pub fn len(&self) -> u64 {
        self.inner.len()
    }

    /// Whether the tree is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// The current root digest, or `None` for an empty tree.
    #[must_use]
    pub fn root(&self) -> Option<Vec<u8>> {
        self.inner.root(ALG)
    }

    /// An inclusion proof for cell `index`: the leaf digest and proof path,
    /// verifiable with [`emt::verify_inclusion`] against `(index, len, 2, root)`.
    #[must_use]
    pub fn inclusion_proof(&self, index: u64) -> Option<(Vec<u8>, Vec<ProofStep>)> {
        self.inner.inclusion_proof(ALG, index)
    }

    /// Consume the tree, sealing it into the kernel currency. One-way.
    pub fn seal(self) -> Result<Sealed> {
        self.inner.seal()
    }
}

impl Default for CyphrTree {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use sha2::{Digest, Sha256};

    use super::*;

    #[test]
    fn reads_in_a_few_lines_and_verifies() {
        let mut tree = CyphrTree::new();
        tree.set(0, b"genesis".to_vec()).unwrap();
        tree.set(1, b"second".to_vec()).unwrap();
        tree.set(2, b"third".to_vec()).unwrap();

        let root = tree.root().unwrap();
        let (leaf, path) = tree.inclusion_proof(1).unwrap();
        let h = Sha256Hasher;
        assert!(emt::verify_inclusion(&h, &leaf, 1, 3, ARITY, &path, &root));
        assert_eq!(leaf, Sha256::digest(b"second").to_vec());
    }

    #[test]
    fn overwrite_changes_the_root() {
        let mut tree = CyphrTree::new();
        tree.set(0, b"a".to_vec()).unwrap();
        tree.set(1, b"b".to_vec()).unwrap();
        let before = tree.root().unwrap();
        tree.set(0, b"A".to_vec()).unwrap();
        assert_ne!(tree.root().unwrap(), before);
    }

    #[test]
    fn seals_one_way() {
        let mut tree = CyphrTree::new();
        tree.set(0, b"x".to_vec()).unwrap();
        let sealed = tree.seal().unwrap();
        assert_eq!(sealed.tree_size(), 1);
    }
}
