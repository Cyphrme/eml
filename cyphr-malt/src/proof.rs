//! Inclusion and consistency proof structures and verification algorithms.

use crate::hasher::Hasher;
use crate::mr::nary_mr;

/// A single level in a Merkle proof path.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProofStep {
    /// Sibling digests at this level (excluding the path node).
    /// Empty for promoted (singleton) nodes.
    pub siblings: Vec<Vec<u8>>,
    /// Position of the path node among all children (0-indexed).
    pub position: usize,
}

/// Inclusion proof: path from a leaf to the root.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InclusionProof {
    /// 0-based leaf index of the target.
    pub index: u64,
    /// Size of the tree for which this proof is valid.
    pub tree_size: u64,
    /// Path steps from leaf to root.
    pub path: Vec<ProofStep>,
}

/// Consistency proof: proves tree at `old_size` is a prefix of tree at `new_size`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConsistencyProof {
    /// Size of the older tree.
    pub old_size: u64,
    /// Size of the newer tree.
    pub new_size: u64,
    /// Starting hash (representing the boundary node of the old tree).
    pub start_hash: Vec<u8>,
    /// Path steps from the boundary to the root.
    pub path: Vec<ProofStep>,
}

/// Verify an inclusion proof.
///
/// Returns `true` if the proof demonstrates that `leaf_hash` is the leaf at
/// the given index in a tree of the given tree size with the given root.
#[must_use]
pub fn verify_inclusion(
    hasher: &dyn Hasher,
    leaf_hash: &[u8],
    proof: &InclusionProof,
    root: &[u8],
) -> bool {
    if proof.index >= proof.tree_size {
        return false;
    }

    let mut current = leaf_hash.to_vec();

    for step in &proof.path {
        if step.siblings.is_empty() {
            // Promoted node — current hash passes through unchanged
            continue;
        }
        if step.position > step.siblings.len() {
            return false;
        }

        // Reconstruct the parent: insert current at position among siblings
        let mut children = Vec::with_capacity(step.siblings.len() + 1);
        for (i, sib) in step.siblings.iter().enumerate() {
            if i == step.position {
                children.push(current.as_slice());
            }
            children.push(sib.as_slice());
        }
        if step.position == step.siblings.len() {
            children.push(current.as_slice());
        }

        current = nary_mr(hasher, &children);
    }

    current == root
}

/// Verify a consistency proof.
///
/// Proves that the tree of size `old_size` with `old_root` is an append-only
/// prefix of the tree of size `new_size` with `new_root`.
#[must_use]
pub fn verify_consistency(
    hasher: &dyn Hasher,
    proof: &ConsistencyProof,
    old_root: &[u8],
    new_root: &[u8],
) -> bool {
    if proof.old_size == 0 || proof.old_size >= proof.new_size {
        return false;
    }

    let mut fr = proof.start_hash.clone();
    let mut sr = proof.start_hash.clone();

    for step in &proof.path {
        if step.siblings.is_empty() {
            // Promoted node — current hashes pass through unchanged
            continue;
        }
        if step.position > step.siblings.len() {
            return false;
        }

        let idx = step.position;
        let left_sibs = &step.siblings[0..idx];
        let right_sibs = &step.siblings[idx..];

        // Reconstruct old parent children: left siblings + old child
        let mut old_children = Vec::with_capacity(left_sibs.len() + 1);
        for sib in left_sibs {
            old_children.push(sib.as_slice());
        }
        old_children.push(fr.as_slice());

        // Reconstruct new parent children: left siblings + new child + right siblings
        let mut new_children = Vec::with_capacity(step.siblings.len() + 1);
        for sib in left_sibs {
            new_children.push(sib.as_slice());
        }
        new_children.push(sr.as_slice());
        for sib in right_sibs {
            new_children.push(sib.as_slice());
        }

        fr = nary_mr(hasher, &old_children);
        sr = nary_mr(hasher, &new_children);
    }

    fr == old_root && sr == new_root
}
