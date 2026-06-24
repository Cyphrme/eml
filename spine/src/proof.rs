//! Inclusion proof structures and verification.
//!
//! # Security boundary: skeleton-pinned, prefix-chained
//!
//! An inclusion proof path runs leaf → root and splits into two regions:
//!
//! - The **log skeleton** — the trailing steps along the fixed-arity proof spine. Their shape
//!   (count, per-step position and sibling count) is fully determined by `(index, tree_size,
//!   arity)` and is pinned exactly against [`crate::topology::inclusion_skeleton`]. Because there
//!   is no per-node domain separation, second-preimage safety rests entirely on this exactness: the
//!   verifier reconstructs the canonical topology and rejects any deviation.
//! - The **subtree prefix** — the leading steps below the leaf's log position, in
//!   application-defined (non-uniform) subtrees. These carry no topological claim and are verified
//!   by hash chaining alone.
//!
//! ## Canonical proof encoding
//!
//! Every accepted step hashes: it must carry at least one sibling. A zero-sibling
//! step would represent a *promoted* (lone-child) node, whose parent equals its
//! child without any hashing — an inert no-op. Such steps are therefore rejected
//! everywhere ([`reconstruct_inclusion_root`]), and honest provers omit them
//! ([`crate::within_subtree_path`]). Omitting a promoted step never changes the
//! computed root, so completeness is preserved; in exchange, a fixed
//! `(leaf_hash, index, tree_size, root)` admits at most one accepting path
//! (modulo hash collisions), which closes prepend/insert malleability. This
//! concerns zero-*sibling* steps only; null-*valued* siblings from a null
//! collapse are unaffected.

use crate::hasher::Hasher;
use crate::mr::nary_mr;
use crate::topology::{ARITY_RANGE, inclusion_skeleton};

/// A single level in a Merkle proof path.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProofStep {
    /// Sibling digests at this level (excluding the path node).
    /// Empty for promoted (lone-child) nodes.
    pub siblings: Vec<Vec<u8>>,
    /// Position of the path node among all children (0-indexed).
    pub position: usize,
}

impl ProofStep {
    /// Project this step's structural shape — position and sibling count —
    /// as a [`crate::topology::SkeletonStep`]. Used by
    /// [`verify_inclusion_path_structure`] to compare against the canonical
    /// skeleton without open-coding the field correspondence.
    #[must_use]
    pub fn shape(&self) -> crate::topology::SkeletonStep {
        crate::topology::SkeletonStep {
            position: self.position,
            sibling_count: self.siblings.len(),
        }
    }
}

/// Inclusion proof: path from a leaf to the root.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InclusionProof {
    /// Path steps from leaf to root.
    pub path: Vec<ProofStep>,
}

/// Timing-safe comparison of two byte slices.
#[inline]
pub fn constant_time_eq(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut result = 0;
    for (&x, &y) in a.iter().zip(b.iter()) {
        result |= std::hint::black_box(x) ^ std::hint::black_box(y);
    }
    std::hint::black_box(result) == 0
}

/// Verify an inclusion proof.
///
/// Returns `true` if the proof demonstrates that `leaf_hash` is the leaf at
/// `index` in a tree of size `tree_size` and arity `arity` whose root is
/// `root`.
///
/// # Trust contract (security-critical)
///
/// `index`, `tree_size`, `arity`, and `root` are **trusted parameters**.
/// Soundness comes from the verifier reconstructing the exact tree topology
/// from `(tree_size, arity, index)` and rejecting any deviation; the proof
/// supplies only sibling digests. These parameters MUST therefore be obtained
/// from an authenticated source — a signed Tree Head (STH) or trusted
/// checkpoint — and never from the proof itself or any caller-untrusted input.
/// If `tree_size`/`index` are attacker-controlled the guarantee is vacuous: the
/// attacker picks the topology the verifier checks against, and an arbitrary
/// `leaf_hash` can be made to "verify" against a matching forged `root`.
///
/// A `true` result binds `leaf_hash` to log position `index` only. The cell's
/// payload and activity are not asserted here — activity is read from the
/// committed epoch timeline (an `epoch` concept), never inferred from a digest.
#[must_use]
pub fn verify_inclusion(
    hasher: &dyn Hasher,
    leaf_hash: &[u8],
    index: u64,
    tree_size: u64,
    arity: u64,
    path: &[ProofStep],
    root: &[u8],
) -> bool {
    reconstruct_inclusion_root(hasher, leaf_hash, index, tree_size, arity, path)
        .is_some_and(|computed| constant_time_eq(&computed, root))
}

/// Validate that the trailing steps of an inclusion proof path match the
/// log-spine skeleton pinned by `(index, tree_size, k)`.
///
/// The skeleton — its length and, per step, the path node's position and sibling
/// count — is derived once by [`inclusion_skeleton`], the single authority on log
/// topology shared with proof generation. The trailing `skeleton.len()` steps are
/// checked field-by-field against it; the leading `path.len() - skeleton.len()`
/// steps are the subtree portion and carry no topological claim here (they are
/// verified by hash chaining in [`reconstruct_inclusion_root`]).
#[must_use]
pub fn verify_inclusion_path_structure(
    k: usize,
    index: u64,
    tree_size: u64,
    path: &[ProofStep],
) -> bool {
    let skeleton = match inclusion_skeleton(k as u64, tree_size, index) {
        Some(s) => s,
        None => return false,
    };
    if path.len() < skeleton.len() {
        return false;
    }
    let d = path.len() - skeleton.len();
    path[d..]
        .iter()
        .zip(skeleton.iter())
        .all(|(step, shape)| step.shape() == *shape)
}

/// Reconstruct the raw root from an inclusion proof path.
///
/// Building block for [`verify_inclusion`]; it computes a root but does not
/// compare it to a trusted one. Callers must hold to the same trust contract:
/// `index`, `tree_size`, and `arity` must be authenticated (see
/// [`verify_inclusion`]), and the returned root is only meaningful when checked
/// against an authenticated root.
#[must_use]
pub fn reconstruct_inclusion_root(
    hasher: &dyn Hasher,
    leaf_hash: &[u8],
    index: u64,
    tree_size: u64,
    arity: u64,
    path: &[ProofStep],
) -> Option<Vec<u8>> {
    let digest_len = hasher.empty().len();
    if digest_len == 0 || digest_len > 64 {
        return None;
    }
    if leaf_hash.len() != digest_len {
        return None;
    }
    if !ARITY_RANGE.contains(&arity) {
        return None;
    }
    if tree_size == 0 {
        return None;
    }
    if index >= tree_size {
        return None;
    }
    if path.len() > 256 {
        return None;
    }

    if !verify_inclusion_path_structure(arity as usize, index, tree_size, path) {
        return None;
    }

    let mut current = leaf_hash.to_vec();

    for step in path {
        if step.siblings.len() > 256 {
            return None;
        }
        for sib in &step.siblings {
            if sib.len() != digest_len {
                return None;
            }
        }
        if step.siblings.is_empty() {
            // Canonical proof encoding: a zero-sibling step would be a promoted
            // (lone-child) node, whose parent equals the child without hashing.
            // Such steps are inert no-ops, so honest provers omit them; rejecting
            // them here makes the accepting path unique for a fixed
            // (leaf_hash, index, tree_size, root). See the module docs.
            return None;
        }
        if step.position > step.siblings.len() {
            return None;
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

    Some(current)
}

#[cfg(test)]
mod tests {
    use sha2::{Digest, Sha256};

    use super::*;

    #[derive(Debug)]
    struct H;
    impl Hasher for H {
        fn leaf(&self, data: &[u8]) -> Vec<u8> {
            Sha256::digest(data).to_vec()
        }

        fn node(&self, children: &[&[u8]]) -> Vec<u8> {
            let mut h = Sha256::new();
            for c in children {
                h.update(c);
            }
            h.finalize().to_vec()
        }

        fn empty(&self) -> Vec<u8> {
            Sha256::digest(b"").to_vec()
        }

        fn hash(&self, data: &[u8]) -> Vec<u8> {
            Sha256::digest(data).to_vec()
        }

        fn clone_box(&self) -> Box<dyn Hasher> {
            Box::new(H)
        }
    }

    /// A zero-sibling (promoted) step is rejected: the accepting path is unique.
    #[test]
    fn zero_sibling_step_is_rejected() {
        let h = H;
        let leaf = h.leaf(b"x");
        let path = vec![ProofStep {
            siblings: vec![],
            position: 0,
        }];
        // A promoted step never reconstructs a root.
        assert_eq!(reconstruct_inclusion_root(&h, &leaf, 0, 2, 2, &path), None);
    }

    /// `constant_time_eq` agrees with `==` on equal and unequal byte slices.
    #[test]
    fn constant_time_eq_matches_equality() {
        assert!(constant_time_eq(b"abc", b"abc"));
        assert!(!constant_time_eq(b"abc", b"abd"));
        assert!(!constant_time_eq(b"abc", b"ab"));
        assert!(constant_time_eq(b"", b""));
    }
}
