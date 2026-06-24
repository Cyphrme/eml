//! Merkle root and evaluation over the n-ary subtree, with canonicalization.
//!
//! Canonicalization is one generic reduction composed of **two distinct
//! primitives**, applied structurally on every fold (always-on, never a
//! toggle):
//!
//! - **promotion** — a lone (single) child is lifted in place of the wrapping hashed node.
//!   Structurally deterministic: a verifier re-derives it.
//! - **collapse** — children of the *same value* fold to that value. The all-null case is *one
//!   instance* of general same-value collapse, not a separate operation; an all-null run is just
//!   the dominant instance in a sparse log.
//!
//! The literal `nary_mr` symbol predates this vocabulary and is kept verbatim;
//! the two primitives are named in this prose, not split in the code here.

use crate::hasher::Hasher;
use crate::proof::ProofStep;
use crate::subtree::Subtree;

/// Compute the Merkle root of an ordered sequence of child digests.
///
/// Applies the two canonicalization primitives: **promotion** (the lone-child
/// case) and **collapse** (the same-value fold). Collapse is general —
/// *any* run of equal children folds to that value, with the all-null run the
/// dominant instance in a sparse log, not a special case. The collapse is
/// value-dependent and always-on; there is no toggle.
///
/// The collapsed value's *multiplicity* (how many leaves the run spans) is not
/// in the digest — it is committed separately as the minimal run-extent
/// (INV-AUTH-BOUNDARY), so distinct equal-entry runs are never conflated on
/// unroll. For non-null runs that extent is mirrored across every algorithm's
/// tree (equal logical data ⇒ equal digest under every hash) and rides free;
/// only null runs are per-tree-divergent and are committed (the null-run-extents
/// in the binding root).
#[must_use]
pub fn nary_mr(hasher: &dyn Hasher, children: &[&[u8]]) -> Vec<u8> {
    match children.len() {
        0 => hasher.empty(),
        1 => children[0].to_vec(),
        _ => {
            // Fixed-width contract (see `Hasher`): the node hash concatenates
            // these child digests with no length prefix, so the child *boundaries*
            // are recoverable only if the children share a width — otherwise a
            // different split of the same bytes is an equally valid child list and
            // the node digest fails to bind its children. Checked here, at the one
            // fold boundary, so a contract violation trips in debug/test builds
            // rather than silently producing an unbinding root.
            //
            // The check is mutual sibling-width-equality, not equality to
            // `hasher.digest_len()`: a binding-root node folds *other* algorithms'
            // member roots (raw, opaque digests — D9) under this hasher, so the
            // children are not this hasher's own outputs. Within a single tree
            // they are, and either way the soundness property is that the siblings
            // agree on a width.
            debug_assert!(
                children.windows(2).all(|w| w[0].len() == w[1].len()),
                "node() children must share a digest width (got widths {:?}); the unprefixed \
                 concatenation is otherwise not uniquely parseable",
                children.iter().map(|c| c.len()).collect::<Vec<_>>()
            );
            // Collapse: if every child is the same value, the parent is that
            // value. The all-null run is the dominant instance of this one rule.
            let first = children[0];
            if children.iter().all(|&c| c == first) {
                first.to_vec()
            } else {
                hasher.node(children)
            }
        },
    }
}

/// Recursively evaluate the root hash of a structured subtree.
#[must_use]
pub fn evaluate(hasher: &dyn Hasher, subtree: &Subtree) -> Vec<u8> {
    match subtree {
        Subtree::Leaf(data) => hasher.leaf(data),
        Subtree::Node(children) => {
            let child_hashes: Vec<Vec<u8>> = children.iter().map(|c| evaluate(hasher, c)).collect();
            let child_refs: Vec<&[u8]> = child_hashes.iter().map(|c| c.as_slice()).collect();
            nary_mr(hasher, &child_refs)
        },
    }
}

/// Count the total number of leaves in a structured subtree.
#[must_use]
pub fn count_leaves(subtree: &Subtree) -> u64 {
    match subtree {
        Subtree::Leaf(_) => 1,
        Subtree::Node(children) => children.iter().map(count_leaves).sum(),
    }
}

/// Generate the inclusion proof path for a leaf index within a structured subtree.
///
/// Returns `Some(path)` if the leaf index is found in the subtree, otherwise `None`.
/// The `leaf_index` represents the flat 0-based leaf index inside this subtree.
#[must_use]
pub fn within_subtree_path(
    hasher: &dyn Hasher,
    subtree: &Subtree,
    leaf_index: u64,
) -> Option<Vec<ProofStep>> {
    match subtree {
        Subtree::Leaf(_) => {
            if leaf_index == 0 {
                Some(Vec::new())
            } else {
                None
            }
        },
        Subtree::Node(children) => {
            let mut cumulative_leaves = 0;
            for (child_idx, child) in children.iter().enumerate() {
                let child_leaves = count_leaves(child);
                if leaf_index < cumulative_leaves + child_leaves {
                    let mut path =
                        within_subtree_path(hasher, child, leaf_index - cumulative_leaves)?;

                    // Canonical proof encoding: a promoted (lone-child) node is
                    // lifted to its parent without hashing, so it contributes no
                    // proof step (the recursion already returns the correct
                    // sub-path). Only genuinely hashing (multi-child) nodes emit
                    // a step.
                    if children.len() > 1 {
                        let mut child_hashes = Vec::with_capacity(children.len());
                        for c in children {
                            child_hashes.push(evaluate(hasher, c));
                        }
                        child_hashes.remove(child_idx);
                        path.push(ProofStep {
                            siblings: child_hashes,
                            position: child_idx,
                        });
                    }
                    return Some(path);
                }
                cumulative_leaves += child_leaves;
            }
            None
        },
    }
}

#[cfg(test)]
mod tests {
    use sha2::{Digest, Sha256};

    use super::*;

    #[derive(Debug)]
    struct Sha256Hasher;

    impl Hasher for Sha256Hasher {
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

        fn clone_box(&self) -> Box<dyn Hasher> {
            Box::new(Sha256Hasher)
        }
    }

    #[test]
    fn test_nary_mr_empty() {
        let hasher = Sha256Hasher;
        let expected = Sha256::digest(b"").to_vec();
        assert_eq!(nary_mr(&hasher, &[]), expected);
    }

    #[test]
    fn test_nary_mr_promotion() {
        let hasher = Sha256Hasher;
        let leaf_hash = hasher.leaf(b"hello");
        assert_eq!(nary_mr(&hasher, &[&leaf_hash]), leaf_hash);
    }

    #[test]
    fn test_nary_mr_null_collapse() {
        let hasher = Sha256Hasher;
        let null = hasher.null();
        // A node with two null children should collapse to null
        assert_eq!(nary_mr(&hasher, &[&null, &null]), null);

        // A node with a mix of null and non-null should NOT collapse to null
        let leaf = hasher.leaf(b"hello");
        let expected = hasher.node(&[&null, &leaf]);
        assert_eq!(nary_mr(&hasher, &[&null, &leaf]), expected);
    }

    #[test]
    fn test_nary_mr_general_same_value_collapse() {
        let hasher = Sha256Hasher;
        // General collapse: all children EQUAL to the same non-null value fold to
        // that value. Null is one instance of this, not the rule.
        let v = hasher.leaf(b"hello");
        assert_eq!(nary_mr(&hasher, &[&v, &v]), v);
        assert_eq!(nary_mr(&hasher, &[&v, &v, &v]), v);

        // A mix of two distinct non-null values must NOT collapse — it hashes.
        let w = hasher.leaf(b"world");
        let expected = hasher.node(&[&v, &w]);
        assert_eq!(nary_mr(&hasher, &[&v, &w]), expected);
        assert_ne!(nary_mr(&hasher, &[&v, &w]), v);

        // The null collapse is exactly the same rule at value = null().
        let null = hasher.null();
        assert_eq!(nary_mr(&hasher, &[&null, &null]), null);
    }

    #[test]
    fn null_is_distinct_from_empty_data_leaf() {
        // Hard constraint: null() = H(b"null") MUST stay distinct from a genuine
        // empty-data leaf leaf(b"") = H(b""), so the null subset of collapses is
        // unambiguous. The preimages differ (4 bytes vs 0), so the digests differ.
        let hasher = Sha256Hasher;
        assert_ne!(hasher.null(), hasher.leaf(b""));
        // And a two-empty-leaf node collapses to the empty-leaf value (general
        // collapse), which is itself distinct from null() — collapse never
        // conflates an empty-data run with a null run.
        let empty_leaf = hasher.leaf(b"");
        assert_eq!(nary_mr(&hasher, &[&empty_leaf, &empty_leaf]), empty_leaf);
        assert_ne!(nary_mr(&hasher, &[&empty_leaf, &empty_leaf]), hasher.null());
    }

    #[test]
    fn test_evaluate_promotion_chain() {
        let hasher = Sha256Hasher;
        // Node([Node([Leaf("x")])])
        let tree = Subtree::Node(vec![Subtree::Node(vec![Subtree::Leaf(b"x".to_vec())])]);
        let expected = hasher.leaf(b"x");
        assert_eq!(evaluate(&hasher, &tree), expected);
    }

    #[test]
    fn test_within_subtree_path() {
        let hasher = Sha256Hasher;
        // Subtree: Node([Leaf("a"), Node([Leaf("b"), Leaf("c")]), Leaf("d")])
        let subtree = Subtree::Node(vec![
            Subtree::Leaf(b"a".to_vec()),
            Subtree::Node(vec![
                Subtree::Leaf(b"b".to_vec()),
                Subtree::Leaf(b"c".to_vec()),
            ]),
            Subtree::Leaf(b"d".to_vec()),
        ]);

        let path = within_subtree_path(&hasher, &subtree, 1).unwrap();
        assert_eq!(path.len(), 2);

        let leaf_hash = hasher.leaf(b"b");
        let root = evaluate(&hasher, &subtree);
        let proof = crate::proof::InclusionProof { path };
        assert!(crate::proof::verify_inclusion(
            &hasher,
            &leaf_hash,
            0,
            1,
            2,
            &proof.path,
            &root
        ));
    }
}
