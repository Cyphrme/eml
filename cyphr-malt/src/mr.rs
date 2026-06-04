//! Merkle root and evaluation algorithms for unified n-ary trees.

use crate::hasher::Hasher;
use crate::proof::ProofStep;
use crate::subtree::Subtree;

/// Compute the Merkle root of an ordered sequence of child digests.
///
/// Applies singleton promotion (Definition 2) and null promotion.
#[must_use]
pub fn nary_mr(hasher: &dyn Hasher, children: &[&[u8]]) -> Vec<u8> {
    match children.len() {
        0 => hasher.empty(),
        1 => children[0].to_vec(),
        _ => {
            // Null promotion: if all children are N₀, parent is N₀.
            let null_const = hasher.null();
            if children.iter().all(|&c| c == null_const) {
                null_const
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
pub fn within_commit_path(
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
        }
        Subtree::Node(children) => {
            let mut cumulative_leaves = 0;
            for (child_idx, child) in children.iter().enumerate() {
                let child_leaves = count_leaves(child);
                if leaf_index < cumulative_leaves + child_leaves {
                    let mut path = within_commit_path(
                        hasher,
                        child,
                        leaf_index - cumulative_leaves,
                    )?;
                    
                    if children.len() == 1 {
                        // Promoted node
                        path.push(ProofStep {
                            siblings: Vec::new(),
                            position: 0,
                        });
                    } else {
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
        }
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

        fn null(&self) -> Vec<u8> {
            Sha256::digest([0x02]).to_vec()
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
    fn test_nary_mr_singleton_promotion() {
        let hasher = Sha256Hasher;
        let leaf_hash = hasher.leaf(b"hello");
        assert_eq!(nary_mr(&hasher, &[&leaf_hash]), leaf_hash);
    }

    #[test]
    fn test_nary_mr_null_promotion() {
        let hasher = Sha256Hasher;
        let null = hasher.null();
        // A node with two null children should evaluate to null
        assert_eq!(nary_mr(&hasher, &[&null, &null]), null);

        // A node with a mix of null and non-null should NOT evaluate to null
        let leaf = hasher.leaf(b"hello");
        let expected = hasher.node(&[&null, &leaf]);
        assert_eq!(nary_mr(&hasher, &[&null, &leaf]), expected);
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
    fn test_within_commit_path() {
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

        let path = within_commit_path(&hasher, &subtree, 1).unwrap();
        assert_eq!(path.len(), 2);

        let leaf_hash = hasher.leaf(b"b");
        let root = evaluate(&hasher, &subtree);
        let proof = crate::proof::InclusionProof {
            index: 1,
            tree_size: 4,
            path,
        };
        assert!(crate::proof::verify_inclusion(&hasher, &leaf_hash, &proof, &root));
    }
}
