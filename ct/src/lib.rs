//! `ct_build` — Certificate Transparency build.
//!
//! EML instantiated at k=2, subtrees banned (flat-leaf only), with a
//! **prefixed `Hasher`** that domain-separates leaf hashes from inner-node
//! hashes to match RFC 9162:
//!
//! - `0x00 ‖ data` for leaf hashes (`leaf`)
//! - `0x01 ‖ left ‖ right` for inner-node hashes (`node`)
//! - `0x02 ‖ b"null"` for the null constant (wrapper so null cannot alias a real leaf payload under
//!   the prefixed scheme)
//!
//! # RFC 9162 root equality
//!
//! A single-algorithm-from-genesis CT build computes a root equal to the
//! RFC 9162 `MTH(D[n])` for the same leaf sequence.  The reduction at play
//! is **promotion**: the binding root has exactly one constituent (a lone
//! child), so canonicalization lifts it in place of the wrapping hashed
//! node.  The binding root therefore reduces to the raw single-algorithm
//! root, which is the RFC 9162 root by construction.
//!
//! # Crypto-agility
//!
//! Epochs and the `add_algorithm` surface are fully active; a second
//! algorithm can be added and will produce a per-algorithm binding root.
//!
//! # Subtrees
//!
//! Subtree appends are not allowed in the CT build.  The log is created
//! with [`new`], which fixes `LogKind::Flat`.

pub use eml::*;

/// CT build arity: binary (`k = 2`).
pub const LOG_ARITY: u64 = 2;

/// CT build configuration: arity `k = 2`.
#[must_use]
pub fn config() -> TreeConfig {
    TreeConfig {
        arity: LOG_ARITY,
    }
}

/// Prefixed `Hasher` that implements RFC 9162 domain separation.
///
/// - Leaf:  `H(0x00 ‖ data)`
/// - Node:  `H(0x01 ‖ c₁ ‖ c₂ ‖ … ‖ cₘ)`
/// - Null:  `H(0x02 ‖ b"null")`
/// - Empty: `H(b"")`
///
/// The underlying `H` is supplied by the caller.  The `PrefixedHasher`
/// wraps any implementation of [`Hasher`] and adds the prefix bytes.
#[derive(Debug)]
pub struct PrefixedHasher<H: Hasher> {
    inner: H,
}

impl<H: Hasher> PrefixedHasher<H> {
    /// Wrap a concrete hasher with RFC 9162 prefix bytes.
    pub fn new(inner: H) -> Self {
        Self { inner }
    }
}

impl<H: Hasher + Clone + 'static> Hasher for PrefixedHasher<H> {
    // Every output is `inner.hash(prefix ‖ …)`, so the width is the inner
    // hasher's width — the prefix changes the preimage, never the digest length.
    fn digest_len(&self) -> usize {
        self.inner.digest_len()
    }

    fn leaf(&self, data: &[u8]) -> Vec<u8> {
        let mut buf = Vec::with_capacity(1 + data.len());
        buf.push(0x00);
        buf.extend_from_slice(data);
        self.inner.hash(&buf)
    }

    fn node(&self, children: &[&[u8]]) -> Vec<u8> {
        let total: usize = children.iter().map(|c| c.len()).sum();
        let mut buf = Vec::with_capacity(1 + total);
        buf.push(0x01);
        for child in children {
            buf.extend_from_slice(child);
        }
        self.inner.hash(&buf)
    }

    fn empty(&self) -> Vec<u8> {
        self.inner.hash(b"")
    }

    // Override null so it uses the 0x02 prefix, distinct from any real leaf.
    fn null(&self) -> Vec<u8> {
        self.inner.hash(b"\x02null")
    }

    fn hash(&self, data: &[u8]) -> Vec<u8> {
        self.inner.hash(data)
    }

    fn clone_box(&self) -> Box<dyn Hasher> {
        Box::new(PrefixedHasher {
            inner: self.inner.clone(),
        })
    }
}

/// Create a new, empty CT build log over `storage`, hashing with `hasher`
/// (wrapped in [`PrefixedHasher`]) under algorithm 0.
///
/// Fixes arity `k = 2`; equivalent to [`NaryMerkleLog::new`] with [`config`].
///
/// # Errors
///
/// Propagates any storage or validation error from [`NaryMerkleLog::new`].
pub async fn new<H: Hasher + Clone + 'static, S: Storage>(
    storage: S,
    hasher: H,
) -> Result<NaryMerkleLog<S>, S::Error> {
    NaryMerkleLog::new(storage, Box::new(PrefixedHasher::new(hasher)), config()).await
}

/// Add a second (or subsequent) algorithm to the CT build log, wrapped in
/// [`PrefixedHasher`].
///
/// # Errors
///
/// Propagates any storage or validation error from [`NaryMerkleLog::add_algorithm`].
pub async fn add_prefixed_algorithm<H: Hasher + Clone + 'static, S: Storage>(
    log: &mut NaryMerkleLog<S>,
    alg_id: u64,
    hasher: H,
) -> Result<(), S::Error> {
    log.add_algorithm(alg_id, Box::new(PrefixedHasher::new(hasher)))
        .await
}

#[cfg(test)]
mod tests {
    use sha2::{Digest, Sha256};

    use super::*;

    // ---------------------------------------------------------------------------
    // Concrete SHA-256 hasher (no prefix — prefix lives in PrefixedHasher).
    // ---------------------------------------------------------------------------

    #[derive(Debug, Clone)]
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

    // ---------------------------------------------------------------------------
    // RFC 9162 MTH reference implementation (standalone, no EML).
    //
    // RFC 9162 §2.1:
    //   MTH({})   = SHA-256("")
    //   MTH({d0}) = SHA-256(0x00 || d0)
    //   MTH(D[n]) = SHA-256(0x01 || MTH(D[0:k]) || MTH(D[k:n]))
    //               where k = largest power of 2 less than n.
    // ---------------------------------------------------------------------------

    fn rfc9162_mth(leaves: &[&[u8]]) -> Vec<u8> {
        match leaves.len() {
            0 => Sha256::digest(b"").to_vec(),
            1 => {
                let mut buf = vec![0x00u8];
                buf.extend_from_slice(leaves[0]);
                Sha256::digest(&buf).to_vec()
            },
            n => {
                // Largest power of 2 less than n.
                let mut k = 1usize;
                while k < n {
                    k <<= 1;
                }
                k >>= 1;

                let left = rfc9162_mth(&leaves[..k]);
                let right = rfc9162_mth(&leaves[k..]);
                let mut buf = vec![0x01u8];
                buf.extend_from_slice(&left);
                buf.extend_from_slice(&right);
                Sha256::digest(&buf).to_vec()
            },
        }
    }

    // ---------------------------------------------------------------------------
    // TDD baseline-failure proof: assert against a wrong reference first.
    //
    // The wrong reference is SHA-256(data) (no prefix), which is what an
    // unprefixed hasher would produce for a 1-leaf log.  The CT build uses
    // 0x00-prefixed leaf hashing, so ct.root() ≠ SHA-256(leaf_data) for any
    // non-empty log.  After fixing to rfc9162_mth the assertion passes.
    // ---------------------------------------------------------------------------

    #[test]
    fn tdd_wrong_reference_fails_then_correct_passes() {
        smol::block_on(async {
            let leaves: &[&[u8]] = &[b"hello"];
            let mut log = new(MemoryStorage::new(), Sha256Hasher).await.unwrap();
            log.append_leaf(leaves[0]).await.unwrap();
            let ct_root = log.root();

            // WRONG reference (plain SHA-256, no prefix): must differ from ct_root.
            // This is the baseline failure that proves the test would catch a bug.
            let wrong = Sha256::digest(leaves[0]).to_vec();
            assert_ne!(
                ct_root, wrong,
                "baseline: ct root must differ from an unprefixed hash"
            );

            // CORRECT reference: RFC 9162 MTH with 0x00-prefixed leaf.
            let correct = rfc9162_mth(leaves);
            assert_eq!(
                ct_root, correct,
                "ct root must equal RFC 9162 MTH for the same leaves"
            );
        });
    }

    // ---------------------------------------------------------------------------
    // CN9-RFC-EQ: ct.root() == rfc9162_mth(leaves) for several sizes.
    //
    // The reduction at play is promotion: the binding root has one constituent
    // (single-algorithm from genesis), so canonicalization lifts the lone child
    // in place of the wrapping hashed node.  The result is the raw per-algorithm
    // root — which equals the RFC 9162 MTH by construction.
    // ---------------------------------------------------------------------------

    #[test]
    fn ct_root_equals_rfc9162_mth() {
        smol::block_on(async {
            let leaf_sets: &[&[&[u8]]] = &[
                // Singleton (non-power-of-2, degenerate).
                &[b"a"],
                // Exact power of 2.
                &[b"a", b"b"],
                &[b"a", b"b", b"c", b"d"],
                // Non-powers-of-2.
                &[b"a", b"b", b"c"],
                &[b"a", b"b", b"c", b"d", b"e"],
                &[b"a", b"b", b"c", b"d", b"e", b"f", b"g"],
            ];

            for &leaves in leaf_sets {
                let mut log = new(MemoryStorage::new(), Sha256Hasher).await.unwrap();
                for &leaf in leaves {
                    log.append_leaf(leaf).await.unwrap();
                }
                let ct_root = log.root();
                let expected = rfc9162_mth(leaves);
                assert_eq!(
                    ct_root,
                    expected,
                    "CT root must equal RFC 9162 MTH for {} leaves",
                    leaves.len()
                );
            }
        });
    }

    // ---------------------------------------------------------------------------
    // CN9-AGILITY: a second algorithm can activate and produce a binding root.
    //
    // Add algorithm 1 after some leaves, append more leaves, then call
    // combined_root_for(1) to get a per-algorithm binding root distinct from
    // the raw single-algorithm root.
    // ---------------------------------------------------------------------------

    #[test]
    fn crypto_agility_second_algorithm() {
        smol::block_on(async {
            let mut log = new(MemoryStorage::new(), Sha256Hasher).await.unwrap();

            // Phase 1: some leaves under algorithm 0 only.
            log.append_leaf(b"a").await.unwrap();
            log.append_leaf(b"b").await.unwrap();

            // Activate algorithm 1 (a second PrefixedHasher with the same
            // underlying function — in practice a different hash algorithm).
            add_prefixed_algorithm(&mut log, 1, Sha256Hasher)
                .await
                .unwrap();

            // Phase 2: more leaves, both algorithms active.
            log.append_leaf(b"c").await.unwrap();
            log.append_leaf(b"d").await.unwrap();

            // Algorithm 0's raw root.
            let root0 = log.root_for(0).unwrap();
            // Algorithm 1's raw root (only covers leaves [2,4)).
            let root1 = log.root_for(1).unwrap();

            // The two raw roots must differ: algorithm 1 activated at leaf 2,
            // so its history is shorter.
            assert_ne!(root0, root1, "roots must differ: algorithm 1 is newer");

            // Each algorithm produces a binding root via combined_root_for.
            // With two active algorithms the binding root differs from the raw
            // root (promotion no longer applies — two constituents → hashed).
            let binding0 = log.combined_root_for(0).await.unwrap();
            let binding1 = log.combined_root_for(1).await.unwrap();

            // Binding roots are non-empty.
            assert!(!binding0.is_empty(), "binding root 0 must be non-empty");
            assert!(!binding1.is_empty(), "binding root 1 must be non-empty");

            // Binding roots differ from each raw root (they commit both
            // algorithms' roots under the respective hash function).
            assert_ne!(
                binding0, root0,
                "binding root 0 must differ from raw root 0 when two algorithms are active"
            );
        });
    }

    // ---------------------------------------------------------------------------
    // Sanity: the prefixed hasher domain-separates leaves from nodes.
    // ---------------------------------------------------------------------------

    #[test]
    fn prefixed_hasher_domain_separation() {
        let h = PrefixedHasher::new(Sha256Hasher);

        let leaf_hash = h.leaf(b"abc");
        // Manually compute what the prefixed hasher should produce.
        let expected_leaf = Sha256::digest(b"\x00abc").to_vec();
        assert_eq!(leaf_hash, expected_leaf);

        let node_hash = h.node(&[&leaf_hash, &leaf_hash]);
        let mut buf = vec![0x01u8];
        buf.extend_from_slice(&leaf_hash);
        buf.extend_from_slice(&leaf_hash);
        let expected_node = Sha256::digest(&buf).to_vec();
        assert_eq!(node_hash, expected_node);

        // Leaf and node of same content must differ.
        assert_ne!(leaf_hash, node_hash);
    }

    // ---------------------------------------------------------------------------
    // Preset smoke-test.
    // ---------------------------------------------------------------------------

    #[test]
    fn preset_is_binary() {
        assert_eq!(config().arity, 2);
    }
}
