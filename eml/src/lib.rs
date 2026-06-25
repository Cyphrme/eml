//! `eml` — the Epoch Merkle Log: a general-purpose append-only log.
//!
//! The EML library — the [`epoch`] combinator over the [`cml`](epoch) single-
//! algorithm engine — instantiated at arity `k = 2`, no prefix (the caller's
//! [`Hasher`] is used directly, with no domain-separation wrapper). It is the
//! behavioral successor of the historical `neml` crate and reproduces its
//! outputs byte-for-byte.
//!
//! The full EML surface is re-exported, so a consumer reaches the library
//! through `eml::*`. The instantiation's only opinion is the arity: the
//! [`config`] preset and [`new`]/[`from_storage`] constructors fix `k = 2`,
//! while the re-exported [`NaryMerkleLog`] still accepts any [`TreeConfig`] for
//! callers that need a different arity.

pub use epoch::*;
// The combinator driver's storage-parameterised error/result are the EML
// library's public `Error`/`Result` (the combinator also has a distinct,
// non-parameterised snapshot `Error`, not re-exported under this name).
pub use epoch::{LogError as Error, LogResult as Result};

/// The EML library's error surface, reached through `eml::error::*`. The
/// driver's storage-parameterised [`LogError`](epoch::LogError) is the public
/// `Error`; this module preserves the `eml::error::Error` path the historical
/// surface exposed.
pub mod error {
    pub use epoch::{LogError as Error, LogResult as Result};
}

/// The log arity: binary (`k = 2`).
pub const LOG_ARITY: u64 = 2;

/// The EML configuration: arity `k = 2`, no prefix.
#[must_use]
pub fn config() -> TreeConfig {
    TreeConfig { arity: LOG_ARITY }
}

/// Create a new, empty log over `storage`, hashing with `hasher` under
/// algorithm 0.
///
/// Fixes the instantiation's arity (`k = 2`); equivalent to
/// [`NaryMerkleLog::new`] with [`config`].
///
/// # Errors
///
/// Propagates any storage or validation error from [`NaryMerkleLog::new`].
pub async fn new<S: Storage>(
    storage: S,
    hasher: Box<dyn Hasher>,
) -> Result<NaryMerkleLog<S>, S::Error> {
    NaryMerkleLog::new(storage, hasher, config()).await
}

/// Reconstruct an existing log from `storage` at the EML arity
/// (`k = 2`).
///
/// Equivalent to [`NaryMerkleLog::from_storage_with_config`] with [`config`].
///
/// # Errors
///
/// Propagates any storage or validation error from reconstruction.
pub async fn from_storage<S: Storage>(
    storage: S,
    hashers: Vec<(u64, Box<dyn Hasher>)>,
) -> Result<NaryMerkleLog<S>, S::Error> {
    NaryMerkleLog::from_storage_with_config(storage, hashers, config()).await
}

#[cfg(test)]
mod tests {
    use epoch::MemoryStorage;
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

    /// The preset fixes binary arity.
    #[test]
    fn preset_is_binary() {
        assert_eq!(config().arity, 2);
    }

    /// The preset constructor builds a working binary log.
    #[test]
    fn new_builds_binary_log() {
        smol::block_on(async {
            let mut log = new(MemoryStorage::new(), Box::new(Sha256Hasher))
                .await
                .unwrap();
            assert_eq!(log.config().arity, 2);
            log.append_leaf(b"a").await.unwrap();
            log.append_leaf(b"b").await.unwrap();
            assert_eq!(log.size(), 2);
            // A binary tree of two leaves has a single internal-node root.
            let root = log.root();
            let expected = Sha256Hasher.node(&[
                Sha256Hasher.leaf(b"a").as_slice(),
                Sha256Hasher.leaf(b"b").as_slice(),
            ]);
            assert_eq!(root, expected);
        });
    }
}
