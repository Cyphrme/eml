//! `seal` — freezing an append-only log into the one kernel currency
//! [`pmt::Sealed`].
//!
//! There is exactly one commitment currency. A mutable `Emt` (from the `emt`
//! crate) and this append-only log both seal into [`pmt::Sealed`]; the kernel
//! computes the resumable frontier for the mutable tree at seal, so every
//! `Sealed` uniformly carries a frontier whatever sealed it. An append-only log
//! already holds its frontier natively, so its seal simply freezes the active
//! algorithms' frontier peaks at the sealed size.
//!
//! The seal is one-way: it consumes the log and there is no path back to one
//! (C-SEAL-ONEWAY). The way *forward* from a `Sealed` is the orthogonal
//! operation set keyed by what each needs:
//!
//! - **verify** — the proofs ([`crate::snapshot_proof`], binding/leaf/consistency) check against
//!   the `Sealed`'s derived roots; needs nothing but the `Sealed`;
//! - **resume** ([`NaryMerkleLog::resume`]) — needs only the frontier (which the `Sealed` *is*);
//!   reopens an append-only log onto the committed frontier;
//! - **[`fill`](crate::fill)** — needs the real leaf data; rebuilds a full, readable tree and
//!   verifies it against the committed binding root.
//!
//! # What a seal commits
//!
//! For every algorithm active at the sealed size (its epoch covers the final
//! position) the seal freezes that algorithm's **frontier peaks** — the digests
//! of the perfect k-ary subtrees [`frontier_for_size`] names — together with the
//! committed epoch timeline and an optional opaque metadata payload
//! ([`pmt::Meta`], where an out-of-band tree-head attestation may ride). The
//! member root, binding root, and run-extents are *derived views* of the
//! `Sealed`, not stored (see [`pmt::Sealed`]).

use pmt::{Meta, Sealed, frontier_for_size};

use crate::error::Result;
use crate::storage::Storage;
use crate::tree::NaryMerkleLog;

impl<S: Storage> NaryMerkleLog<S> {
    /// Seal this log into the kernel currency [`Sealed`] at its current size,
    /// consuming the log.
    ///
    /// Freezes the frontier peaks of every algorithm active at the sealed size
    /// and the committed epoch timeline. The transition is one-way: the log is
    /// consumed and a `Sealed` cannot be walked back to a log (C-SEAL-ONEWAY).
    ///
    /// To attach an optional opaque metadata payload (where a tree-head
    /// attestation may ride), use [`Self::seal_with_meta`].
    ///
    /// # Errors
    ///
    /// Returns a storage error if a frontier node cannot be read.
    pub async fn seal(self) -> Result<Sealed, S::Error> {
        self.seal_inner(None).await
    }

    /// Seal this log into [`Sealed`], attaching an opaque metadata payload,
    /// consuming the log.
    ///
    /// Identical to [`Self::seal`] except the `Sealed` carries `meta`. The
    /// library never reads or validates the payload; any byte sequence is
    /// accepted (INV-METADATA-AGNOSTIC).
    ///
    /// # Errors
    ///
    /// As [`Self::seal`].
    pub async fn seal_with_meta(self, meta: Meta) -> Result<Sealed, S::Error> {
        self.seal_inner(Some(meta)).await
    }

    /// Shared seal body: gather the active algorithms' frontier peaks and the
    /// committed timeline, then build the one-way [`Sealed`]. Consumes `self`.
    async fn seal_inner(self, meta: Option<Meta>) -> Result<Sealed, S::Error> {
        let size = self.count();
        let k = self.config().log_arity as u64;

        // At size 0 there is no active algorithm and no timeline to freeze.
        let (frontiers, alg_epochs) = if size == 0 {
            (Vec::new(), Vec::new())
        } else {
            let alg_epochs = self.committed_epochs_at(size);
            let coords = frontier_for_size(size, k);

            // Only algorithms active at the sealed size contribute a frontier.
            let mut frontiers = Vec::new();
            for &(id, _) in &alg_epochs {
                if let Some(true) = crate::proof::committed_active_at(&alg_epochs, id, size - 1) {
                    let mut peaks = Vec::with_capacity(coords.len());
                    for &(left, height) in &coords {
                        peaks.push(self.peak_at(id, left, height).await?);
                    }
                    frontiers.push((id, peaks));
                }
            }
            (frontiers, alg_epochs)
        };

        let sealed = Sealed::new(size, k, frontiers, alg_epochs)
            .map_err(|_| crate::error::Error::MalformedSeal)?;
        Ok(match meta {
            Some(m) => sealed.with_meta(m),
            None => sealed,
        })
    }
}

#[cfg(test)]
mod tests {
    use pmt::Hasher;
    use sha2::{Digest, Sha256};

    use super::*;
    use crate::storage::MemoryStorage;
    use crate::tree::TreeConfig;

    /// A real fixed-width (32-byte) hasher — the crate's canonical test hasher.
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
            Box::new(self.clone())
        }
    }

    async fn log_with(n: u64, k: usize) -> NaryMerkleLog<MemoryStorage> {
        let config = TreeConfig { log_arity: k };
        let mut log = NaryMerkleLog::new(MemoryStorage::new(), Box::new(Sha256Hasher), config)
            .await
            .unwrap();
        for i in 0..n {
            log.append_leaf(format!("leaf-{i}").as_bytes())
                .await
                .unwrap();
        }
        log
    }

    // The sealed frontier's folded member root equals the live per-algorithm
    // root, and its derived binding root equals the live combined root — the
    // representation change preserves every committed digest.
    #[test]
    fn folded_member_root_equals_live_root_across_sizes() {
        smol::block_on(async {
            let h = Sha256Hasher;
            let hashers: [(u64, &dyn Hasher); 1] = [(0, &h)];
            for k in [2usize, 3, 4] {
                for n in 1u64..30 {
                    let log = log_with(n, k).await;
                    let live_root = log.root_for_at(0, n).await.unwrap();
                    let live_combined = log.combined_root_at(0, n).await.unwrap();
                    let sealed = log.seal().await.unwrap();
                    assert_eq!(
                        sealed.member_root(0, &h),
                        Some(live_root),
                        "folded member root must equal live root (n={n}, k={k})"
                    );
                    assert_eq!(
                        sealed.binding_root(0, &h, &hashers),
                        Some(live_combined),
                        "derived binding root must equal live combined root (n={n}, k={k})"
                    );
                }
            }
        });
    }

    #[test]
    fn empty_log_seals_to_empty_frontier() {
        smol::block_on(async {
            let log = log_with(0, 2).await;
            let sealed = log.seal().await.unwrap();
            assert_eq!(sealed.tree_size(), 0);
            assert!(sealed.frontiers().is_empty());
            assert!(sealed.alg_epochs().is_empty());
            assert!(sealed.run_extents().is_empty());
        });
    }

    #[test]
    fn run_extents_match_frontier_minus_promotions() {
        smol::block_on(async {
            for k in [2usize, 3, 4] {
                for n in 1u64..30 {
                    let log = log_with(n, k).await;
                    let sealed = log.seal().await.unwrap();
                    let expected: Vec<(u64, u32)> = frontier_for_size(n, k as u64)
                        .into_iter()
                        .filter(|&(_, h)| h >= 1)
                        .collect();
                    let got: Vec<(u64, u32)> = sealed
                        .run_extents()
                        .iter()
                        .map(|e| (e.left(), e.height()))
                        .collect();
                    assert_eq!(got, expected, "n={n}, k={k}");
                }
            }
        });
    }

    #[test]
    fn opaque_meta_round_trips() {
        smol::block_on(async {
            let payload: Vec<u8> = (0u8..=255).collect();
            let log = log_with(3, 2).await;
            let sealed = log
                .seal_with_meta(Meta::new(payload.clone()))
                .await
                .unwrap();
            assert_eq!(sealed.meta().map(Meta::as_bytes), Some(payload.as_slice()));
        });
    }

    #[test]
    fn binding_root_per_active_algorithm() {
        smol::block_on(async {
            let config = TreeConfig { log_arity: 2 };
            let mut log = NaryMerkleLog::new(MemoryStorage::new(), Box::new(Sha256Hasher), config)
                .await
                .unwrap();
            log.add_algorithm(1, Box::new(Sha256Hasher)).await.unwrap();
            for i in 0..4u64 {
                log.append_leaf(&i.to_be_bytes()).await.unwrap();
            }
            let size = log.count();
            let br0 = log.combined_root_at(0, size).await.unwrap();
            let br1 = log.combined_root_at(1, size).await.unwrap();
            let sealed = log.seal().await.unwrap();
            let h = Sha256Hasher;
            let hashers: [(u64, &dyn Hasher); 2] = [(0, &h), (1, &h)];
            // Two active algorithms; the timeline is no longer the promoted
            // registry-singleton, so binding roots take the hashed form.
            let brs = sealed.binding_roots(&hashers);
            assert_eq!(brs.len(), 2);
            assert_eq!(sealed.binding_root(0, &h, &hashers), Some(br0));
            assert_eq!(sealed.binding_root(1, &h, &hashers), Some(br1));
            // Unknown algorithm: no frontier, no binding root.
            assert_eq!(sealed.binding_root(9, &h, &hashers), None);
        });
    }
}
