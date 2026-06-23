//! `Snapshot` — the third seal level: a frozen, immutable materialization of an
//! append-only log at a point in time (the "stateless cutoff").
//!
//! The seal chain is monotonic and forward-only: a mutable construction seals to
//! the kernel carrier ([`pmt::Sealed`]), an append-only log consumes that, and a
//! log seals to a [`Snapshot`]. Each step consumes `self`; **no step has an
//! inverse**. A `Snapshot` exposes read accessors only — no constructor walks
//! back to a log (C-SEAL-ONEWAY).
//!
//! # What a snapshot commits
//!
//! A snapshot is the minimal, authenticated basis the operator-level `fill` step
//! unrolls from. It carries exactly three things:
//!
//! - the **binding root** of every algorithm active at the sealed size — each a top-level node
//!   computed with that algorithm's own hash, the head the rest of the structure authenticates
//!   against (it is the log's live binding root at the sealed size, frozen, not a freshly
//!   recomputed one);
//! - the **committed canonicalization run-extents** — the minimal record of how the canonical form
//!   was reached, namely the contiguous-collapse runs. Promotion commits nothing (a singleton leaf
//!   is structurally deterministic); a collapse commits its run-extent. The run-extents are
//!   *derived* from the sealed size and the arity, never inferred from a digest or a node's shape;
//! - an **opaque metadata** payload ([`pmt::Meta`]) the library never interprets — the channel an
//!   optional tree-head attestation may ride on.

use pmt::metadata::Meta;
use pmt::topology::frontier_for_size;

use crate::error::Result;
use crate::storage::Storage;
use crate::tree::NaryMerkleLog;

/// One committed canonicalization run-extent: a contiguous collapse of `k^height`
/// consecutive leaves into a single subtree, beginning at leaf index `left`.
///
/// A run-extent is emitted only for a *collapse* — a node above leaf level
/// (`height >= 1`). A promoted singleton leaf (`height == 0`) is structurally
/// deterministic and commits no run-extent (INV-AUTH-BOUNDARY: promotion commits
/// nothing, collapse commits its minimal run-extent), so it never appears here.
///
/// The extent is the minimal metadata the `fill` step unrolls from: it says how
/// many real historical leaves a stored subtree root stands for, so a complete
/// (gapless) history can be recomputed without inferring shape from the digest.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RunExtent {
    /// Index of the first leaf the run collapses.
    left: u64,
    /// Height of the collapsed subtree; the run spans `k.pow(height)` leaves.
    /// Always `>= 1` — a height-0 node is a promotion, not a collapse.
    height: u32,
}

impl RunExtent {
    /// Index of the first leaf this run collapses.
    #[must_use]
    pub fn left(&self) -> u64 {
        self.left
    }

    /// Height of the collapsed subtree. The run spans `k.pow(height)` leaves.
    #[must_use]
    pub fn height(&self) -> u32 {
        self.height
    }

    /// Number of leaves this run collapses, given the log arity `k`.
    #[must_use]
    pub fn span(&self, k: u64) -> u64 {
        k.pow(self.height)
    }
}

/// A frozen, immutable materialization of an append-only log at the size it was
/// sealed at — the stateless cutoff.
///
/// Construct one only by sealing a log ([`NaryMerkleLog::seal_snapshot`]), which
/// consumes the log. A `Snapshot` exposes read borrows of what it committed and
/// nothing else: there is no field mutator and no path back to a log, so the
/// seal is one-way (C-SEAL-ONEWAY).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Snapshot {
    /// The size the log was sealed at.
    tree_size: u64,
    /// Log arity `k`; fixes how a run-extent's height maps to a leaf span.
    log_arity: u64,
    /// The raw member root of each algorithm active at the sealed size, sorted
    /// by algorithm ID: `(alg_id, raw_root)`. These are the leaves the binding
    /// roots are built over.
    active_roots: Vec<(u64, Vec<u8>)>,
    /// The committed epoch timeline of every algorithm registered by the sealed
    /// size, sorted by algorithm ID. Bound into each binding root.
    alg_epochs: Vec<(u64, Vec<(u64, u64)>)>,
    /// The binding root of each algorithm active at the sealed size, sorted by
    /// algorithm ID: `(alg_id, binding_root)`. Each is the top-level node of
    /// that algorithm's tree under its own hash.
    binding_roots: Vec<(u64, Vec<u8>)>,
    /// The committed canonicalization run-extents: every contiguous-collapse run
    /// the canonical form reached at the sealed size, in left-to-right order.
    /// Minimal — promotions are omitted — and derivable from `(tree_size, k)`.
    run_extents: Vec<RunExtent>,
    /// Opaque metadata channel; the library never inspects the contents. An
    /// optional tree-head attestation may ride here.
    meta: Option<Meta>,
}

impl Snapshot {
    /// The size the log was sealed at.
    #[must_use]
    pub fn tree_size(&self) -> u64 {
        self.tree_size
    }

    /// The log arity `k` the snapshot was sealed under.
    #[must_use]
    pub fn log_arity(&self) -> u64 {
        self.log_arity
    }

    /// The binding root of every algorithm active at the sealed size, sorted by
    /// algorithm ID. Each is the head the rest of the structure authenticates
    /// against.
    #[must_use]
    pub fn binding_roots(&self) -> &[(u64, Vec<u8>)] {
        &self.binding_roots
    }

    /// The binding root of a single algorithm at the sealed size, if it was
    /// active there.
    #[must_use]
    pub fn binding_root(&self, alg_id: u64) -> Option<&[u8]> {
        self.binding_roots
            .iter()
            .find(|(id, _)| *id == alg_id)
            .map(|(_, r)| r.as_slice())
    }

    /// The committed canonicalization run-extents — the minimal record the
    /// `fill` step unrolls from. Promotions are omitted (they commit nothing);
    /// every entry is a contiguous collapse with its run-extent.
    #[must_use]
    pub fn run_extents(&self) -> &[RunExtent] {
        &self.run_extents
    }

    /// A read borrow of the sealed active member roots, `(alg_id, raw_root)`.
    #[must_use]
    pub fn active_roots(&self) -> &[(u64, Vec<u8>)] {
        &self.active_roots
    }

    /// A read borrow of the sealed committed epoch timeline.
    #[must_use]
    pub fn alg_epochs(&self) -> &[(u64, Vec<(u64, u64)>)] {
        &self.alg_epochs
    }

    /// The opaque metadata attached at seal time, if any. The library never
    /// interprets the bytes; an optional tree-head attestation may ride here.
    #[must_use]
    pub fn meta(&self) -> Option<&Meta> {
        self.meta.as_ref()
    }
}

impl<S: Storage> NaryMerkleLog<S> {
    /// Seal this log into an immutable [`Snapshot`] at its current size,
    /// consuming the log.
    ///
    /// This is the third and final seal level (the others seal a mutable tree to
    /// the kernel carrier and that carrier into a log). The transition is
    /// one-way: the log is consumed and a `Snapshot` cannot be walked back to a
    /// log (C-SEAL-ONEWAY).
    ///
    /// The snapshot freezes the binding root of every active algorithm and the
    /// committed canonicalization run-extents — the minimal basis `fill` unrolls
    /// from. The run-extents are *derived* from the sealed size and the arity
    /// (the contiguous-collapse frontier geometry), never inferred from a digest
    /// or a node's shape.
    ///
    /// To attach an optional opaque metadata payload (where a tree-head
    /// attestation may ride), pass it via [`Self::seal_snapshot_with_meta`].
    ///
    /// # Errors
    ///
    /// Returns a storage error if a binding root or member root cannot be read.
    pub async fn seal_snapshot(self) -> Result<Snapshot, S::Error> {
        self.seal_snapshot_inner(None).await
    }

    /// Seal this log into an immutable [`Snapshot`], attaching an opaque metadata
    /// payload, consuming the log.
    ///
    /// Identical to [`Self::seal_snapshot`] except the snapshot carries `meta`.
    /// The library never reads or validates the payload; any byte sequence is
    /// accepted (INV-METADATA-AGNOSTIC).
    ///
    /// # Errors
    ///
    /// As [`Self::seal_snapshot`].
    pub async fn seal_snapshot_with_meta(self, meta: Meta) -> Result<Snapshot, S::Error> {
        self.seal_snapshot_inner(Some(meta)).await
    }

    /// Shared seal body: gather the frozen commitments and build the immutable
    /// `Snapshot`. Consumes `self` so no log survives the seal.
    async fn seal_snapshot_inner(self, meta: Option<Meta>) -> Result<Snapshot, S::Error> {
        let size = self.count();
        let k = self.config().log_arity as u64;

        // The active member roots, the committed epoch timeline, and each active
        // algorithm's binding root at the sealed size. At size 0 there is no
        // active algorithm and no timeline to freeze.
        let (active_roots, alg_epochs, binding_roots) = if size == 0 {
            (Vec::new(), Vec::new(), Vec::new())
        } else {
            let alg_epochs = self.committed_epochs_at(size);

            // Only algorithms active at the sealed size (their epoch covers the
            // final position) contribute a member root and a binding root.
            let mut active_roots = Vec::new();
            for &(id, _) in &alg_epochs {
                if let Some(true) = crate::proof::committed_active_at(&alg_epochs, id, size - 1) {
                    let root = self.root_for_at(id, size).await?;
                    active_roots.push((id, root));
                }
            }

            // Each active algorithm's binding root — its top-level node under its
            // own hash, derived exactly as the log's live binding root is, so a
            // sealed snapshot's head equals the log's head at the sealed size.
            let mut binding_roots = Vec::with_capacity(active_roots.len());
            for &(id, _) in &active_roots {
                let br = self.combined_root_at(id, size).await?;
                binding_roots.push((id, br));
            }

            (active_roots, alg_epochs, binding_roots)
        };

        // The committed canonicalization run-extents: the contiguous-collapse
        // frontier geometry at the sealed size. A frontier node of height >= 1
        // is a collapse and commits its run-extent; a height-0 node is a
        // promoted singleton leaf and commits nothing, so it is dropped here.
        // Derived from (size, k) alone — never inferred from any digest/shape.
        let run_extents: Vec<RunExtent> = frontier_for_size(size, k)
            .into_iter()
            .filter(|&(_, height)| height >= 1)
            .map(|(left, height)| RunExtent { left, height })
            .collect();

        Ok(Snapshot {
            tree_size: size,
            log_arity: k,
            active_roots,
            alg_epochs,
            binding_roots,
            run_extents,
            meta,
        })
    }
}

#[cfg(test)]
mod tests {
    use pmt::hasher::Hasher;
    use sha2::{Digest, Sha256};

    use super::*;
    use crate::storage::MemoryStorage;
    use crate::tree::TreeConfig;

    /// A real fixed-width (32-byte) hasher — the crate's canonical test hasher.
    /// A constant-length digest is required: the tree's node-integrity check
    /// rejects any stored node whose length differs from `null().len()`.
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

    // ---------------------------------------------------------------------
    // C-SEAL-ONEWAY — the seal consumes the log and exposes only reads.
    // (Self-consuming is enforced by the type system: `log` is moved into the
    //  seal, so a use-after-seal does not compile; the snapshot has no
    //  `into_log`, no field mutator, no path back.)
    // ---------------------------------------------------------------------

    #[test]
    fn seal_snapshot_consumes_the_log() {
        smol::block_on(async {
            let log = log_with(5, 2).await;
            let snap = log.seal_snapshot().await.unwrap();
            assert_eq!(snap.tree_size(), 5);
        });
    }

    // ---------------------------------------------------------------------
    // The snapshot's binding root equals the log's binding root at the same
    // size — the seal freezes the live head, it does not recompute a new one.
    // ---------------------------------------------------------------------

    #[test]
    fn binding_root_matches_the_live_combined_root() {
        smol::block_on(async {
            let log = log_with(7, 2).await;
            let size = log.count();
            let live = log.combined_root_at(0, size).await.unwrap();
            let snap = log.seal_snapshot().await.unwrap();
            assert_eq!(snap.binding_root(0), Some(live.as_slice()));
            assert_eq!(snap.binding_roots().len(), 1);
            assert_eq!(snap.binding_roots()[0].0, 0);
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
            let snap = log.seal_snapshot().await.unwrap();
            // Both active algorithms carry their own binding root, sorted by ID.
            assert_eq!(snap.binding_roots().len(), 2);
            assert_eq!(snap.binding_root(0), Some(br0.as_slice()));
            assert_eq!(snap.binding_root(1), Some(br1.as_slice()));
            // Unknown algorithm: no binding root.
            assert_eq!(snap.binding_root(9), None);
        });
    }

    // ---------------------------------------------------------------------
    // INV-AUTH-BOUNDARY — run-extents are the minimal contiguous-collapse
    // record, derivable from (size, k); promotion commits nothing.
    // ---------------------------------------------------------------------

    #[test]
    fn run_extents_are_the_collapse_frontier_geometry() {
        smol::block_on(async {
            // Size 7, k=2: frontier = [(0,2),(4,1),(6,0)]. The height-0 entry
            // is a promoted singleton leaf and commits nothing; the two higher
            // nodes are collapses and commit their run-extents.
            let log = log_with(7, 2).await;
            let snap = log.seal_snapshot().await.unwrap();
            let extents = snap.run_extents();
            assert_eq!(extents.len(), 2, "the height-0 promotion is omitted");
            assert_eq!((extents[0].left(), extents[0].height()), (0, 2));
            assert_eq!((extents[1].left(), extents[1].height()), (4, 1));
            assert_eq!(extents[0].span(2), 4);
            assert_eq!(extents[1].span(2), 2);
            // The run-extents account for 4 + 2 = 6 leaves; the 7th is the
            // promoted leaf that committed no extent.
            let collapsed: u64 = extents.iter().map(|e| e.span(2)).sum();
            assert_eq!(collapsed, 6);
        });
    }

    #[test]
    fn run_extents_match_frontier_for_size_minus_promotions() {
        smol::block_on(async {
            // Property: for any size, the committed run-extents are exactly the
            // frontier nodes of height >= 1, derivable from (size, k) alone —
            // never from a digest. Checked across a sweep of sizes and arities.
            for k in [2usize, 3, 4] {
                for n in 0..40u64 {
                    let log = log_with(n, k).await;
                    let snap = log.seal_snapshot().await.unwrap();
                    let expected: Vec<(u64, u32)> = frontier_for_size(n, k as u64)
                        .into_iter()
                        .filter(|&(_, h)| h >= 1)
                        .collect();
                    let got: Vec<(u64, u32)> = snap
                        .run_extents()
                        .iter()
                        .map(|e| (e.left(), e.height()))
                        .collect();
                    assert_eq!(got, expected, "size {n}, arity {k}");
                    // Heights are strictly positive — no promotion leaks in.
                    assert!(snap.run_extents().iter().all(|e| e.height() >= 1));
                }
            }
        });
    }

    #[test]
    fn fully_collapsed_size_has_one_run_no_promotion() {
        smol::block_on(async {
            // Size 4, k=2 is a perfect tree: one collapse run (0, height 2),
            // zero promotions.
            let log = log_with(4, 2).await;
            let snap = log.seal_snapshot().await.unwrap();
            assert_eq!(snap.run_extents().len(), 1);
            assert_eq!(
                (snap.run_extents()[0].left(), snap.run_extents()[0].height()),
                (0, 2)
            );
            assert_eq!(snap.run_extents()[0].span(2), 4);
        });
    }

    #[test]
    fn single_leaf_commits_no_run_extent() {
        smol::block_on(async {
            // Size 1: a single promoted leaf. Promotion commits nothing, so the
            // run-extents are empty.
            let log = log_with(1, 2).await;
            let snap = log.seal_snapshot().await.unwrap();
            assert!(snap.run_extents().is_empty());
            assert_eq!(snap.tree_size(), 1);
        });
    }

    // ---------------------------------------------------------------------
    // INV-METADATA-AGNOSTIC — opaque metadata round-trips; default is None.
    // ---------------------------------------------------------------------

    #[test]
    fn no_meta_by_default() {
        smol::block_on(async {
            let log = log_with(3, 2).await;
            let snap = log.seal_snapshot().await.unwrap();
            assert_eq!(snap.meta(), None);
        });
    }

    #[test]
    fn opaque_meta_round_trips() {
        smol::block_on(async {
            let payload: Vec<u8> = (0u8..=255u8).collect();
            let log = log_with(3, 2).await;
            let snap = log
                .seal_snapshot_with_meta(Meta::new(payload.clone()))
                .await
                .unwrap();
            assert_eq!(snap.meta().map(Meta::as_bytes), Some(payload.as_slice()));
        });
    }

    #[test]
    fn empty_meta_round_trips() {
        smol::block_on(async {
            let log = log_with(2, 2).await;
            let snap = log
                .seal_snapshot_with_meta(Meta::new(vec![]))
                .await
                .unwrap();
            assert!(snap.meta().expect("meta present").is_empty());
        });
    }

    // ---------------------------------------------------------------------
    // Sealed-shape carry-through: tree_size, active roots and the timeline
    // are frozen exactly as the log held them.
    // ---------------------------------------------------------------------

    #[test]
    fn sealed_shape_carries_size_roots_and_timeline() {
        smol::block_on(async {
            let log = log_with(6, 2).await;
            let size = log.count();
            let live_root = log.root_for_at(0, size).await.unwrap();
            let live_epochs = log.committed_epochs_at(size);
            let snap = log.seal_snapshot().await.unwrap();
            assert_eq!(snap.tree_size(), 6);
            assert_eq!(snap.log_arity(), 2);
            assert_eq!(snap.active_roots(), &[(0u64, live_root)]);
            assert_eq!(snap.alg_epochs(), live_epochs.as_slice());
        });
    }

    #[test]
    fn empty_log_seals_to_an_empty_snapshot() {
        smol::block_on(async {
            let log = log_with(0, 2).await;
            let snap = log.seal_snapshot().await.unwrap();
            assert_eq!(snap.tree_size(), 0);
            assert!(snap.binding_roots().is_empty());
            assert!(snap.run_extents().is_empty());
            assert!(snap.active_roots().is_empty());
            assert!(snap.alg_epochs().is_empty());
            assert_eq!(snap.meta(), None);
        });
    }
}
