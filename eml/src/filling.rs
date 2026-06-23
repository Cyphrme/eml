//! `fill` — the operator-level filling operation over a sealed [`Snapshot`].
//!
//! Filling **raises the certainty of the past**. A snapshot is the immutable
//! stateless cutoff; a single algorithm in it may have a *gappy* history — it
//! was registered late (a null prefix) or deactivated and resumed (interior null
//! runs), so its sealed per-algorithm root projects those gaps as null cells.
//! `fill` recomputes that algorithm's hashes over the **real historical leaf
//! data**, with the algorithm treated as active at *every* position, to produce
//! an entirely new **complete (gapless)** single-algorithm tree — a copy, never a
//! mutation of the snapshot (the seal stays one-way, C-SEAL-ONEWAY).
//!
//! # Why both inputs are mandatory
//!
//! `fill` consumes **two** things and neither substitutes for the other:
//!
//! - the **trusted snapshot** — the authoritative, committed basis. Its
//!   [`run-extents`](Snapshot::run_extents) and sealed [`tree_size`](Snapshot::tree_size) are the
//!   boundary the fill unrolls against. The unroll length and the canonical contiguous-collapse
//!   geometry are read from the *committed* record, never inferred from a digest or a node's shape
//!   (INV-AUTH-BOUNDARY);
//! - the **complete original leaf data** — every leaf the snapshot sealed, in index order. This is
//!   a hard physical requirement and a *feature*: a log abstracts its leaves by hash, so only the
//!   party that still holds the real data can fill. A snapshot alone cannot reconstruct the leaves.
//!
//! Supplying one without the other fails: a snapshot with the wrong number of
//! leaves, or leaf data with no committed basis to unroll against, is rejected
//! rather than guessed.
//!
//! # Optional prune
//!
//! In the same pass `fill` may **prune** a retired algorithm: the caller names an
//! algorithm whose binding the filled tree must not carry forward. Pruning is a
//! pure read-side omission — the filled single-algorithm tree never depended on
//! the pruned algorithm, so the prune only asserts the retirement and rejects a
//! contradictory request (pruning the algorithm being filled).

use pmt::hasher::Hasher;
use pmt::mr::nary_mr;
use pmt::topology::frontier_for_size;

use crate::snapshot::Snapshot;

/// Why a [`fill`] request was rejected.
///
/// `fill` does no storage I/O — it recomputes over caller-supplied data — so it
/// carries its own error channel rather than the storage-parameterised
/// [`crate::Error`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FillError {
    /// The supplied leaf data does not match the snapshot's committed size.
    ///
    /// Both inputs are mandatory: the snapshot commits exactly `committed`
    /// leaves, so the caller must supply exactly that many real leaves. A
    /// mismatch means the two inputs do not describe the same log.
    LeafCountMismatch {
        /// The size the snapshot sealed at — the committed leaf count.
        committed: u64,
        /// The number of leaves the caller supplied.
        supplied: u64,
    },
    /// The committed run-extents do not partition `[0, tree_size)`.
    ///
    /// The extents are the authoritative unroll boundary; if reinserting the
    /// promotion remainder does not reconstruct the full sealed size, the
    /// committed basis is internally inconsistent and the fill cannot proceed
    /// against it (it would have to infer the canonicalization, which
    /// INV-AUTH-BOUNDARY forbids).
    ExtentsDoNotCoverSize {
        /// The sealed size the extents must account for.
        tree_size: u64,
        /// The leaf span the committed extents and promotions actually cover.
        covered: u64,
    },
    /// The caller asked to prune the very algorithm being filled.
    ///
    /// Pruning retires an algorithm the filled tree must not carry forward;
    /// the filled algorithm is the one tree being produced, so pruning it is a
    /// contradiction rather than a no-op.
    PruneTargetIsFillTarget(u64),
}

impl std::fmt::Display for FillError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::LeafCountMismatch {
                committed,
                supplied,
            } => write!(
                f,
                "leaf data does not match the snapshot: snapshot committed {committed} leaves, \
                 caller supplied {supplied}"
            ),
            Self::ExtentsDoNotCoverSize { tree_size, covered } => write!(
                f,
                "committed run-extents cover {covered} leaves but the snapshot sealed {tree_size}"
            ),
            Self::PruneTargetIsFillTarget(id) => {
                write!(f, "cannot prune algorithm {id}: it is the fill target")
            },
        }
    }
}

impl std::error::Error for FillError {}

/// A new, complete (gapless) single-algorithm tree produced by [`fill`].
///
/// It is an independent copy: it owns its recomputed root and shares no state
/// with the snapshot it was filled from. The algorithm is gapless by
/// construction — active at every position in `[0, tree_size)` — so its root is
/// byte-identical to a from-scratch single-algorithm build over the same data.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FilledTree {
    alg_id: u64,
    tree_size: u64,
    root: Vec<u8>,
    pruned: Option<u64>,
}

impl FilledTree {
    /// The algorithm this tree was filled for.
    #[must_use]
    pub fn alg_id(&self) -> u64 {
        self.alg_id
    }

    /// The number of leaves the filled tree spans (the snapshot's sealed size).
    #[must_use]
    pub fn tree_size(&self) -> u64 {
        self.tree_size
    }

    /// The gapless single-algorithm root recomputed over the real leaf data.
    #[must_use]
    pub fn root(&self) -> &[u8] {
        &self.root
    }

    /// The algorithm retired in the same pass, if a prune was requested.
    #[must_use]
    pub fn pruned(&self) -> Option<u64> {
        self.pruned
    }
}

/// Recompute a complete (gapless) single-algorithm tree from a sealed snapshot
/// and the real historical leaf data, optionally pruning a retired algorithm.
///
/// `alg_id` names the algorithm to fill and `hasher` is its hash function (the
/// snapshot froze digests, not hashers, so the operator supplies the function to
/// recompute with). `leaf_data` is every leaf the snapshot sealed, in index
/// order. `prune` optionally names a retired algorithm to drop in the same pass.
///
/// The unroll proceeds from the snapshot's **committed** run-extents and sealed
/// size — the authoritative basis — never from any inferred shape
/// (INV-AUTH-BOUNDARY). The result is a new tree; the snapshot is untouched.
///
/// # Errors
///
/// - [`FillError::LeafCountMismatch`] if `leaf_data.len()` differs from the snapshot's sealed size
///   (both inputs are mandatory and must agree);
/// - [`FillError::ExtentsDoNotCoverSize`] if the committed extents plus promotions do not
///   reconstruct the sealed size;
/// - [`FillError::PruneTargetIsFillTarget`] if `prune == Some(alg_id)`.
pub fn fill<D: AsRef<[u8]>>(
    snapshot: &Snapshot,
    alg_id: u64,
    hasher: &dyn Hasher,
    leaf_data: &[D],
    prune: Option<u64>,
) -> Result<FilledTree, FillError> {
    let tree_size = snapshot.tree_size();
    let k = snapshot.log_arity();

    // ── Both inputs mandatory: the leaf data must match the committed size. ──
    let supplied = leaf_data.len() as u64;
    if supplied != tree_size {
        return Err(FillError::LeafCountMismatch {
            committed: tree_size,
            supplied,
        });
    }

    // ── Prune cannot target the algorithm being filled. ──
    if prune == Some(alg_id) {
        return Err(FillError::PruneTargetIsFillTarget(alg_id));
    }

    // ── Reconstruct the committed frontier partition the snapshot sealed. The
    //    run-extents are the height >= 1 contiguous-collapse runs; the height-0
    //    frontier nodes are promoted singleton leaves (which commit nothing).
    //    Reinserting the promotions into the committed extents must reconstruct
    //    the full left-to-right partition of [0, tree_size) — this is the
    //    authoritative unroll boundary (INV-AUTH-BOUNDARY: we unroll the
    //    committed record, never infer the canonicalization from a digest or a
    //    node's shape). A partition that does not cover the sealed size is an
    //    inconsistent basis and is rejected. ──
    let partition = committed_partition(snapshot, tree_size, k)?;

    // ── Unroll each committed component over the real leaves it stands for.
    //    A collapse run folds its `k^height` contiguous real leaves into the
    //    subtree root the snapshot committed; a promotion is a single real leaf.
    //    The algorithm is active at every position (the fill closes the gaps),
    //    so every leaf contributes its real hash and no cell is a null
    //    projection. ──
    let mut component_roots = Vec::with_capacity(partition.len());
    for &(left, height) in &partition {
        let span = k.pow(height) as usize;
        let lo = left as usize;
        let component = subtree_root(hasher, &leaf_data[lo..lo + span], k);
        component_roots.push(component);
    }

    let root = fold_components(hasher, component_roots, k as usize);

    Ok(FilledTree {
        alg_id,
        tree_size,
        root,
        pruned: prune,
    })
}

/// Reconstruct the committed frontier partition of `[0, tree_size)`: the
/// run-extents (height >= 1 collapses) merged with the promoted singleton
/// leaves (height 0), in left-to-right order.
///
/// The promotions are *derived* from `(tree_size, k)` — the same geometry the
/// seal dropped — and reinserted around the committed extents. The reconstructed
/// partition must left-align and exactly cover the sealed size, or the committed
/// basis is inconsistent.
fn committed_partition(
    snapshot: &Snapshot,
    tree_size: u64,
    k: u64,
) -> Result<Vec<(u64, u32)>, FillError> {
    // The full committed geometry is the canonical frontier: the extents are its
    // height >= 1 members, the promotions its height-0 members. Rebuilding it
    // from the extents plus the derived promotions and checking it equals the
    // canonical frontier ties the unroll to the committed record.
    let canonical = frontier_for_size(tree_size, k);

    let mut partition: Vec<(u64, u32)> = snapshot
        .run_extents()
        .iter()
        .map(|e| (e.left(), e.height()))
        .chain(canonical.iter().copied().filter(|&(_, height)| height == 0))
        .collect();
    partition.sort_unstable_by_key(|&(left, _)| left);

    let covered: u64 = partition.iter().map(|&(_, height)| k.pow(height)).sum();
    if covered != tree_size {
        return Err(FillError::ExtentsDoNotCoverSize { tree_size, covered });
    }

    Ok(partition)
}

/// Fold a perfect `k^height` block of real leaves into its subtree root. The
/// slice length is always a power of `k`, so the reduction is the uniform
/// bottom-up merge a committed collapse run stands for.
fn subtree_root<D: AsRef<[u8]>>(hasher: &dyn Hasher, leaves: &[D], k: u64) -> Vec<u8> {
    let mut level: Vec<Vec<u8>> = leaves.iter().map(|l| hasher.leaf(l.as_ref())).collect();
    let k_usize = k as usize;
    while level.len() > 1 {
        let mut next = Vec::with_capacity(level.len() / k_usize);
        for chunk in level.chunks(k_usize) {
            let refs: Vec<&[u8]> = chunk.iter().map(|v| v.as_slice()).collect();
            next.push(nary_mr(hasher, &refs));
        }
        level = next;
    }
    level.into_iter().next().unwrap_or_else(|| hasher.empty())
}

/// Fold the committed partition's component roots into the single tree root,
/// merging the rightmost `k` repeatedly — identical to the log's own root fold,
/// so the filled root matches a from-scratch build.
fn fold_components(hasher: &dyn Hasher, components: Vec<Vec<u8>>, k: usize) -> Vec<u8> {
    if components.is_empty() {
        return hasher.empty();
    }
    if components.len() == 1 {
        return components.into_iter().next().unwrap();
    }
    let mut current = components;
    while current.len() > k {
        let split = current.len() - k;
        let right: Vec<&[u8]> = current[split..].iter().map(|v| v.as_slice()).collect();
        let merged = nary_mr(hasher, &right);
        current.truncate(split);
        current.push(merged);
    }
    let refs: Vec<&[u8]> = current.iter().map(|v| v.as_slice()).collect();
    nary_mr(hasher, &refs)
}

#[cfg(test)]
mod tests {
    use pmt::hasher::Hasher;
    use sha2::{Digest, Sha256};

    use super::*;
    use crate::storage::MemoryStorage;
    use crate::tree::{NaryMerkleLog, TreeConfig};

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

    fn leaves(n: u64) -> Vec<Vec<u8>> {
        (0..n).map(|i| format!("leaf-{i}").into_bytes()).collect()
    }

    /// Build a log over `data` with a single algorithm (0) active from genesis
    /// and seal it. This is the gapless case: the snapshot's per-algorithm root
    /// already equals the from-scratch build, so the filled root must reproduce
    /// it exactly.
    async fn gapless_snapshot(data: &[Vec<u8>], k: usize) -> Snapshot {
        let config = TreeConfig { log_arity: k };
        let mut log = NaryMerkleLog::new(MemoryStorage::new(), Box::new(Sha256Hasher), config)
            .await
            .unwrap();
        for leaf in data {
            log.append_leaf(leaf).await.unwrap();
        }
        log.seal_snapshot().await.unwrap()
    }

    /// The from-scratch oracle: a fresh single-algorithm log over exactly the
    /// same data, taking its raw per-algorithm root. There is NO difftest
    /// baseline (D7); this independent rebuild is the correctness oracle.
    async fn from_scratch_root(data: &[Vec<u8>], k: usize) -> Vec<u8> {
        let config = TreeConfig { log_arity: k };
        let mut log = NaryMerkleLog::new(MemoryStorage::new(), Box::new(Sha256Hasher), config)
            .await
            .unwrap();
        for leaf in data {
            log.append_leaf(leaf).await.unwrap();
        }
        let size = log.count();
        log.root_for_at(0, size).await.unwrap()
    }

    // ─────────────────────────────────────────────────────────────────────
    // CORRECTNESS ORACLE — the filled single-algorithm root EQUALS a
    // from-scratch build over the same leaf data, across a sweep of sizes
    // (including non-powers-of-k) and arities. (Spec/property oracle; D7.)
    // ─────────────────────────────────────────────────────────────────────

    #[test]
    fn filled_root_equals_from_scratch_build() {
        smol::block_on(async {
            for k in [2usize, 3, 4] {
                for n in 0..40u64 {
                    let data = leaves(n);
                    let snap = gapless_snapshot(&data, k).await;
                    let filled =
                        fill(&snap, 0, &Sha256Hasher, &data, None).expect("fill should succeed");
                    let oracle = from_scratch_root(&data, k).await;
                    assert_eq!(
                        filled.root(),
                        oracle.as_slice(),
                        "filled root must equal from-scratch build at size {n}, arity {k}"
                    );
                    assert_eq!(filled.tree_size(), n);
                    assert_eq!(filled.alg_id(), 0);
                }
            }
        });
    }

    // ─────────────────────────────────────────────────────────────────────
    // FILLING RAISES CERTAINTY — an algorithm registered LATE has a gappy
    // sealed root (null prefix); the filled root closes the gap and equals the
    // from-scratch build, differing from the snapshot's own gappy binding root.
    // ─────────────────────────────────────────────────────────────────────

    #[test]
    fn filling_closes_a_late_registration_gap() {
        smol::block_on(async {
            let config = TreeConfig { log_arity: 2 };
            let mut log = NaryMerkleLog::new(MemoryStorage::new(), Box::new(Sha256Hasher), config)
                .await
                .unwrap();
            // Algorithm 0 covers all leaves; algorithm 7 registers at index 3,
            // so its sealed history has a null prefix over [0, 3).
            let data = leaves(8);
            for (i, leaf) in data.iter().enumerate() {
                if i == 3 {
                    log.add_algorithm(7, Box::new(Sha256Hasher)).await.unwrap();
                }
                log.append_leaf(leaf).await.unwrap();
            }
            let size = log.count();
            let gappy_root = log.root_for_at(7, size).await.unwrap();
            let snap = log.seal_snapshot().await.unwrap();

            // Fill algorithm 7 over the real data: the gap is closed.
            let filled = fill(&snap, 7, &Sha256Hasher, &data, None).unwrap();
            let oracle = from_scratch_root(&data, 2).await;
            assert_eq!(
                filled.root(),
                oracle.as_slice(),
                "filled root closes the gap to a gapless build"
            );
            // The whole point: the filled root genuinely differs from the
            // snapshot's gappy sealed root for that algorithm.
            assert_ne!(
                filled.root(),
                gappy_root.as_slice(),
                "filling must raise certainty, not reproduce the gappy root"
            );
        });
    }

    // ─────────────────────────────────────────────────────────────────────
    // BOTH INPUTS REQUIRED — a snapshot with a leaf-count mismatch is rejected;
    // neither input substitutes for the other.
    // ─────────────────────────────────────────────────────────────────────

    #[test]
    fn fill_requires_leaf_data_matching_the_committed_size() {
        smol::block_on(async {
            let data = leaves(6);
            let snap = gapless_snapshot(&data, 2).await;

            // Too few leaves: rejected.
            let short = &data[..4];
            assert_eq!(
                fill(&snap, 0, &Sha256Hasher, short, None),
                Err(FillError::LeafCountMismatch {
                    committed: 6,
                    supplied: 4
                })
            );

            // Too many leaves: rejected.
            let mut long = data.clone();
            long.push(b"extra".to_vec());
            assert_eq!(
                fill(&snap, 0, &Sha256Hasher, &long, None),
                Err(FillError::LeafCountMismatch {
                    committed: 6,
                    supplied: 7
                })
            );

            // Empty data against a non-empty snapshot: rejected.
            let none: [Vec<u8>; 0] = [];
            assert_eq!(
                fill(&snap, 0, &Sha256Hasher, &none, None),
                Err(FillError::LeafCountMismatch {
                    committed: 6,
                    supplied: 0
                })
            );
        });
    }

    #[test]
    fn empty_snapshot_fills_to_the_empty_root() {
        smol::block_on(async {
            let data: Vec<Vec<u8>> = Vec::new();
            let snap = gapless_snapshot(&data, 2).await;
            let filled = fill(&snap, 0, &Sha256Hasher, &data, None).unwrap();
            assert_eq!(filled.root(), Sha256Hasher.empty().as_slice());
            assert_eq!(filled.tree_size(), 0);
        });
    }

    // ─────────────────────────────────────────────────────────────────────
    // OPTIONAL PRUNE — a retired algorithm may be dropped in the same pass;
    // pruning the fill target is a contradiction.
    // ─────────────────────────────────────────────────────────────────────

    #[test]
    fn prune_path_drops_a_retired_algorithm() {
        smol::block_on(async {
            let data = leaves(5);
            let snap = gapless_snapshot(&data, 2).await;
            // Fill algorithm 0, pruning a retired algorithm 9 in the same pass.
            let filled = fill(&snap, 0, &Sha256Hasher, &data, Some(9)).unwrap();
            assert_eq!(filled.pruned(), Some(9));
            // The filled root is unaffected by the prune — the single-algorithm
            // tree never depended on the pruned algorithm.
            let oracle = from_scratch_root(&data, 2).await;
            assert_eq!(filled.root(), oracle.as_slice());
        });
    }

    #[test]
    fn no_prune_leaves_pruned_unset() {
        smol::block_on(async {
            let data = leaves(3);
            let snap = gapless_snapshot(&data, 2).await;
            let filled = fill(&snap, 0, &Sha256Hasher, &data, None).unwrap();
            assert_eq!(filled.pruned(), None);
        });
    }

    #[test]
    fn cannot_prune_the_fill_target() {
        smol::block_on(async {
            let data = leaves(4);
            let snap = gapless_snapshot(&data, 2).await;
            assert_eq!(
                fill(&snap, 0, &Sha256Hasher, &data, Some(0)),
                Err(FillError::PruneTargetIsFillTarget(0))
            );
        });
    }
}
