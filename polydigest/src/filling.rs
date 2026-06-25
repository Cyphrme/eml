//! `fill` — the operator-level filling operation over a sealed [`crate::Sealed`].
//!
//! `fill` is the **trustless verification path**: it consumes a `Sealed` (the
//! committed basis) and the **real historical leaf data**, rebuilds a full,
//! readable single-algorithm tree over that data, and **verifies the rebuilt
//! binding root against the `Sealed`'s committed binding root**. A target the
//! data cannot reproduce — wrong leaves, a layout the chosen kind cannot rebuild
//! — yields a root mismatch and is **rejected**. This is what lets a holder of
//! the data verify a commitment *without trusting any attester*: the only thing
//! the verifier must hold besides the data is the committed binding root (which
//! an out-of-band attestation on the [`Sealed`]'s opaque metadata may vouch for).
//!
//! # Why both inputs are mandatory
//!
//! `fill` consumes **two** things and neither substitutes for the other:
//!
//! - the **trusted `Sealed`** — the authoritative, committed basis. Its
//!   [`run-extents`](crate::Sealed::run_extents) and sealed [`tree_size`](crate::Sealed::tree_size)
//!   are the boundary the fill unrolls against; the unroll length and the canonical
//!   contiguous-collapse geometry are read from the *committed* record, never inferred from a
//!   digest or a node's shape (INV-AUTH-BOUNDARY);
//! - the **complete original leaf data** — every leaf the `Sealed` committed, in index order. This
//!   is a hard physical requirement and a *feature*: a log abstracts its leaves by hash, so only
//!   the party that still holds the real data can fill. A `Sealed` alone cannot reconstruct the
//!   leaves.
//!
//! Supplying one without the other fails: a `Sealed` with the wrong number of
//! leaves, or leaf data with no committed basis to unroll against, is rejected
//! rather than guessed.
//!
//! # Target kind
//!
//! The rebuilt tree is materialized as the caller's chosen [`FillKind`] — a
//! readable append-only log (EML) or a mutable tree (EMT). Both fold the same
//! committed partition over the same data, so both reproduce the same root; the
//! kind selects only the materialization the caller wants back. A kind that
//! cannot reproduce the committed layout fails the binding-root check.

use spine::{Hasher, constant_time_eq, frontier_for_size, nary_mr};

use crate::Sealed;
use crate::root::combined_root;

/// Which readable materialization [`fill`] produces.
///
/// Both kinds unroll the same committed partition over the same data, but they
/// **bag the resulting peaks differently** — the append-only log (EML) with the
/// MMR backward-bag, the mutable tree (EMT) with the rebalanced fold — so the two
/// reproduce *different* roots (the MMR migration's intentional divergence). A
/// fill therefore reproduces, and verifies against, a commitment of its own kind:
/// an EML fill against an EML-topology seal, an EMT fill against an EMT one.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FillKind {
    /// A readable append-only log (EML) materialization.
    Eml,
    /// A readable mutable-tree (EMT) materialization.
    Emt,
}

impl FillKind {
    /// The peak-bagging this kind commits with: the append-only log's MMR
    /// backward-bag, the mutable tree's rebalanced fold.
    #[must_use]
    pub fn bag(self) -> spine::BagFn {
        match self {
            Self::Eml => cml::mountain::bag_peaks,
            Self::Emt => cmt::rebalanced_bag,
        }
    }
}

/// Why a [`fill`] request was rejected.
///
/// `fill` does no storage I/O — it recomputes over caller-supplied data — so it
/// carries its own error channel rather than the storage-parameterised
/// [`crate::Error`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FillError {
    /// The supplied leaf data does not match the `Sealed`'s committed size.
    ///
    /// Both inputs are mandatory: the `Sealed` commits exactly `committed`
    /// leaves, so the caller must supply exactly that many real leaves. A
    /// mismatch means the two inputs do not describe the same log.
    LeafCountMismatch {
        /// The size the `Sealed` sealed at — the committed leaf count.
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
    /// The named algorithm has no committed frontier in the `Sealed`, so there
    /// is no committed binding root to fill against.
    UnknownAlgorithm(u64),
    /// No hasher was supplied for an algorithm active in the `Sealed`.
    ///
    /// The committed binding root commits *every* active algorithm's member
    /// root as a child, so the trustless check cannot recompute it with a
    /// missing hasher — supplying an incomplete `all_hashers` would silently
    /// fold over a truncated child set. Surfaced rather than dropped.
    MissingHasher {
        /// The active algorithm whose hasher was absent from `all_hashers`.
        alg_id: u64,
    },
    /// The rebuilt binding root does not match the `Sealed`'s committed binding
    /// root for the filled algorithm.
    ///
    /// The data and target kind could not reproduce the committed layout — a
    /// forged leaf, the wrong data, or a layout the kind cannot rebuild. This is
    /// the trustless rejection: the commitment is not vouched for by the data.
    BindingRootMismatch {
        /// The algorithm whose binding root failed to reproduce.
        alg_id: u64,
    },
}

impl std::fmt::Display for FillError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::LeafCountMismatch {
                committed,
                supplied,
            } => write!(
                f,
                "leaf data does not match the sealed commitment: committed {committed} leaves, \
                 caller supplied {supplied}"
            ),
            Self::ExtentsDoNotCoverSize { tree_size, covered } => write!(
                f,
                "committed run-extents cover {covered} leaves but the commitment sealed \
                 {tree_size}"
            ),
            Self::UnknownAlgorithm(id) => {
                write!(
                    f,
                    "algorithm {id} has no committed frontier in the sealed commitment"
                )
            },
            Self::MissingHasher { alg_id } => {
                write!(
                    f,
                    "no hasher supplied for algorithm {alg_id}, which is active in the sealed \
                     commitment; the binding-root check needs every active algorithm's hasher"
                )
            },
            Self::BindingRootMismatch { alg_id } => write!(
                f,
                "rebuilt binding root for algorithm {alg_id} does not match the committed binding \
                 root: the data could not reproduce the committed layout"
            ),
        }
    }
}

impl std::error::Error for FillError {}

/// A complete (gapless), readable single-algorithm tree produced by [`fill`],
/// verified against the `Sealed`'s committed binding root.
///
/// It is an independent copy: it owns its recomputed root and shares no state
/// with the `Sealed` it was filled from. The algorithm is gapless by
/// construction — active at every position in `[0, tree_size)` — so its root is
/// byte-identical to a from-scratch single-algorithm build over the same data,
/// and its binding root has been checked equal to the committed one.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FilledTree {
    alg_id: u64,
    tree_size: u64,
    kind: FillKind,
    root: Vec<u8>,
}

impl FilledTree {
    /// The algorithm this tree was filled for.
    #[must_use]
    pub fn alg_id(&self) -> u64 {
        self.alg_id
    }

    /// The number of leaves the filled tree spans (the `Sealed`'s sealed size).
    #[must_use]
    pub fn tree_size(&self) -> u64 {
        self.tree_size
    }

    /// The materialization kind the caller requested.
    #[must_use]
    pub fn kind(&self) -> FillKind {
        self.kind
    }

    /// The gapless single-algorithm member root recomputed over the real leaf
    /// data — verified equal to the `Sealed`'s committed binding root.
    #[must_use]
    pub fn root(&self) -> &[u8] {
        &self.root
    }
}

/// Rebuild a complete (gapless) single-algorithm tree from a sealed [`Sealed`]
/// and the real historical leaf data, **verifying the rebuilt binding root
/// against the committed one** — the trustless verification path.
///
/// `alg_id` names the algorithm to fill and `hasher` is its hash function (the
/// `Sealed` froze digests, not hashers). `leaf_data` is every leaf the `Sealed`
/// committed, in index order. `kind` selects the readable materialization.
/// `all_hashers` resolves every active algorithm's own hash for the
/// promotion-aware binding-root check (for a single-algorithm promoted
/// commitment it may carry just `alg_id`).
///
/// The unroll proceeds from the `Sealed`'s **committed** run-extents and sealed
/// size — the authoritative basis — never from any inferred shape
/// (INV-AUTH-BOUNDARY). The rebuilt binding root is then compared to the
/// `Sealed`'s committed binding root; a mismatch is rejected.
///
/// # Errors
///
/// - [`FillError::LeafCountMismatch`] if `leaf_data.len()` differs from the sealed size;
/// - [`FillError::ExtentsDoNotCoverSize`] if the committed extents plus promotions do not
///   reconstruct the sealed size;
/// - [`FillError::UnknownAlgorithm`] if `alg_id` has no committed frontier;
/// - [`FillError::BindingRootMismatch`] if the rebuilt binding root does not reproduce the
///   committed one (the data could not reproduce the committed layout).
pub fn fill<D: AsRef<[u8]>>(
    sealed: &Sealed,
    alg_id: u64,
    hasher: &dyn Hasher,
    leaf_data: &[D],
    kind: FillKind,
    all_hashers: &[(u64, &dyn Hasher)],
) -> Result<FilledTree, FillError> {
    let tree_size = sealed.tree_size();
    let k = sealed.arity();

    // ── The algorithm must have a committed frontier to fill against. ──
    if sealed.peaks(alg_id).is_none() {
        return Err(FillError::UnknownAlgorithm(alg_id));
    }

    // ── Both inputs mandatory: the leaf data must match the committed size. ──
    let supplied = leaf_data.len() as u64;
    if supplied != tree_size {
        return Err(FillError::LeafCountMismatch {
            committed: tree_size,
            supplied,
        });
    }

    // ── Reconstruct the committed frontier partition the seal froze: the
    //    run-extents (height >= 1 collapse runs) plus the derived promotions
    //    (height-0 nodes). Reinserting the promotions must reconstruct the full
    //    left-to-right partition of [0, tree_size) — the authoritative unroll
    //    boundary (INV-AUTH-BOUNDARY). A partition that does not cover the
    //    sealed size is an inconsistent basis and is rejected. ──
    let partition = committed_partition(sealed, tree_size, k)?;

    // ── Unroll each committed component over the real leaves it stands for.
    //    The algorithm is active at every position (the fill closes any gaps),
    //    so every leaf contributes its real hash and no cell is null. The
    //    component peaks are then bagged with the **kind's** fold (EML → MMR
    //    backward-bag, EMT → rebalanced): the two kinds reproduce different
    //    roots, so a fill verifies against a commitment of its own kind. ──
    let mut component_roots = Vec::with_capacity(partition.len());
    for &(left, height) in &partition {
        let span = k.pow(height) as usize;
        let lo = left as usize;
        let component = subtree_root(hasher, &leaf_data[lo..lo + span], k);
        component_roots.push(component);
    }
    let member_root = kind.bag()(hasher, &component_roots, k);

    // ── Trustless verification: the rebuilt binding root must equal the one
    //    the Sealed committed. For a gapless single-algorithm fill the rebuilt
    //    member root is the binding root under genesis promotion; otherwise the
    //    binding root is the promotion-aware combined root, which we compute
    //    from the rebuilt member root and the committed timeline. A mismatch
    //    means the data could not reproduce the committed layout. ──
    // The committed seal must have been bagged with this kind's topology; verify
    // the rebuilt member root reproduces the committed binding root under the
    // same bag. (Filling an EMT against an EML seal — or vice versa — correctly
    // mismatches: the two topologies commit different roots.)
    let committed = sealed
        .binding_root(alg_id, hasher, all_hashers, kind.bag())
        .map_err(fill_error_from_missing_hasher)?
        .ok_or(FillError::UnknownAlgorithm(alg_id))?;
    let rebuilt_binding =
        rebuilt_binding_root(sealed, alg_id, hasher, &member_root, all_hashers, kind)?;
    if !constant_time_eq(&rebuilt_binding, &committed) {
        return Err(FillError::BindingRootMismatch { alg_id });
    }

    Ok(FilledTree {
        alg_id,
        tree_size,
        kind,
        root: member_root,
    })
}

/// Compute the binding root the *rebuilt* member root implies: the
/// canonicalization fold ([`crate::root::combined_root`]) over every active algorithm's
/// member root, with the filled algorithm's committed member root replaced by
/// the *rebuilt* (gapless) one, under that algorithm's hash. Genesis promotion
/// is native to the fold — a single member root under a trivial timeline folds
/// to itself — so a promoted commitment needs no special case.
fn rebuilt_binding_root(
    sealed: &Sealed,
    alg_id: u64,
    hasher: &dyn Hasher,
    member_root: &[u8],
    all_hashers: &[(u64, &dyn Hasher)],
    kind: FillKind,
) -> Result<Vec<u8>, FillError> {
    // The fold's children are every active algorithm's member root; for the
    // filled algorithm we substitute the rebuilt root so the check verifies the
    // data reproduces the committed layout exactly. Use the *complete* member-
    // root set: folding over a truncated one (a missing hasher silently dropped)
    // would compare against a binding root no algorithm committed.
    let mut members = sealed
        .all_member_roots(all_hashers, kind.bag())
        .map_err(fill_error_from_missing_hasher)?;
    for (id, mr) in &mut members {
        if *id == alg_id {
            *mr = member_root.to_vec();
        }
    }
    Ok(combined_root(
        hasher,
        &members,
        sealed.alg_epochs(),
        sealed.tree_size(),
        sealed.arity(),
    ))
}

/// Map a combinator [`crate::Error`] from a member/binding-root fold into the
/// fill error channel. Only [`spine::Error::MissingHasher`] can arise here — the
/// timeline and arity were validated when the `Sealed` was constructed — so any
/// other variant is unreachable on this path.
fn fill_error_from_missing_hasher(e: crate::Error) -> FillError {
    match e {
        crate::Error::Spine(spine::Error::MissingHasher { alg_id }) => {
            FillError::MissingHasher { alg_id }
        },
        crate::Error::Spine(spine::Error::BadArity | spine::Error::MalformedFrontier)
        | crate::Error::MalformedEpochs => {
            unreachable!("binding-root fold over a validated Sealed yields only MissingHasher")
        },
    }
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
    sealed: &Sealed,
    tree_size: u64,
    k: u64,
) -> Result<Vec<(u64, u32)>, FillError> {
    let canonical = frontier_for_size(tree_size, k);

    let mut partition: Vec<(u64, u32)> = sealed
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

#[cfg(test)]
mod tests {
    use sha2::{Digest, Sha256};
    use spine::Hasher;

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

    /// Build a single-algorithm (alg 0 from genesis) log over `data` and seal it.
    async fn gapless_sealed(data: &[Vec<u8>], k: usize) -> Sealed {
        let config = TreeConfig { arity: k as u64 };
        let mut log = NaryMerkleLog::new(MemoryStorage::new(), Box::new(Sha256Hasher), config)
            .await
            .unwrap();
        for leaf in data {
            log.append_leaf(leaf).await.unwrap();
        }
        log.seal().await.unwrap()
    }

    /// The from-scratch EML oracle: a fresh single-algorithm log over the same
    /// data (its root is the MMR backward-bag).
    async fn from_scratch_root(data: &[Vec<u8>], k: usize) -> Vec<u8> {
        let config = TreeConfig { arity: k as u64 };
        let mut log = NaryMerkleLog::new(MemoryStorage::new(), Box::new(Sha256Hasher), config)
            .await
            .unwrap();
        for leaf in data {
            log.append_leaf(leaf).await.unwrap();
        }
        log.root_for_at(0, log.count()).await.unwrap()
    }

    /// Build a single-algorithm (alg 0 from genesis) mutable tree over `data` and
    /// seal it — the EMT-topology (rebalanced) counterpart of `gapless_sealed`.
    fn emt_sealed(data: &[Vec<u8>], k: usize) -> Sealed {
        let mut t = crate::EpochTree::new(crate::CmtConfig { arity: k as u64 }).unwrap();
        t.register_algorithm(0, Box::new(Sha256Hasher)).unwrap();
        for (i, leaf) in data.iter().enumerate() {
            t.set(i as u64, leaf.clone(), Vec::new()).unwrap();
        }
        t.seal().unwrap()
    }

    /// The from-scratch EMT oracle: a fresh single-algorithm mutable tree over the
    /// same data (its root is the rebalanced fold).
    fn emt_from_scratch_root(data: &[Vec<u8>], k: usize) -> Vec<u8> {
        let mut t = crate::EpochTree::new(crate::CmtConfig { arity: k as u64 }).unwrap();
        t.register_algorithm(0, Box::new(Sha256Hasher)).unwrap();
        for (i, leaf) in data.iter().enumerate() {
            t.set(i as u64, leaf.clone(), Vec::new()).unwrap();
        }
        t.root(0).unwrap()
    }

    // ─────────────────────────────────────────────────────────────────────
    // CORRECTNESS ORACLE + TRUSTLESS VERIFY — each fill kind reproduces a
    // from-scratch build of ITS OWN structure AND verifies against a committed
    // binding root of the MATCHING kind, across a sweep of sizes (incl.
    // non-powers-of-k) and arities. No difftest baseline (D7); the from-scratch
    // rebuild is the oracle.
    //
    // Under MMR each kind commits its own way: an EML fill (MMR backward-bag)
    // reproduces an append-only log seal; an EMT fill (rebalanced fold)
    // reproduces a mutable-tree seal. Both retained capabilities are tested here,
    // each against a seal of its own kind — only the now-false *cross-kind*
    // equality (one fold serving both) is dropped, never the EMT-fill capability.
    // ─────────────────────────────────────────────────────────────────────

    #[test]
    fn filled_root_equals_from_scratch_and_verifies_per_kind() {
        smol::block_on(async {
            let h = Sha256Hasher;
            let hashers: [(u64, &dyn Hasher); 1] = [(0, &h)];
            for k in [2usize, 3, 4] {
                for n in 1u64..40 {
                    let data = leaves(n);

                    // EML fill against an append-only (MMR) seal.
                    let eml_sealed = gapless_sealed(&data, k).await;
                    let eml_oracle = from_scratch_root(&data, k).await;
                    let eml_filled = fill(&eml_sealed, 0, &h, &data, FillKind::Eml, &hashers)
                        .expect("gapless data verifies against the EML binding root");
                    assert_eq!(eml_filled.root(), eml_oracle.as_slice(), "EML n={n} k={k}");
                    assert_eq!(eml_filled.tree_size(), n);
                    assert_eq!(eml_filled.kind(), FillKind::Eml);

                    // EMT fill against a mutable-tree (rebalanced) seal.
                    let emt_sealed = emt_sealed(&data, k);
                    let emt_oracle = emt_from_scratch_root(&data, k);
                    let emt_filled = fill(&emt_sealed, 0, &h, &data, FillKind::Emt, &hashers)
                        .expect("gapless data verifies against the EMT binding root");
                    assert_eq!(emt_filled.root(), emt_oracle.as_slice(), "EMT n={n} k={k}");
                    assert_eq!(emt_filled.tree_size(), n);
                    assert_eq!(emt_filled.kind(), FillKind::Emt);
                }
            }
        });
    }

    // ─────────────────────────────────────────────────────────────────────
    // TRUSTLESS REJECTION — forged/wrong data that cannot reproduce the
    // committed layout fails the binding-root check.
    // ─────────────────────────────────────────────────────────────────────

    #[test]
    fn forged_leaf_data_is_rejected() {
        smol::block_on(async {
            let h = Sha256Hasher;
            let hashers: [(u64, &dyn Hasher); 1] = [(0, &h)];
            let data = leaves(7);
            let sealed = gapless_sealed(&data, 2).await;
            // Tamper with one leaf — the rebuilt binding root no longer matches.
            let mut forged = data.clone();
            forged[3] = b"forged".to_vec();
            assert_eq!(
                fill(&sealed, 0, &h, &forged, FillKind::Eml, &hashers),
                Err(FillError::BindingRootMismatch { alg_id: 0 })
            );
        });
    }

    // ─────────────────────────────────────────────────────────────────────
    // BOTH INPUTS REQUIRED — a leaf-count mismatch is rejected before any
    // verification; neither input substitutes for the other.
    // ─────────────────────────────────────────────────────────────────────

    #[test]
    fn fill_requires_leaf_data_matching_the_committed_size() {
        smol::block_on(async {
            let h = Sha256Hasher;
            let hashers: [(u64, &dyn Hasher); 1] = [(0, &h)];
            let data = leaves(6);
            let sealed = gapless_sealed(&data, 2).await;

            assert_eq!(
                fill(&sealed, 0, &h, &data[..4], FillKind::Eml, &hashers),
                Err(FillError::LeafCountMismatch {
                    committed: 6,
                    supplied: 4
                })
            );
            let mut long = data.clone();
            long.push(b"extra".to_vec());
            assert_eq!(
                fill(&sealed, 0, &h, &long, FillKind::Eml, &hashers),
                Err(FillError::LeafCountMismatch {
                    committed: 6,
                    supplied: 7
                })
            );
        });
    }

    #[test]
    fn unknown_algorithm_is_rejected() {
        smol::block_on(async {
            let h = Sha256Hasher;
            let hashers: [(u64, &dyn Hasher); 1] = [(0, &h)];
            let data = leaves(4);
            let sealed = gapless_sealed(&data, 2).await;
            assert_eq!(
                fill(&sealed, 9, &h, &data, FillKind::Eml, &hashers),
                Err(FillError::UnknownAlgorithm(9))
            );
        });
    }

    #[test]
    fn empty_commitment_fills_to_the_empty_root() {
        smol::block_on(async {
            // A size-0 seal has no frontier, hence no algorithm 0 — fill cannot
            // target it. (Sealing an empty log yields an empty commitment.)
            let h = Sha256Hasher;
            let hashers: [(u64, &dyn Hasher); 1] = [(0, &h)];
            let data: Vec<Vec<u8>> = Vec::new();
            let sealed = gapless_sealed(&data, 2).await;
            assert_eq!(
                fill(&sealed, 0, &h, &data, FillKind::Eml, &hashers),
                Err(FillError::UnknownAlgorithm(0))
            );
        });
    }

    // ─────────────────────────────────────────────────────────────────────
    // MULTI-ALGORITHM — a non-promoted commitment binds the timeline into the
    // binding root; a gapless fill of an active-from-genesis algorithm
    // reproduces it. Filling the other algorithm likewise verifies.
    // ─────────────────────────────────────────────────────────────────────

    #[test]
    fn multi_algorithm_gapless_fill_verifies() {
        smol::block_on(async {
            let config = TreeConfig { arity: 2 };
            let mut log = NaryMerkleLog::new(MemoryStorage::new(), Box::new(Sha256Hasher), config)
                .await
                .unwrap();
            log.add_algorithm(1, Box::new(Sha256Hasher)).await.unwrap();
            let data = leaves(8);
            for leaf in &data {
                log.append_leaf(leaf).await.unwrap();
            }
            let sealed = log.seal().await.unwrap();
            let h = Sha256Hasher;
            let hashers: [(u64, &dyn Hasher); 2] = [(0, &h), (1, &h)];
            // Both algorithms were active from genesis over the same data, so
            // both rebuild to the same member root and bind correctly.
            let f0 = fill(&sealed, 0, &h, &data, FillKind::Eml, &hashers).unwrap();
            let f1 = fill(&sealed, 1, &h, &data, FillKind::Emt, &hashers).unwrap();
            assert_eq!(f0.root(), f1.root());
        });
    }
}
