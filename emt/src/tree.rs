//! The mutable Epoch Merkle Tree state machine.

use std::collections::BTreeMap;

use pmt::mr::nary_mr;
use pmt::proof::ProofStep;
use pmt::{Hasher, Sealed};

use crate::error::{Error, Result};
use crate::spine::{self, SpineNode};

/// Configuration for an [`Emt`].
///
/// The mutable tree's only structural axis is the proof-spine arity `k`
/// (`2..=256`), shared with the kernel topology. (Prefix domain-separation is
/// not a kernel axis — an application that wants it wraps the [`Hasher`].)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Config {
    /// Proof-spine arity `k` (`2..=256`).
    pub arity: u64,
}

impl Default for Config {
    fn default() -> Self {
        Self { arity: 2 }
    }
}

/// A logical cell of the tree: an opaque payload plus an opaque metadata
/// channel the library carries but never interprets.
///
/// A cell is **positional** — addressed by its flat index, never by a key. The
/// payload is hashed under each registered algorithm to give the cell its
/// per-algorithm leaf digest (per-node multi-hash); the metadata bytes ride
/// alongside untouched (INV-METADATA-AGNOSTIC).
#[derive(Debug, Clone, PartialEq, Eq, Default)]
struct Cell {
    payload: Vec<u8>,
    metadata: Vec<u8>,
}

/// A registered hashing algorithm and its materialized digest spine.
struct Alg {
    hasher: Box<dyn Hasher>,
    /// The materialized root digest at the current size, or `None` for the
    /// empty tree.
    root: Option<Vec<u8>>,
    /// Materialized digest of every spine node — leaves and inner nodes —
    /// keyed by the closed leaf interval `(leftmost, rightmost)` it covers.
    /// `(size, arity)` fixes the shape, so this key is unique within one
    /// materialization. A path-recompute reads every off-path node from here
    /// and rewrites only the path, which is what bounds its work to `O(log n)`.
    cache: BTreeMap<(u64, u64), Vec<u8>>,
}

impl std::fmt::Debug for Alg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Alg")
            .field("hasher", &self.hasher)
            .field("root", &self.root)
            .field("materialized_nodes", &self.cache.len())
            .finish()
    }
}

/// The mutable Epoch Merkle Tree over the PMT kernel.
///
/// Positional and dense: cells are addressed by flat index `0..len`. The tree
/// shares the kernel's proof-spine index space, so an inclusion proof generated
/// here verifies with `pmt::verify_inclusion` against the trusted
/// `(index, tree_size, arity, root)` topology. Unlike the append-only EML it has
/// no frontier and no consistency proofs — interior cells mutate, which the
/// frontier's left-subtrees-sealed assumption cannot model.
///
/// Multiple algorithms may address the same node (per-node multi-hash), and an
/// algorithm may be added after the fact with the root recomputed in `O(log n)`
/// along the changed node's ancestors only ([`Emt::set`], retroactive add).
#[derive(Debug)]
pub struct Emt {
    config: Config,
    cells: Vec<Cell>,
    /// Registered algorithms, keyed by stable algorithm ID.
    algs: BTreeMap<u64, Alg>,
}

impl Emt {
    /// Create an empty tree.
    ///
    /// Fails with [`Error::InvalidArity`] if `config.arity` is outside the
    /// kernel's `2..=256` range.
    pub fn new(config: Config) -> Result<Self> {
        if !(2..=256).contains(&config.arity) {
            return Err(Error::InvalidArity(config.arity));
        }
        Ok(Self {
            config,
            cells: Vec::new(),
            algs: BTreeMap::new(),
        })
    }

    /// Register an algorithm under `alg_id`, hashing every existing cell under
    /// it. This is the *bulk* registration cost (`O(n)` over `n` existing
    /// cells), distinct from the per-node retroactive add below.
    ///
    /// Fails with [`Error::DuplicateAlgorithm`] if `alg_id` is already
    /// registered.
    pub fn register_algorithm(&mut self, alg_id: u64, hasher: Box<dyn Hasher>) -> Result<()> {
        if self.algs.contains_key(&alg_id) {
            return Err(Error::DuplicateAlgorithm(alg_id));
        }
        let mut alg = Alg {
            hasher,
            root: None,
            cache: BTreeMap::new(),
        };
        self.recompute_full(&mut alg);
        self.algs.insert(alg_id, alg);
        Ok(())
    }

    /// Set the payload (and opaque metadata) of cell `index`.
    ///
    /// Indices extend the tree densely: setting `index == len` appends a cell;
    /// setting an existing index overwrites it. A gap (`index > len`) is
    /// rejected with [`Error::IndexGap`] — the tree is positional and dense,
    /// not sparse.
    ///
    /// Overwriting an existing cell recomputes only that cell's ancestor path
    /// in every registered algorithm: `O(log n)` per algorithm. Appending may
    /// change the spine shape and is recomputed against the new shape.
    pub fn set(&mut self, index: u64, payload: Vec<u8>, metadata: Vec<u8>) -> Result<()> {
        let len = self.cells.len() as u64;
        if index > len {
            return Err(Error::IndexGap { index, len });
        }
        let cell = Cell { payload, metadata };
        let appended = index == len;
        if appended {
            self.cells.push(cell);
        } else {
            self.cells[index as usize] = cell;
        }

        // Collect ids first to avoid borrowing `self.algs` while mutating cells.
        let ids: Vec<u64> = self.algs.keys().copied().collect();
        for id in ids {
            let mut alg = self.algs.remove(&id).expect("id from keys");
            if appended {
                // The spine shape may change on append, so recompute it fully.
                self.recompute_full(&mut alg);
            } else {
                let _ = self.recompute_path(&mut alg, index);
            }
            self.algs.insert(id, alg);
        }
        Ok(())
    }

    /// Read the payload of cell `index`, or `None` if out of range.
    #[must_use]
    pub fn get(&self, index: u64) -> Option<&[u8]> {
        self.cells.get(index as usize).map(|c| c.payload.as_slice())
    }

    /// Read the opaque metadata of cell `index`, or `None` if out of range.
    ///
    /// The bytes are returned verbatim; the library never parses them
    /// (INV-METADATA-AGNOSTIC).
    #[must_use]
    pub fn metadata(&self, index: u64) -> Option<&[u8]> {
        self.cells
            .get(index as usize)
            .map(|c| c.metadata.as_slice())
    }

    /// Number of cells in the tree.
    #[must_use]
    pub fn len(&self) -> u64 {
        self.cells.len() as u64
    }

    /// Whether the tree holds no cells.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.cells.is_empty()
    }

    /// The configured proof-spine arity.
    #[must_use]
    pub fn arity(&self) -> u64 {
        self.config.arity
    }

    /// The current root digest under `alg_id`, or `None` if the algorithm is
    /// unregistered or the tree is empty.
    #[must_use]
    pub fn root(&self, alg_id: u64) -> Option<Vec<u8>> {
        self.algs.get(&alg_id).and_then(|a| a.root.clone())
    }

    // --- materialization -----------------------------------------------------

    /// Rebuild one algorithm's materialized spine from scratch (`O(n)`). Used on
    /// registration and on append, where the spine shape may change.
    fn recompute_full(&self, alg: &mut Alg) {
        alg.cache.clear();
        alg.root =
            spine::build(self.len(), self.config.arity).map(|shape| self.eval_node(alg, &shape));
    }

    /// Recompute only the ancestor path of cell `index` (`O(log n)`), returning
    /// the number of inner-node digests recomputed.
    ///
    /// Walks from the root to the leaf following child spans, recomputing each
    /// inner digest on the way back up. Inner nodes off the path are read from
    /// the materialized cache untouched — that is what bounds the work to the
    /// path length. The returned count is the locality witness inspected by the
    /// `O(log n)` property test: it is the ancestor depth, not the total node
    /// count.
    fn recompute_path(&self, alg: &mut Alg, index: u64) -> usize {
        let Some(shape) = spine::build(self.len(), self.config.arity) else {
            alg.root = None;
            return 0;
        };
        let mut recomputed = 0usize;
        alg.root = Some(self.eval_on_path(alg, &shape, index, &mut recomputed));
        recomputed
    }

    /// Evaluate `node`'s digest, materializing every node — leaves and inner
    /// nodes alike — into the cache. Caching leaves is what lets a later
    /// path-recompute read every off-path sibling from the cache without ever
    /// re-hashing it, and lets the null seeding ([`Emt::seed_null`]) record a
    /// distinct (all-null) materialization for a freshly added algorithm.
    fn eval_node(&self, alg: &mut Alg, node: &SpineNode) -> Vec<u8> {
        match node {
            SpineNode::Leaf(pos) => {
                let digest = self.leaf_digest(alg, *pos);
                alg.cache.insert(node_key(node), digest.clone());
                digest
            },
            SpineNode::Inner(children) => {
                let child_digests: Vec<Vec<u8>> =
                    children.iter().map(|c| self.eval_node(alg, c)).collect();
                let refs: Vec<&[u8]> = child_digests.iter().map(Vec::as_slice).collect();
                let digest = nary_mr(alg.hasher.as_ref(), &refs);
                alg.cache.insert(node_key(node), digest.clone());
                digest
            },
        }
    }

    /// Recompute the digests on the path to `index`, reading every off-path node
    /// from the cache. Only nodes on the path (the changed leaf and its
    /// ancestors) are recomputed and re-cached; counts the inner nodes
    /// recomputed via `recomputed`.
    fn eval_on_path(
        &self,
        alg: &mut Alg,
        node: &SpineNode,
        index: u64,
        recomputed: &mut usize,
    ) -> Vec<u8> {
        match node {
            SpineNode::Leaf(pos) => {
                let digest = self.leaf_digest(alg, *pos);
                alg.cache.insert(node_key(node), digest.clone());
                digest
            },
            SpineNode::Inner(children) => {
                let mut refs_owned: Vec<Vec<u8>> = Vec::with_capacity(children.len());
                for child in children {
                    if covers(child, index) {
                        refs_owned.push(self.eval_on_path(alg, child, index, recomputed));
                    } else {
                        // Off the path: read the materialized digest, never
                        // re-hashing the subtree. The callers always leave a
                        // complete materialization, so a miss is a logic error;
                        // fall back to a full eval defensively rather than
                        // silently producing a wrong root.
                        let cached = alg
                            .cache
                            .get(&node_key(child))
                            .cloned()
                            .unwrap_or_else(|| self.eval_node(alg, child));
                        refs_owned.push(cached);
                    }
                }
                let refs: Vec<&[u8]> = refs_owned.iter().map(Vec::as_slice).collect();
                let digest = nary_mr(alg.hasher.as_ref(), &refs);
                alg.cache.insert(node_key(node), digest.clone());
                *recomputed += 1;
                digest
            },
        }
    }

    /// The leaf digest of cell `pos` under this algorithm. An absent cell (off
    /// the end) hashes the null constant, matching a vacant kernel position.
    fn leaf_digest(&self, alg: &Alg, pos: u64) -> Vec<u8> {
        match self.cells.get(pos as usize) {
            Some(cell) => alg.hasher.leaf(&cell.payload),
            None => alg.hasher.null(),
        }
    }

    // --- proofs --------------------------------------------------------------

    /// Generate an inclusion proof for cell `index` under `alg_id`.
    ///
    /// Returns the leaf digest and the proof path. The path verifies with
    /// [`pmt::verify_inclusion`] against the trusted `(index, len, arity, root)`
    /// — the EMT shares the kernel index space, so it generates paths the kernel
    /// checks rather than running a second verifier. Returns `None` if `alg_id`
    /// is unregistered or `index` is out of range.
    #[must_use]
    pub fn inclusion_proof(&self, alg_id: u64, index: u64) -> Option<(Vec<u8>, Vec<ProofStep>)> {
        if index >= self.len() {
            return None;
        }
        let alg = self.algs.get(&alg_id)?;
        let shape = spine::build(self.len(), self.config.arity)?;
        let leaf_hash = self.leaf_digest(alg, index);
        let path = crate::proof::inclusion_path(
            &shape,
            index,
            &mut |pos| self.leaf_digest(alg, pos),
            &mut |children| nary_mr(alg.hasher.as_ref(), children),
        );
        Some((leaf_hash, path))
    }

    /// Produce a self-contained [`pmt::LeafProof`] for cell `index` under
    /// `alg_id` — the live "is this a legitimate leaf?" witness, peer of the
    /// inclusion proof. It bundles the leaf digest with its trusted positional
    /// parameters `(index, len, arity)` and the inclusion path, so a consumer
    /// verifies with one [`pmt::LeafProof::verify`] call against an
    /// authenticated root. Returns `None` for an unregistered algorithm or an
    /// out-of-range index.
    #[must_use]
    pub fn leaf_proof(&self, alg_id: u64, index: u64) -> Option<pmt::LeafProof> {
        let (leaf_hash, path) = self.inclusion_proof(alg_id, index)?;
        Some(pmt::LeafProof::new(
            leaf_hash,
            index,
            self.len(),
            self.config.arity,
            path,
        ))
    }

    /// Generate a non-membership proof for `index` under `alg_id`: an inclusion
    /// proof for the kernel null constant (SAD §5, inclusion-of-null via
    /// collapse).
    ///
    /// Succeeds only when cell `index` actually hashes to `null()` — i.e. the
    /// position carries no real value — returning the null leaf digest and the
    /// proof path. A cell with a real payload is *present*, so non-membership
    /// returns `None`. Returns `None` for an unregistered algorithm or an
    /// out-of-range index.
    #[must_use]
    pub fn non_membership_proof(
        &self,
        alg_id: u64,
        index: u64,
    ) -> Option<(Vec<u8>, Vec<ProofStep>)> {
        let alg = self.algs.get(&alg_id)?;
        let (leaf_hash, path) = self.inclusion_proof(alg_id, index)?;
        if leaf_hash == alg.hasher.null() {
            Some((leaf_hash, path))
        } else {
            None
        }
    }

    /// Add `alg_id` to a single cell `index` after the fact, recomputing the
    /// root in `O(log n)` along that cell's ancestors only (D11, the
    /// "Post-Facto Digest" / retroactive algorithm addition).
    ///
    /// This is the EMT's *incremental* multi-hash operation: distinct from
    /// bulk filling (an EML operator, `O(n)`, which re-derives a whole
    /// algorithm's history). Here a node gains a digest under a *newly seeded*
    /// algorithm and only its ancestor path is touched; positions other than
    /// `index` contribute their already-materialized digests (the null
    /// constant for positions never hashed under this algorithm).
    ///
    /// Returns the number of inner-node digests the per-node add recomputed —
    /// the cell's ancestor depth, the `O(log n)` cost witness (the initial null
    /// seeding is the one-time `O(n)` materialization, not the per-node cost).
    ///
    /// Fails with [`Error::DuplicateAlgorithm`] if `alg_id` is already
    /// registered and with [`Error::IndexGap`] if `index` is out of range.
    pub fn add_algorithm_at(
        &mut self,
        alg_id: u64,
        index: u64,
        hasher: Box<dyn Hasher>,
    ) -> Result<usize> {
        if self.algs.contains_key(&alg_id) {
            return Err(Error::DuplicateAlgorithm(alg_id));
        }
        if index >= self.len() {
            return Err(Error::IndexGap {
                index,
                len: self.len(),
            });
        }
        // Seed the algorithm with every position null, then path-recompute the
        // single cell that gains a digest — touching only its ancestors.
        let mut alg = Alg {
            hasher,
            root: None,
            cache: BTreeMap::new(),
        };
        self.seed_null(&mut alg);
        let recomputed = self.recompute_path(&mut alg, index);
        self.algs.insert(alg_id, alg);
        Ok(recomputed)
    }

    /// Materialize every spine node as the null digest (the state before any
    /// cell has been hashed under a freshly added algorithm). `O(n)` to seed
    /// once; the subsequent per-node add is `O(log n)`.
    fn seed_null(&self, alg: &mut Alg) {
        alg.cache.clear();
        let null = alg.hasher.null();
        alg.root = spine::build(self.len(), self.config.arity)
            .map(|shape| self.seed_node(alg, &shape, &null));
    }

    fn seed_node(&self, alg: &mut Alg, node: &SpineNode, null: &[u8]) -> Vec<u8> {
        match node {
            SpineNode::Leaf(_) => {
                // Cache the leaf as null so the subsequent path-recompute reads
                // every off-path sibling from the cache (never the real
                // payload): only the target cell gains a real digest.
                alg.cache.insert(node_key(node), null.to_vec());
                null.to_vec()
            },
            SpineNode::Inner(children) => {
                let child_digests: Vec<Vec<u8>> = children
                    .iter()
                    .map(|c| self.seed_node(alg, c, null))
                    .collect();
                let refs: Vec<&[u8]> = child_digests.iter().map(Vec::as_slice).collect();
                let digest = nary_mr(alg.hasher.as_ref(), &refs);
                alg.cache.insert(node_key(node), digest.clone());
                digest
            },
        }
    }

    /// Consume the tree and seal it into the one kernel currency [`Sealed`].
    ///
    /// One-way: there is no `unseal` and no path back to an `Emt`
    /// (C-SEAL-ONEWAY). The seal **computes the resumable frontier** — every
    /// registered algorithm's frontier peaks (the digests of the perfect k-ary
    /// subtrees the kernel topology names at this size) — under the default open
    /// epoch timeline `(0, MAX)`, the only timeline a mutable tree (which has no
    /// epoch lifecycle of its own) can assert.
    ///
    /// A live `Emt` has no frontier stack — that absence is the EMT/EML tell.
    /// Computing the peaks at seal erases the distinction, so *every* `Sealed`
    /// uniformly carries a resumable frontier regardless of source kind, and the
    /// member root every consumer sees is the fold of those peaks (identical to
    /// the EMT's own root, since both fold the same perfect-subtree digests).
    ///
    /// # No `from_sealed` — why a `Sealed` cannot revive an `Emt`
    ///
    /// There is deliberately **no `Emt::from_sealed`**. A frontier is the
    /// *complete* continuation state of an append-only log (every future append
    /// folds against the peaks alone), but only *partial* state for a mutable
    /// tree: mutating an interior cell needs every cell's digest along its
    /// ancestor path, and the seal dropped all of those, keeping only the peaks.
    /// Reviving arbitrary mutation over the committed positions would also
    /// *un-seal the committed past* — the one-way guarantee the seal exists to
    /// make. The way to a readable, mutable-or-append tree over the committed
    /// data is [`fill`](../../eml_log/fn.fill.html) (data-required), which
    /// rebuilds and verifies against the committed binding root; the discarded
    /// frontier is simply unused when the fill target is an EMT.
    ///
    /// Fails with [`Error::EmptySeal`] on an empty tree (nothing to seal) and
    /// propagates [`Error::MalformedSeal`] if the kernel rejects the timeline.
    pub fn seal(self) -> Result<Sealed> {
        if self.cells.is_empty() {
            return Err(Error::EmptySeal);
        }
        let size = self.cells.len() as u64;
        let k = self.config.arity;
        let coords = pmt::topology::frontier_for_size(size, k);
        let mut frontiers: Vec<(u64, Vec<Vec<u8>>)> = Vec::with_capacity(self.algs.len());
        let mut alg_epochs: Vec<(u64, Vec<(u64, u64)>)> = Vec::with_capacity(self.algs.len());
        for (&id, alg) in &self.algs {
            if alg.root.is_none() {
                continue;
            }
            // The frontier peaks are the materialized digests of the perfect
            // k-ary subtrees at the frontier coordinates. Each is the cache
            // entry keyed by the closed leaf interval the subtree covers.
            let peaks: Vec<Vec<u8>> = coords
                .iter()
                .map(|&(left, height)| self.peak_digest(alg, left, height, k))
                .collect();
            frontiers.push((id, peaks));
            alg_epochs.push((id, vec![(0, u64::MAX)]));
        }
        Sealed::new(size, k, frontiers, alg_epochs).map_err(|_| Error::MalformedSeal)
    }

    /// The materialized digest of the perfect k-ary subtree at frontier
    /// coordinate `(left, height)` — the closed leaf interval
    /// `[left, left + k^height - 1]`. Read from the algorithm's cache, with a
    /// defensive re-evaluation if the materialization is incomplete (the seal
    /// always runs on a fully materialized tree, so a miss is a logic error
    /// rather than a silent wrong digest).
    fn peak_digest(&self, alg: &Alg, left: u64, height: u32, k: u64) -> Vec<u8> {
        let right = left + k.pow(height) - 1;
        if let Some(d) = alg.cache.get(&(left, right)) {
            return d.clone();
        }
        let shape = spine_perfect(left, height, k);
        self.eval_uncached(alg, &shape)
    }

    /// Evaluate a spine node's digest without touching the cache — the
    /// defensive fallback for [`Self::peak_digest`] on a cache miss.
    fn eval_uncached(&self, alg: &Alg, node: &SpineNode) -> Vec<u8> {
        match node {
            SpineNode::Leaf(pos) => self.leaf_digest(alg, *pos),
            SpineNode::Inner(children) => {
                let child_digests: Vec<Vec<u8>> = children
                    .iter()
                    .map(|c| self.eval_uncached(alg, c))
                    .collect();
                let refs: Vec<&[u8]> = child_digests.iter().map(Vec::as_slice).collect();
                nary_mr(alg.hasher.as_ref(), &refs)
            },
        }
    }
}

/// A perfect k-ary subtree shape of the given `height`, leftmost leaf at flat
/// position `left`. Height 0 is a lone leaf. Mirrors [`crate::spine`]'s internal
/// `perfect`; used only by the defensive seal fallback.
fn spine_perfect(left: u64, height: u32, k: u64) -> SpineNode {
    if height == 0 {
        return SpineNode::Leaf(left);
    }
    let child_span = k.pow(height - 1);
    let children = (0..k)
        .map(|c| spine_perfect(left + c * child_span, height - 1, k))
        .collect();
    SpineNode::Inner(children)
}

/// A stable cache key for a spine node: the closed interval of leaf positions it
/// covers, `(leftmost, rightmost)`. `(size, arity)` fixes the shape, so a node
/// is uniquely identified by the leaves beneath it — distinguishing nested
/// left-aligned nodes (e.g. the root and its leftmost descendants), which a
/// `(leftmost, child_count)` key would alias.
fn node_key(node: &SpineNode) -> (u64, u64) {
    (leftmost(node), rightmost(node))
}

/// The leftmost flat leaf position covered by `node`.
fn leftmost(node: &SpineNode) -> u64 {
    match node {
        SpineNode::Leaf(pos) => *pos,
        SpineNode::Inner(children) => leftmost(&children[0]),
    }
}

/// The rightmost flat leaf position covered by `node`.
fn rightmost(node: &SpineNode) -> u64 {
    match node {
        SpineNode::Leaf(pos) => *pos,
        SpineNode::Inner(children) => rightmost(children.last().expect("inner node has children")),
    }
}

/// Whether `node` covers flat position `index`.
fn covers(node: &SpineNode, index: u64) -> bool {
    leftmost(node) <= index && index <= rightmost(node)
}
