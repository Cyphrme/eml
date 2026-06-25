//! The Canonical Mutable Tree state machine.

use std::collections::BTreeMap;

use spine::{ARITY_RANGE, Hasher, ProofStep, Seal, nary_mr};

use crate::error::{Error, Result};
use crate::shape::{self, ShapeNode, covers, leftmost, rightmost};

/// Configuration for a [`Cmt`].
///
/// The mutable tree's only structural axis is the proof-spine arity `k`
/// (`2..=256`), shared with the spine topology. (Prefix domain-separation is
/// not a spine axis — an application that wants it wraps the [`Hasher`].)
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

/// The mutable materialization state for one registered algorithm: the current
/// root and the materialized node cache. Split from the immutable hasher identity
/// so [`Cmt::set`] can borrow the state mutably and the hasher immutably at the
/// same time, without the remove-and-reinsert dance a single `Alg` struct forced.
struct AlgState {
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

impl std::fmt::Debug for AlgState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("AlgState")
            .field("root", &self.root)
            .field("materialized_nodes", &self.cache.len())
            .finish()
    }
}

/// The Canonical Mutable Tree over the Merkle Spine.
///
/// Positional and dense: cells are addressed by flat index `0..len`. The tree
/// shares the spine's proof-spine index space, so an inclusion proof generated
/// here verifies with [`spine::verify_inclusion`] against the trusted
/// `(index, tree_size, arity, root)` topology. Unlike the append-only CML it has
/// no frontier and no consistency proofs — interior cells mutate, which the
/// frontier's left-subtrees-sealed assumption cannot model.
///
/// Single-algorithm structurally, but the materialization holds one
/// `{hasher, root, cache}` view per registered algorithm, so a node may be
/// addressed under many algorithms (per-node multi-hash) and an algorithm may be
/// added after the fact with the root recomputed in `O(log n)` along the changed
/// node's ancestors only ([`Cmt::set`], retroactive add). The cross-tree binding
/// of those per-algorithm roots is the `polydigest` combinator's concern, not the
/// CMT's — the CMT exposes each algorithm's raw member [`root`](Cmt::root) and
/// the structural [`seal`](Cmt::seal), never a binding/combined root.
#[derive(Debug)]
pub struct Cmt {
    config: Config,
    cells: Vec<Cell>,
    /// Immutable hasher identity, keyed by stable algorithm ID.
    hashers: BTreeMap<u64, Box<dyn Hasher>>,
    /// Mutable materialization state, keyed by stable algorithm ID.
    states: BTreeMap<u64, AlgState>,
}

impl Cmt {
    /// Create an empty tree.
    ///
    /// Fails with [`Error::InvalidArity`] if `config.arity` is outside the
    /// spine's `2..=256` range.
    pub fn new(config: Config) -> Result<Self> {
        if !ARITY_RANGE.contains(&config.arity) {
            return Err(Error::InvalidArity(config.arity));
        }
        Ok(Self {
            config,
            cells: Vec::new(),
            hashers: BTreeMap::new(),
            states: BTreeMap::new(),
        })
    }

    /// Register an algorithm under `alg_id`, hashing every existing cell under
    /// it. This is the *bulk* registration cost (`O(n)` over `n` existing
    /// cells), distinct from the per-node retroactive add below.
    ///
    /// Fails with [`Error::DuplicateAlgorithm`] if `alg_id` is already
    /// registered.
    pub fn register_algorithm(&mut self, alg_id: u64, hasher: Box<dyn Hasher>) -> Result<()> {
        if self.hashers.contains_key(&alg_id) {
            return Err(Error::DuplicateAlgorithm(alg_id));
        }
        let mut state = AlgState {
            root: None,
            cache: BTreeMap::new(),
        };
        recompute_full(&self.cells, self.config.arity, hasher.as_ref(), &mut state);
        self.hashers.insert(alg_id, hasher);
        self.states.insert(alg_id, state);
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

        // Split borrows: `states` is mutable, `hashers` is immutable; no
        // remove-and-reinsert needed since the two maps are independent.
        for (id, state) in &mut self.states {
            let h = self
                .hashers
                .get(id)
                .expect("states and hashers are in sync")
                .as_ref();
            if appended {
                // The spine shape may change on append, so recompute fully.
                recompute_full(&self.cells, self.config.arity, h, state);
            } else {
                let _ = recompute_path(&self.cells, self.config.arity, h, state, index);
            }
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

    /// The current per-algorithm **member root** under `alg_id` — the raw root
    /// the leaves authenticate against — or `None` if the algorithm is
    /// unregistered or the tree is empty.
    ///
    /// This is the structural per-algorithm root. The cross-tree **binding /
    /// combined root** that folds every algorithm's member root together is the
    /// `polydigest` combinator's derived view, not the CMT's (D9/D12); the CMT exposes
    /// the raw member roots it materializes and leaves the binding to `polydigest`.
    #[must_use]
    pub fn root(&self, alg_id: u64) -> Option<Vec<u8>> {
        self.states.get(&alg_id).and_then(|s| s.root.clone())
    }

    /// The set of registered algorithm IDs paired with their current member
    /// root, sorted by algorithm ID, skipping any with no root (empty tree).
    ///
    /// The `polydigest` combinator reads these raw member roots as the children of
    /// its binding/combined-root fold; the CMT itself never folds them.
    #[must_use]
    pub fn member_roots(&self) -> Vec<(u64, Vec<u8>)> {
        self.states
            .iter()
            .filter_map(|(&id, s)| s.root.clone().map(|r| (id, r)))
            .collect()
    }

    /// The hasher registered under `alg_id`, or `None` if unregistered.
    ///
    /// The `polydigest` combinator needs the algorithm's own hash to fold the binding
    /// root over the member roots; the CMT materializes the per-algorithm roots
    /// but never folds them, so it lends the hasher rather than computing the
    /// binding root itself.
    #[must_use]
    pub fn hasher(&self, alg_id: u64) -> Option<&dyn Hasher> {
        self.hashers.get(&alg_id).map(AsRef::as_ref)
    }

    // --- proofs --------------------------------------------------------------

    /// Generate an inclusion proof for cell `index` under `alg_id`.
    ///
    /// Returns the leaf digest and the proof path. The path verifies with
    /// [`spine::verify_inclusion`] against the trusted `(index, len, arity, root)`
    /// — the CMT shares the spine index space, so it generates paths the spine
    /// checks rather than running a second verifier. Returns `None` if `alg_id`
    /// is unregistered or `index` is out of range.
    #[must_use]
    pub fn inclusion_proof(&self, alg_id: u64, index: u64) -> Option<(Vec<u8>, Vec<ProofStep>)> {
        if index >= self.len() {
            return None;
        }
        let h = self.hashers.get(&alg_id)?.as_ref();
        let state = self.states.get(&alg_id)?;
        let shape = shape::build(self.len(), self.config.arity)?;
        let leaf_hash = leaf_digest_raw(&self.cells, h, index);
        let path = crate::proof::inclusion_path(
            &shape,
            index,
            &state.cache,
            &mut |pos| leaf_digest_raw(&self.cells, h, pos),
            &mut |children| nary_mr(h, children),
        );
        Some((leaf_hash, path))
    }

    /// Produce a self-contained [`spine::LeafProof`] for cell `index` under
    /// `alg_id` — the live "is this a legitimate leaf?" witness, peer of the
    /// inclusion proof. It bundles the leaf digest with its trusted positional
    /// parameters `(index, len, arity)` and the inclusion path, so a consumer
    /// verifies with one [`spine::LeafProof::verify`] call against an
    /// authenticated root. Returns `None` for an unregistered algorithm or an
    /// out-of-range index.
    #[must_use]
    pub fn leaf_proof(&self, alg_id: u64, index: u64) -> Option<spine::LeafProof> {
        let (leaf_hash, path) = self.inclusion_proof(alg_id, index)?;
        Some(spine::LeafProof::new(
            leaf_hash,
            index,
            self.len(),
            self.config.arity,
            path,
        ))
    }

    /// Generate a non-membership proof for `index` under `alg_id`: an inclusion
    /// proof for the spine null constant (SAD §5, inclusion-of-null via
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
        let h = self.hashers.get(&alg_id)?.as_ref();
        let (leaf_hash, path) = self.inclusion_proof(alg_id, index)?;
        if leaf_hash == h.null() {
            Some((leaf_hash, path))
        } else {
            None
        }
    }

    /// Add `alg_id` to a single cell `index` after the fact, recomputing the
    /// root in `O(log n)` along that cell's ancestors only (D11, the
    /// "Post-Facto Digest" / retroactive algorithm addition).
    ///
    /// This is the mutable tree's *incremental* multi-hash operation: distinct
    /// from bulk filling (a `polydigest` operator, `O(n)`, which re-derives a whole
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
        if self.hashers.contains_key(&alg_id) {
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
        let mut state = AlgState {
            root: None,
            cache: BTreeMap::new(),
        };
        let recomputed = add_alg_seeded(
            &self.cells,
            self.config.arity,
            hasher.as_ref(),
            &mut state,
            index,
        );
        self.hashers.insert(alg_id, hasher);
        self.states.insert(alg_id, state);
        Ok(recomputed)
    }

    /// Consume the tree and seal it into the general structural [`spine::Seal`]
    /// (D13, the structural facet of the seal chain).
    ///
    /// One-way: there is no `unseal` and no path back to a `Cmt`
    /// (C-SEAL-ONEWAY). The seal **computes the resumable frontier** — every
    /// registered algorithm's frontier peaks (the digests of the perfect k-ary
    /// subtrees the spine topology names at this size). The `Seal` carries **no
    /// committed epoch timeline and no binding root** — those are the *epoch
    /// facet*, added by the `polydigest` combinator as a wrapper over this general
    /// `Seal` (`polydigest(cmt)`), never baked in here.
    ///
    /// A live `Cmt` has no frontier stack — that absence is the mutable/append
    /// tell. Computing the peaks at seal erases the distinction, so every `Seal`
    /// uniformly carries a resumable frontier regardless of source kind, and the
    /// member root every consumer sees is the fold of those peaks (identical to
    /// the tree's own root, since both fold the same perfect-subtree digests).
    ///
    /// # No `from_seal` — why a `Seal` cannot revive a `Cmt`
    ///
    /// There is deliberately **no `Cmt::from_seal`**. A frontier is the
    /// *complete* continuation state of an append-only log (every future append
    /// folds against the peaks alone), but only *partial* state for a mutable
    /// tree: mutating an interior cell needs every cell's digest along its
    /// ancestor path, and the seal dropped all of those, keeping only the peaks.
    /// Reviving arbitrary mutation over the committed positions would also
    /// *un-seal the committed past* — the one-way guarantee the seal exists to
    /// make. The way to a readable, mutable-or-append tree over the committed
    /// data is the `polydigest` combinator's `fill` (data-required), which rebuilds
    /// and verifies against the committed binding root; the discarded frontier is
    /// simply unused when the fill target is a mutable tree.
    ///
    /// Fails with [`Error::EmptySeal`] on an empty tree (nothing to seal) and
    /// propagates [`Error::MalformedSeal`] if the spine rejects the frontier.
    pub fn seal(self) -> Result<Seal> {
        if self.cells.is_empty() {
            return Err(Error::EmptySeal);
        }
        let size = self.cells.len() as u64;
        let k = self.config.arity;
        let coords = spine::frontier_for_size(size, k);
        let mut frontiers: Vec<(u64, Vec<Vec<u8>>)> = Vec::with_capacity(self.states.len());
        // Iterate states mutably for peak_digest's defensive cache-healing fallback.
        let mut states = self.states;
        for (id, state) in &mut states {
            if state.root.is_none() {
                continue;
            }
            let h = self
                .hashers
                .get(id)
                .expect("states and hashers are in sync")
                .as_ref();
            let peaks: Vec<Vec<u8>> = coords
                .iter()
                .map(|&(left, height)| peak_digest(&self.cells, h, state, left, height, k))
                .collect();
            frontiers.push((*id, peaks));
        }
        Seal::new(size, k, frontiers).map_err(|_| Error::MalformedSeal)
    }

    /// Like [`Self::inclusion_proof`] but also returns the number of off-path
    /// cache misses during proof generation. A fully materialized tree has zero
    /// misses; any positive count is a regression signal (F4 perf invariant).
    #[cfg(test)]
    pub(crate) fn inclusion_proof_miss_count(
        &self,
        alg_id: u64,
        index: u64,
    ) -> Option<(Vec<u8>, Vec<ProofStep>, usize)> {
        if index >= self.len() {
            return None;
        }
        let h = self.hashers.get(&alg_id)?.as_ref();
        let state = self.states.get(&alg_id)?;
        let shape = shape::build(self.len(), self.config.arity)?;
        let leaf_hash = leaf_digest_raw(&self.cells, h, index);
        let (path, misses) = crate::proof::inclusion_path_with_miss_count(
            &shape,
            index,
            &state.cache,
            &mut |pos| leaf_digest_raw(&self.cells, h, pos),
            &mut |children| nary_mr(h, children),
        );
        Some((leaf_hash, path, misses))
    }
}

// --- free helper functions --------------------------------------------------

/// Rebuild one algorithm's materialized spine from scratch (`O(n)`). Used on
/// registration and on append, where the spine shape may change.
fn recompute_full(cells: &[Cell], arity: u64, hasher: &dyn Hasher, state: &mut AlgState) {
    state.cache.clear();
    state.root = shape::build(cells.len() as u64, arity).map(|shape| {
        eval_subtree(&mut state.cache, hasher, &shape, &mut |pos| {
            leaf_digest_raw(cells, hasher, pos)
        })
    });
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
fn recompute_path(
    cells: &[Cell],
    arity: u64,
    hasher: &dyn Hasher,
    state: &mut AlgState,
    index: u64,
) -> usize {
    let Some(shape) = shape::build(cells.len() as u64, arity) else {
        state.root = None;
        return 0;
    };
    let mut recomputed = 0usize;
    state.root = Some(eval_on_path(
        cells,
        hasher,
        state,
        &shape,
        index,
        &mut recomputed,
    ));
    recomputed
}

/// Recompute the digests on the path to `index`, reading every off-path node
/// from the cache. Only nodes on the path (the changed leaf and its
/// ancestors) are recomputed and re-cached; counts the inner nodes
/// recomputed via `recomputed`.
fn eval_on_path(
    cells: &[Cell],
    hasher: &dyn Hasher,
    state: &mut AlgState,
    node: &ShapeNode,
    index: u64,
    recomputed: &mut usize,
) -> Vec<u8> {
    match node {
        ShapeNode::Leaf(_) => {
            let digest = leaf_digest_raw(cells, hasher, shape::leftmost(node));
            state.cache.insert(node_key(node), digest.clone());
            digest
        },
        ShapeNode::Inner(children) => {
            let mut refs_owned: Vec<Vec<u8>> = Vec::with_capacity(children.len());
            for child in children {
                if covers(child, index) {
                    refs_owned.push(eval_on_path(cells, hasher, state, child, index, recomputed));
                } else {
                    // Off the path: read the materialized digest, never
                    // re-hashing the subtree. The callers always leave a
                    // complete materialization, so a miss is a logic error;
                    // fall back to a full eval defensively rather than
                    // silently producing a wrong root.
                    let cached = state
                        .cache
                        .get(&node_key(child))
                        .cloned()
                        .unwrap_or_else(|| {
                            eval_subtree(&mut state.cache, hasher, child, &mut |pos| {
                                leaf_digest_raw(cells, hasher, pos)
                            })
                        });
                    refs_owned.push(cached);
                }
            }
            let refs: Vec<&[u8]> = refs_owned.iter().map(Vec::as_slice).collect();
            let digest = nary_mr(hasher, &refs);
            state.cache.insert(node_key(node), digest.clone());
            *recomputed += 1;
            digest
        },
    }
}

/// Materialize every spine node as the null digest (the state before any
/// cell has been hashed under a freshly added algorithm). `O(n)` to seed
/// once; the subsequent per-node add is `O(log n)`.
fn seed_null(cells: &[Cell], arity: u64, hasher: &dyn Hasher, state: &mut AlgState) {
    state.cache.clear();
    let null = hasher.null();
    state.root = shape::build(cells.len() as u64, arity).map(|shape| {
        // Cache the leaf as null so the subsequent path-recompute reads
        // every off-path sibling from the cache (never the real
        // payload): only the target cell gains a real digest.
        eval_subtree(&mut state.cache, hasher, &shape, &mut |_| null.clone())
    });
}

/// Seed a fresh algorithm with all-null digests and then recompute the
/// single path to `index`. The ordering is structural: seed MUST precede
/// path-recompute (a swapped call order produces a correct root at O(n)
/// cost instead of O(log n), caught only by a perf property test).
fn add_alg_seeded(
    cells: &[Cell],
    arity: u64,
    hasher: &dyn Hasher,
    state: &mut AlgState,
    index: u64,
) -> usize {
    seed_null(cells, arity, hasher, state);
    recompute_path(cells, arity, hasher, state, index)
}

/// The materialized digest of the perfect k-ary subtree at frontier
/// coordinate `(left, height)` — the closed leaf interval
/// `[left, left + k^height - 1]`. Read from the algorithm's cache; a miss
/// is a logic error (the tree is always fully materialized before seal), but
/// the defensive fallback re-evaluates and caches the subtree rather than
/// silently producing a wrong digest.
fn peak_digest(
    cells: &[Cell],
    hasher: &dyn Hasher,
    state: &mut AlgState,
    left: u64,
    height: u32,
    k: u64,
) -> Vec<u8> {
    let right = left + k.pow(height) - 1;
    if let Some(d) = state.cache.get(&(left, right)) {
        return d.clone();
    }
    let shape = shape::perfect(left, height, k);
    eval_subtree(&mut state.cache, hasher, &shape, &mut |pos| {
        leaf_digest_raw(cells, hasher, pos)
    })
}

/// Evaluate a subtree's digest, materializing every node — leaves and inner
/// nodes alike — into `cache`. Parameterized over leaf behavior via `leaf_fn`:
///
/// - Real digests: `|pos| leaf_digest_raw(cells, hasher, pos)`
/// - Null seeding: `|_| null_digest.clone()`
///
/// Caching leaves lets a later path-recompute ([`recompute_path`]) read every
/// off-path sibling from the cache without ever re-hashing the subtree.
fn eval_subtree(
    cache: &mut BTreeMap<(u64, u64), Vec<u8>>,
    hasher: &dyn Hasher,
    node: &ShapeNode,
    leaf_fn: &mut dyn FnMut(u64) -> Vec<u8>,
) -> Vec<u8> {
    let key = node_key(node);
    match node {
        ShapeNode::Leaf(pos) => {
            let digest = leaf_fn(*pos);
            cache.insert(key, digest.clone());
            digest
        },
        ShapeNode::Inner(children) => {
            let child_digests: Vec<Vec<u8>> = children
                .iter()
                .map(|c| eval_subtree(cache, hasher, c, leaf_fn))
                .collect();
            let refs: Vec<&[u8]> = child_digests.iter().map(Vec::as_slice).collect();
            let digest = nary_mr(hasher, &refs);
            cache.insert(key, digest.clone());
            digest
        },
    }
}

/// The leaf digest of cell `pos` in `cells` under `hasher`. An absent cell
/// (position beyond the end) hashes the null constant.
fn leaf_digest_raw(cells: &[Cell], hasher: &dyn Hasher, pos: u64) -> Vec<u8> {
    match cells.get(pos as usize) {
        Some(cell) => hasher.leaf(&cell.payload),
        None => hasher.null(),
    }
}

/// A stable cache key for a spine node: the closed interval of leaf positions it
/// covers, `(leftmost, rightmost)`. `(size, arity)` fixes the shape, so a node
/// is uniquely identified by the leaves beneath it — distinguishing nested
/// left-aligned nodes (e.g. the root and its leftmost descendants), which a
/// `(leftmost, child_count)` key would alias.
fn node_key(node: &ShapeNode) -> (u64, u64) {
    (leftmost(node), rightmost(node))
}
