//! The single-algorithm canonical-log engine over the [`spine`].
//!
//! A [`AlgView`] is **one algorithm's** continuation state — its hasher, its
//! committed epoch intervals, and its frontier stack — and the free functions
//! here are the structural operations over it: the base-k frontier carry, the
//! member-root fold, inclusion/consistency proof generation, and the historical
//! root reconstructions. Every operation that touches stored bytes reads them
//! through a borrowed [`NodeReader`]; the engine never owns the store, so the
//! `polydigest` combinator can drive **N** views over **one** shared substrate
//! without duplicating leaf data (D14). The engine names no epoch concept: a
//! view's epoch intervals are read locally only to project a coordinate's
//! null/active value, never to bind a cross-tree timeline.

use spine::{Hasher, fold_frontier, frontier_for_size, nary_mr};

use crate::consistency::ProofStep;
use crate::error::{Error, Result};
use crate::schedule::reduction_count;

/// A borrowed read substrate the single-algorithm engine folds over.
///
/// The engine reads stored node digests and (for flat logs) raw leaf payloads
/// through this trait; it never writes and never owns the store. The `polydigest`
/// combinator implements it over its one shared storage so N algorithm views
/// share a single data substrate (D14). The `alg_id` selects which algorithm's
/// node namespace the read targets — leaf payloads are algorithm-agnostic and
/// stored once.
pub trait NodeReader {
    /// The read backend's error type.
    type Error;

    /// Retrieve a sealed internal node digest at `(alg_id, left, height)`, or
    /// `None` if no node is stored there.
    fn get_node(
        &self,
        alg_id: u64,
        left: u64,
        height: u32,
    ) -> impl std::future::Future<Output = ReadResult<Option<Vec<u8>>, Self>> + Send;

    /// Retrieve the raw leaf payload at `index` (flat logs only).
    fn get_leaf(
        &self,
        index: u64,
    ) -> impl std::future::Future<Output = ReadResult<Vec<u8>, Self>> + Send;
}

/// The `Result` a [`NodeReader`] read yields: a value `T` or the backend's own
/// error. Aliased so the trait's `impl Future` return types stay readable.
pub type ReadResult<T, R> = std::result::Result<T, <R as NodeReader>::Error>;

/// Whether log-level appends are flat leaf appends or subtree appends.
///
/// The single-algorithm engine reads this only to know whether a height-0 cell
/// is a raw leaf payload (flat) or an authoritative stored subtree digest
/// (subtree); the combinator owns the value and its persistence.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LogKind {
    /// Each append is a raw leaf; the payload is stored verbatim for auditability.
    Flat,
    /// Each append is a subtree root; only the evaluated root hash is stored.
    Subtree,
}

impl LogKind {
    /// Serialize to the storage byte representation.
    #[must_use]
    pub fn to_byte(self) -> u8 {
        match self {
            Self::Flat => 0,
            Self::Subtree => 1,
        }
    }

    /// Deserialize from the storage byte representation.
    ///
    /// Returns `None` if the byte is not a recognized `LogKind` variant.
    #[must_use]
    pub fn from_byte(b: u8) -> Option<Self> {
        match b {
            0 => Some(Self::Flat),
            1 => Some(Self::Subtree),
            _ => None,
        }
    }
}

/// One algorithm's single-tree continuation state: its hasher, committed epoch
/// intervals, and frontier stack. This is the **per-algorithm frontier only**
/// (D14) — the shared leaf data lives once in the combinator's store, never
/// here.
#[derive(Debug)]
pub struct AlgView {
    /// Hasher instance.
    pub hasher: Box<dyn Hasher>,
    /// Epoch intervals: half-open `[start, end)`.
    /// `end == u64::MAX` represents an active (open) epoch.
    pub epochs: Vec<(u64, u64)>,
    /// Frontier stack: holds hashes of completed subtrees.
    pub frontier: Vec<Vec<u8>>,
    /// Coordinates of each frontier node: `(left_index, height)`.
    pub frontier_coords: Vec<(u64, u32)>,
}

impl Clone for AlgView {
    fn clone(&self) -> Self {
        Self {
            hasher: self.hasher.clone_box(),
            epochs: self.epochs.clone(),
            frontier: self.frontier.clone(),
            frontier_coords: self.frontier_coords.clone(),
        }
    }
}

impl AlgView {
    /// Whether this algorithm is currently active (not frozen).
    #[must_use]
    pub fn is_active(&self) -> bool {
        self.epochs.last().is_some_and(|&(_, end)| end == u64::MAX)
    }

    /// Whether leaf/subtree index `i` falls within any of this algorithm's active epochs.
    #[must_use]
    pub fn is_active_at(&self, i: u64) -> bool {
        self.epochs
            .iter()
            .any(|&(start, end)| start <= i && i < end)
    }

    /// The tree size for this algorithm.
    ///
    /// Active algorithms track the global tree size.
    /// Frozen algorithms stopped at their last deactivation point.
    #[must_use]
    pub fn tree_size(&self, global_size: u64) -> u64 {
        if self.is_active() {
            global_size
        } else {
            self.epochs.last().map_or(0, |&(_, end)| end)
        }
    }

    /// The activation index of the first epoch.
    #[must_use]
    pub fn first_activation(&self) -> u64 {
        self.epochs.first().map_or(0, |&(start, _)| start)
    }

    /// Whether algorithm has active content in the half-open range `[lo, hi)`.
    ///
    /// Definition 14b (Active range): true iff any epoch overlaps the interval.
    #[must_use]
    pub fn active_range(&self, lo: u64, hi: u64) -> bool {
        self.epochs
            .iter()
            .any(|&(start, end)| start < hi && end > lo)
    }

    /// Whether the range `[lo, hi)` is fully contained within the active epochs.
    #[must_use]
    pub fn fully_active(&self, lo: u64, hi: u64) -> bool {
        self.epochs
            .iter()
            .any(|&(start, end)| start <= lo && hi <= end)
    }

    /// The algorithm-local tree size corresponding to global size `size`.
    ///
    /// Active algorithms (or null-projection spans before first activation)
    /// see the full global size. Frozen algorithms cap at their last
    /// deactivation point; the maximum epoch end that is strictly less than
    /// `size` is the algorithm's effective size.
    #[must_use]
    pub fn effective_size_at(&self, size: u64) -> u64 {
        if size <= self.first_activation() {
            // Pre-activation: null projections span [0, size); the frontier
            // geometry uses the global size.  When size == 0 this is 0.
            size
        } else if self.is_active_at(size - 1) {
            size
        } else {
            self.epochs
                .iter()
                .filter(|&&(_, end)| end < size)
                .map(|&(_, end)| end)
                .max()
                .unwrap_or(0)
        }
    }

    /// The epoch timeline as it stood at size `size`, for commitment into
    /// the combined root and audit checkpoints (Design A+).
    ///
    /// Intervals beginning after `size` are dropped; an interval extending
    /// past `size` is encoded as open (`end == u64::MAX`), matching what the
    /// timeline looked like when the log was that size. An interval closed
    /// exactly at `size` stays closed — this is what distinguishes
    /// "deactivated at the tip" from "still live, log idle" (frontier
    /// freshness). Returns `None` if the algorithm was not yet registered.
    #[must_use]
    pub fn epochs_at(&self, size: u64) -> Option<Vec<(u64, u64)>> {
        let mut out = Vec::new();
        for &(start, end) in &self.epochs {
            if start > size {
                break;
            }
            if end > size {
                out.push((start, u64::MAX));
                break;
            }
            out.push((start, end));
        }
        if out.is_empty() { None } else { Some(out) }
    }
}

/// Compute the member root from an algorithm's in-memory frontier — the fold of
/// its frontier peaks under its own hash.
#[must_use]
pub fn compute_root(view: &AlgView, k: usize) -> Vec<u8> {
    if view.frontier.is_empty() {
        return view.hasher.empty();
    }
    let h = view.hasher.as_ref();
    fold_frontier(view.frontier.clone(), k, |chunk| {
        let refs: Vec<&[u8]> = chunk.iter().map(|v| v.as_slice()).collect();
        nary_mr(h, &refs)
    })
}

/// One step of the base-k frontier carry for a single algorithm view.
///
/// Pushes `digest` onto the view's frontier at log position `count`, then runs
/// the [`reduction_count`] merges the schedule mandates, appending any newly
/// sealed internal node as `(left, height, hash)` to `out_nodes`. The view is
/// mutated in place; the carry is pure over `(view, digest, count, arity)`.
///
/// # Errors
///
/// Returns [`Error::Corrupted`] if the frontier or coordinate stack underflows
/// during a reduction — a structural invariant break, never expected for a
/// well-formed view.
pub fn carry<E>(
    view: &mut AlgView,
    alg_id: u64,
    digest: Vec<u8>,
    count: u64,
    arity: u64,
    out_nodes: &mut Vec<(u64, u64, u32, Vec<u8>)>,
) -> Result<(), E> {
    view.frontier.push(digest);
    view.frontier_coords.push((count, 0));

    let merges = reduction_count(count, arity);
    for _ in 0..merges {
        let mut children = Vec::with_capacity(arity as usize);
        let mut coords = Vec::with_capacity(arity as usize);
        for _ in 0..arity as usize {
            children.push(view.frontier.pop().ok_or_else(|| Error::Corrupted {
                alg_id,
                reason: "frontier stack underflow during reduction".to_string(),
            })?);
            coords.push(view.frontier_coords.pop().ok_or_else(|| Error::Corrupted {
                alg_id,
                reason: "frontier_coords stack underflow during reduction".to_string(),
            })?);
        }
        children.reverse();
        coords.reverse();
        let child_refs: Vec<&[u8]> = children.iter().map(|c| c.as_slice()).collect();
        let parent = nary_mr(view.hasher.as_ref(), &child_refs);

        let parent_left_index = coords[0].0;
        let parent_height = coords[0].1 + 1;

        if parent != view.hasher.null() {
            out_nodes.push((alg_id, parent_left_index, parent_height, parent.clone()));
        }

        view.frontier.push(parent);
        view.frontier_coords
            .push((parent_left_index, parent_height));
    }
    Ok(())
}

/// A frontier node carrying its hash and the path accumulated so far while
/// merging across the frontier reduction loop.
struct MergeNode {
    hash: Vec<u8>,
    path: Vec<ProofStep>,
}

/// Fold a set of frontier hashes (and an already-accumulated `bisect_path`)
/// across the canonical frontier-reduction loop, accumulating [`ProofStep`]s for
/// `target_idx` and appending them to `bisect_path`.
///
/// `hashes` must be the ordered list of frontier-node hashes (left-to-right).
/// `target_idx` is the index into `hashes` that the proof is for.
/// `k` is the log arity.
/// `hasher` supplies the hash combiner (`nary_mr`).
///
/// After the call `bisect_path` contains the complete frontier leg of the proof.
pub fn merge_frontier_paths(
    hashes: Vec<Vec<u8>>,
    target_idx: usize,
    k: usize,
    hasher: &dyn Hasher,
    bisect_path: &mut Vec<ProofStep>,
) {
    let mut current: Vec<MergeNode> = hashes
        .into_iter()
        .map(|h| MergeNode {
            hash: h,
            path: Vec::new(),
        })
        .collect();

    let mut target = target_idx;
    while current.len() > k {
        let split_idx = current.len() - k;

        let refs: Vec<&[u8]> = current[split_idx..]
            .iter()
            .map(|n| n.hash.as_slice())
            .collect();
        let merged_hash = nary_mr(hasher, &refs);

        let mut target_path = Vec::new();
        let mut is_target_merged = false;
        if target >= split_idx {
            let mut siblings = Vec::with_capacity(k - 1);
            for (j, item) in current.iter().enumerate().skip(split_idx) {
                if j != target {
                    siblings.push(item.hash.clone());
                }
            }
            let step = ProofStep {
                siblings,
                position: target - split_idx,
            };
            let mut p = std::mem::take(&mut current[target].path);
            p.push(step);
            target_path = p;
            is_target_merged = true;
        }

        if is_target_merged {
            current.truncate(split_idx);
            current.push(MergeNode {
                hash: merged_hash,
                path: target_path,
            });
            target = split_idx;
        } else {
            current.truncate(split_idx);
            current.push(MergeNode {
                hash: merged_hash,
                path: Vec::new(),
            });
        }
    }

    if current.len() > 1 {
        let mut siblings = Vec::with_capacity(current.len() - 1);
        for (j, item) in current.iter().enumerate() {
            if j != target {
                siblings.push(item.hash.clone());
            }
        }
        let step = ProofStep {
            siblings,
            position: target,
        };
        current[target].path.push(step);
    }

    bisect_path.extend(std::mem::take(&mut current[target].path));
}

/// Retrieve a node hash from the read substrate, or return the algorithm's null
/// constant if the coordinate's range carries no active leaf.
///
/// # Errors
///
/// Returns [`Error::Read`] on a backend error, or [`Error::Corrupted`] if a
/// stored node has the wrong digest width or an active range is missing its node.
pub async fn get_node_hash<R: NodeReader>(
    reader: &R,
    view: &AlgView,
    alg_id: u64,
    left: u64,
    height: u32,
    arity: u64,
) -> Result<Vec<u8>, R::Error> {
    let cap = match arity.checked_pow(height) {
        Some(c) => c,
        None => return Ok(view.hasher.null()),
    };
    let limit = match left.checked_add(cap) {
        Some(val) => val,
        None => return Ok(view.hasher.null()),
    };
    if !view.active_range(left, limit) {
        return Ok(view.hasher.null());
    }
    if let Some(hash) = reader
        .get_node(alg_id, left, height)
        .await
        .map_err(Error::Read)?
    {
        let expected = view.hasher.null().len();
        if hash.len() != expected {
            return Err(Error::Corrupted {
                alg_id,
                reason: format!(
                    "node at left {left} height {height} has wrong digest length: expected \
                     {expected}, got {}",
                    hash.len()
                ),
            });
        }
        Ok(hash)
    } else {
        // Any node whose range has at least one active leaf will be stored
        // as a non-null value (null requires every active leaf to collide
        // with the null digest — negligible probability). A missing node
        // in any active range is therefore corruption, whether the range is
        // fully or only partially active.
        Err(Error::Corrupted {
            alg_id,
            reason: format!(
                "missing internal node for algorithm {alg_id} at left {left} height {height}"
            ),
        })
    }
}

/// Generate an inclusion proof for `index` in a tree of size `tree_size` for the
/// algorithm `view`, reading nodes through `reader`. Returns `None` when out of
/// range or `tree_size` exceeds the algorithm's committed size.
///
/// # Errors
///
/// Propagates [`Error`] from the node reads.
pub async fn inclusion_proof<R: NodeReader>(
    reader: &R,
    view: &AlgView,
    alg_id: u64,
    index: u64,
    tree_size: u64,
    global_size: u64,
    arity: u64,
) -> Result<Option<crate::consistency::InclusionProof>, R::Error> {
    let max_size = view.tree_size(global_size);

    if tree_size == 0 || index >= tree_size || tree_size > max_size {
        return Ok(None);
    }

    let k = arity;
    let coords = frontier_for_size(tree_size, k);

    let mut target_f_idx = None;
    for (f_idx, &(left, height)) in coords.iter().enumerate() {
        let cap = k.pow(height);
        if index >= left && index < left + cap {
            target_f_idx = Some((f_idx, left, height));
            break;
        }
    }

    let (f_idx, left, height) = match target_f_idx {
        Some(val) => val,
        None => return Ok(None),
    };

    let mut path = Vec::new();
    log_level_bisection_path_to_height(
        reader, view, alg_id, left, height, index, 0, arity, &mut path,
    )
    .await?;
    path.reverse();

    let mut hashes = Vec::with_capacity(coords.len());
    for &(l, h) in &coords {
        let hash = get_node_hash(reader, view, alg_id, l, h, arity).await?;
        hashes.push(hash);
    }

    merge_frontier_paths(
        hashes,
        f_idx,
        arity as usize,
        view.hasher.as_ref(),
        &mut path,
    );

    // The log spine's shape is owned by the topology module; generation must
    // emit exactly the skeleton the verifier will check against. This holds by
    // construction — the pin guards against the producer and verifier drifting.
    debug_assert!(
        spine::inclusion_skeleton(k, tree_size, index).is_some_and(|skeleton| {
            skeleton.len() == path.len()
                && path.iter().zip(skeleton.iter()).all(|(step, shape)| {
                    step.position == shape.position && step.siblings.len() == shape.sibling_count
                })
        }),
        "generated inclusion proof must match the canonical log skeleton"
    );

    Ok(Some(crate::consistency::InclusionProof { path }))
}

/// Produce a self-contained [`spine::LeafProof`] for `index` in a tree of size
/// `tree_size`. Returns `None` when no inclusion proof exists.
///
/// # Errors
///
/// Propagates [`Error`] from the node reads.
pub async fn leaf_proof<R: NodeReader>(
    reader: &R,
    view: &AlgView,
    alg_id: u64,
    index: u64,
    tree_size: u64,
    global_size: u64,
    arity: u64,
) -> Result<Option<spine::LeafProof>, R::Error> {
    let Some(proof) =
        inclusion_proof(reader, view, alg_id, index, tree_size, global_size, arity).await?
    else {
        return Ok(None);
    };
    // The leaf digest is the height-0 node at the leaf's position.
    let leaf_hash = get_node_hash(reader, view, alg_id, index, 0, arity).await?;
    Ok(Some(spine::LeafProof::new(
        leaf_hash, index, tree_size, arity, proof.path,
    )))
}

/// Generate a consistency proof between `old_size` and `new_size` for the
/// algorithm `view`. Returns `None` when the request is out of range.
///
/// # Errors
///
/// Propagates [`Error`] from the node reads.
#[allow(clippy::too_many_arguments)]
pub async fn consistency_proof<R: NodeReader>(
    reader: &R,
    view: &AlgView,
    alg_id: u64,
    old_size: u64,
    new_size: u64,
    global_size: u64,
    arity: u64,
) -> Result<Option<crate::consistency::ConsistencyProof>, R::Error> {
    let max_size = view.tree_size(global_size);

    if old_size == 0 || old_size >= new_size || new_size > max_size {
        return Ok(None);
    }

    let k = arity;
    let old_coords = frontier_for_size(old_size, k);
    let &(boundary_left, boundary_height) = old_coords.last().ok_or_else(|| Error::Corrupted {
        alg_id,
        reason: "empty old_coords for non-zero old_size".to_string(),
    })?;

    let start_hash =
        get_node_hash(reader, view, alg_id, boundary_left, boundary_height, arity).await?;

    let new_coords = frontier_for_size(new_size, k);
    let mut target_new_f_idx = None;
    for (f_idx, &(new_left, new_height)) in new_coords.iter().enumerate() {
        let cap = k.pow(new_height);
        if boundary_left >= new_left && boundary_left < new_left + cap {
            target_new_f_idx = Some((f_idx, new_left, new_height));
            break;
        }
    }

    let (f_idx, left, height) = match target_new_f_idx {
        Some(val) => val,
        None => return Ok(None),
    };

    if height < boundary_height {
        return Ok(None);
    }

    let mut path = Vec::new();
    log_level_bisection_path_to_height(
        reader,
        view,
        alg_id,
        left,
        height,
        boundary_left,
        boundary_height,
        arity,
        &mut path,
    )
    .await?;
    path.reverse();

    let mut hashes = Vec::with_capacity(new_coords.len());
    for &(l, h) in &new_coords {
        let hash = get_node_hash(reader, view, alg_id, l, h, arity).await?;
        hashes.push(hash);
    }

    merge_frontier_paths(
        hashes,
        f_idx,
        arity as usize,
        view.hasher.as_ref(),
        &mut path,
    );

    Ok(Some(crate::consistency::ConsistencyProof {
        start_hash,
        path,
    }))
}

#[allow(clippy::too_many_arguments)]
async fn log_level_bisection_path_to_height<R: NodeReader>(
    reader: &R,
    view: &AlgView,
    alg_id: u64,
    left_index: u64,
    height: u32,
    target_index: u64,
    target_height: u32,
    arity: u64,
    path: &mut Vec<ProofStep>,
) -> Result<(), R::Error> {
    let mut curr_left = left_index;
    let mut curr_height = height;
    let k = arity;

    while curr_height > target_height {
        let child_capacity = k.pow(curr_height - 1);
        let child_idx = (target_index - curr_left) / child_capacity;

        let mut siblings = Vec::with_capacity(arity as usize - 1);
        for j in 0..arity as usize {
            let j_u64 = j as u64;
            if j_u64 == child_idx {
                continue;
            }
            let c_left = curr_left + j_u64 * child_capacity;
            let hash = get_node_hash(reader, view, alg_id, c_left, curr_height - 1, arity).await?;
            siblings.push(hash);
        }

        path.push(ProofStep {
            siblings,
            position: child_idx as usize,
        });

        curr_left += child_idx * child_capacity;
        curr_height -= 1;
    }
    Ok(())
}

/// The materialized digest of the frontier peak at coordinate `(left, height)` —
/// one perfect k-ary subtree root of the frontier. Returns the algorithm's null
/// constant for a coordinate whose range carries no active leaf.
///
/// # Errors
///
/// Propagates [`Error`] from the node read.
pub async fn peak_at<R: NodeReader>(
    reader: &R,
    view: &AlgView,
    alg_id: u64,
    left: u64,
    height: u32,
    arity: u64,
) -> Result<Vec<u8>, R::Error> {
    get_node_hash(reader, view, alg_id, left, height, arity).await
}

/// Retrieve the raw member root for the algorithm at a historical tree size.
///
/// # Errors
///
/// Propagates [`Error`] from the node reads.
pub async fn root_for_at<R: NodeReader>(
    reader: &R,
    view: &AlgView,
    alg_id: u64,
    size: u64,
    arity: u64,
) -> Result<Vec<u8>, R::Error> {
    let alg_size = view.effective_size_at(size);

    if alg_size == 0 {
        return Ok(view.hasher.empty());
    }

    let k = arity as usize;
    let coords = frontier_for_size(alg_size, arity);

    let mut frontier = Vec::with_capacity(coords.len());
    for &(left, height) in &coords {
        let hash = get_node_hash(reader, view, alg_id, left, height, arity).await?;
        frontier.push(hash);
    }

    if frontier.is_empty() {
        return Ok(view.hasher.empty());
    }
    let h = view.hasher.as_ref();
    Ok(fold_frontier(frontier, k, |chunk| {
        let refs: Vec<&[u8]> = chunk.iter().map(|v| v.as_slice()).collect();
        nary_mr(h, &refs)
    }))
}

/// Gather an algorithm's frontier peaks at `size` — the digests of the perfect
/// k-ary subtrees [`frontier_for_size`] names, the structural snapshot facet a
/// [`spine::Seal`] freezes. Each peak is the algorithm's null constant for a
/// coordinate whose range carries no active leaf.
///
/// # Errors
///
/// Propagates [`Error`] from the node reads.
pub async fn frontier_peaks<R: NodeReader>(
    reader: &R,
    view: &AlgView,
    alg_id: u64,
    size: u64,
    arity: u64,
) -> Result<Vec<Vec<u8>>, R::Error> {
    let coords = frontier_for_size(size, arity);
    let mut peaks = Vec::with_capacity(coords.len());
    for &(left, height) in &coords {
        peaks.push(peak_at(reader, view, alg_id, left, height, arity).await?);
    }
    Ok(peaks)
}

/// Validate an algorithm's committed epoch intervals against the global size.
///
/// # Errors
///
/// Returns [`Error::Corrupted`] for an empty, non-monotonic, or out-of-range
/// interval sequence.
pub fn validate_epochs<E>(alg_id: u64, epochs: &[(u64, u64)], global_size: u64) -> Result<(), E> {
    if epochs.is_empty() {
        return Err(Error::Corrupted {
            alg_id,
            reason: "epoch sequence is empty".to_string(),
        });
    }
    let mut last_end = 0;
    for (i, &(start, end)) in epochs.iter().enumerate() {
        if start > end {
            return Err(Error::Corrupted {
                alg_id,
                reason: format!("epoch start {start} exceeds end {end}"),
            });
        }
        if start < last_end {
            return Err(Error::Corrupted {
                alg_id,
                reason: format!("epoch start {start} is less than prior end {last_end}"),
            });
        }
        if end != u64::MAX && end > global_size {
            return Err(Error::Corrupted {
                alg_id,
                reason: format!("epoch end {end} exceeds global size {global_size}"),
            });
        }
        if end == u64::MAX && i != epochs.len() - 1 {
            return Err(Error::Corrupted {
                alg_id,
                reason: "open epoch (end = u64::MAX) is not the final entry".to_string(),
            });
        }
        last_end = end;
    }
    if let Some(&(start, end)) = epochs.last() {
        if end == u64::MAX && start > global_size {
            return Err(Error::Corrupted {
                alg_id,
                reason: format!("active epoch start {start} exceeds global size {global_size}"),
            });
        }
    }
    Ok(())
}

/// Reconstruct an algorithm's frontier view from the read substrate at
/// `global_size`. The hasher and committed `epochs` are supplied by the
/// combinator (which owns the timeline); the frontier peaks are read back.
///
/// # Errors
///
/// Propagates [`Error`] from the node reads, or [`Error::Corrupted`] for an
/// ill-formed epoch sequence or a missing frontier node.
pub async fn reconstruct_view<R: NodeReader>(
    reader: &R,
    alg_id: u64,
    hasher: Box<dyn Hasher>,
    epochs: &[(u64, u64)],
    global_size: u64,
    arity: u64,
) -> Result<AlgView, R::Error> {
    validate_epochs(alg_id, epochs, global_size)?;

    let is_active = epochs.last().is_some_and(|&(_, end)| end == u64::MAX);
    let tree_size = if is_active {
        global_size
    } else {
        epochs.last().map_or(0, |&(_, end)| end)
    };

    let mut view = AlgView {
        hasher,
        epochs: epochs.to_vec(),
        frontier: Vec::new(),
        frontier_coords: Vec::new(),
    };

    if tree_size == 0 {
        return Ok(view);
    }

    let coords = frontier_for_size(tree_size, arity);
    let mut frontier = Vec::with_capacity(coords.len());
    for &(left, height) in &coords {
        let cap = arity.pow(height);
        let hash = if !view.active_range(left, left + cap) {
            view.hasher.null()
        } else {
            reader
                .get_node(alg_id, left, height)
                .await
                .map_err(Error::Read)?
                .ok_or_else(|| Error::Corrupted {
                    alg_id,
                    reason: format!(
                        "missing frontier node for algorithm {alg_id} at left {left} height \
                         {height}"
                    ),
                })?
        };
        frontier.push(hash);
    }

    view.frontier = frontier;
    view.frontier_coords = coords;

    Ok(view)
}

/// Recursively resolve a subtree root over the read substrate and collect the
/// mixed boundary nodes that must be persisted (used when reopening a frozen
/// algorithm's frontier). Returns `(root, mixed_nodes)` where `mixed_nodes` are
/// `(left, height, hash)` triples.
///
/// # Errors
///
/// Propagates [`Error`] from the node/leaf reads.
#[allow(clippy::type_complexity)]
#[allow(clippy::too_many_arguments)]
pub fn reconstruct_subtree_root<'a, R>(
    reader: &'a R,
    alg_id: u64,
    view: &'a AlgView,
    lo: u64,
    hi: u64,
    k: u64,
    kind: LogKind,
    store_mixed: bool,
) -> std::pin::Pin<
    Box<
        dyn std::future::Future<Output = Result<(Vec<u8>, Vec<(u64, u32, Vec<u8>)>), R::Error>>
            + Send
            + 'a,
    >,
>
where
    R: NodeReader + Sync + 'a,
{
    Box::pin(async move {
        let size = hi - lo;
        if size == 0 {
            return Ok((view.hasher.empty(), Vec::new()));
        }
        if size == 1 {
            if view.is_active_at(lo) {
                if kind == LogKind::Subtree {
                    if let Some(hash) = reader.get_node(alg_id, lo, 0).await.map_err(Error::Read)? {
                        let expected = view.hasher.null().len();
                        if hash.len() != expected {
                            return Err(Error::Corrupted {
                                alg_id,
                                reason: format!(
                                    "subtree node at left {lo} height 0 has wrong digest length: \
                                     expected {expected}, got {}",
                                    hash.len()
                                ),
                            });
                        }
                        return Ok((hash, Vec::new()));
                    } else {
                        return Ok((view.hasher.null(), Vec::new()));
                    }
                } else {
                    let data = reader.get_leaf(lo).await.map_err(Error::Read)?;
                    return Ok((view.hasher.leaf(&data), Vec::new()));
                }
            }
            return Ok((view.hasher.null(), Vec::new()));
        }

        if !view.active_range(lo, hi) {
            return Ok((view.hasher.null(), Vec::new()));
        }

        let is_power_of_k = {
            let mut temp = size;
            while temp % k == 0 {
                temp /= k;
            }
            temp == 1
        };

        if is_power_of_k {
            let height = {
                let mut h = 0;
                let mut temp = size;
                while temp > 1 {
                    temp /= k;
                    h += 1;
                }
                h as u32
            };
            if view.fully_active(lo, hi) {
                if let Some(hash) = reader
                    .get_node(alg_id, lo, height)
                    .await
                    .map_err(Error::Read)?
                {
                    let expected = view.hasher.null().len();
                    if hash.len() != expected {
                        return Err(Error::Corrupted {
                            alg_id,
                            reason: format!(
                                "node at left {lo} height {height} has wrong digest length: \
                                 expected {expected}, got {}",
                                hash.len()
                            ),
                        });
                    }
                    return Ok((hash, Vec::new()));
                }
            }

            let child_size = size / k;
            let mut child_hashes = Vec::with_capacity(k as usize);
            let mut mixed_nodes = Vec::new();
            for j in 0..k {
                let c_lo = lo + j * child_size;
                let c_hi = lo + (j + 1) * child_size;
                let (child_hash, child_mixed) = reconstruct_subtree_root(
                    reader,
                    alg_id,
                    view,
                    c_lo,
                    c_hi,
                    k,
                    kind,
                    store_mixed,
                )
                .await?;
                child_hashes.push(child_hash);
                mixed_nodes.extend(child_mixed);
            }
            let child_refs: Vec<&[u8]> = child_hashes.iter().map(|c| c.as_slice()).collect();
            let hash = nary_mr(view.hasher.as_ref(), &child_refs);

            if store_mixed {
                mixed_nodes.push((lo, height, hash.clone()));
            }
            Ok((hash, mixed_nodes))
        } else {
            let coords = frontier_for_size(size, k);
            let mut component_hashes = Vec::with_capacity(coords.len());
            let mut mixed_nodes = Vec::new();
            for &(part_left, part_height) in &coords {
                let cap = k.pow(part_height);
                let c_lo = lo + part_left;
                let c_hi = c_lo + cap;
                let (part_root, part_mixed) = reconstruct_subtree_root(
                    reader,
                    alg_id,
                    view,
                    c_lo,
                    c_hi,
                    k,
                    kind,
                    store_mixed,
                )
                .await?;
                component_hashes.push(part_root);
                mixed_nodes.extend(part_mixed);
            }

            let k_usize = k as usize;
            let h = view.hasher.as_ref();
            let root = fold_frontier(component_hashes, k_usize, |chunk| {
                let refs: Vec<&[u8]> = chunk.iter().map(|v| v.as_slice()).collect();
                nary_mr(h, &refs)
            });
            Ok((root, mixed_nodes))
        }
    })
}

#[cfg(test)]
mod tests {
    use sha2::Digest as _;

    use super::*;

    /// A real fixed-width (32-byte) hasher. These tests exercise the view's
    /// epoch geometry, independent of digest content.
    #[derive(Debug)]
    struct TestHasher;
    impl Hasher for TestHasher {
        fn leaf(&self, data: &[u8]) -> Vec<u8> {
            sha2::Sha256::digest(data).to_vec()
        }

        fn node(&self, children: &[&[u8]]) -> Vec<u8> {
            let mut h = sha2::Sha256::new();
            for c in children {
                h.update(c);
            }
            h.finalize().to_vec()
        }

        fn empty(&self) -> Vec<u8> {
            sha2::Sha256::digest(b"").to_vec()
        }

        fn hash(&self, data: &[u8]) -> Vec<u8> {
            sha2::Sha256::digest(data).to_vec()
        }

        fn clone_box(&self) -> Box<dyn Hasher> {
            Box::new(TestHasher)
        }
    }

    // The committed timeline an `AlgView` projects at a historical size: intervals
    // past the size drop, an interval spanning the size encodes open, and an
    // interval closed exactly at the size stays closed (frontier-freshness).
    #[test]
    fn epochs_at_snapshot_clamping() {
        let view = AlgView {
            hasher: Box::new(TestHasher),
            epochs: vec![(2, 5), (7, 12), (15, u64::MAX)],
            frontier: Vec::new(),
            frontier_coords: Vec::new(),
        };
        // Not yet registered.
        assert_eq!(view.epochs_at(1), None);
        // Mid-interval: encoded open, later intervals dropped.
        assert_eq!(view.epochs_at(3), Some(vec![(2, u64::MAX)]));
        // Exactly at a deactivation boundary: stays closed.
        assert_eq!(view.epochs_at(5), Some(vec![(2, 5)]));
        // Between intervals.
        assert_eq!(view.epochs_at(6), Some(vec![(2, 5)]));
        // Activation exactly at the snapshot: registered, open, no content.
        assert_eq!(view.epochs_at(7), Some(vec![(2, 5), (7, u64::MAX)]));
        // Past all closed intervals, inside the open one.
        assert_eq!(
            view.epochs_at(20),
            Some(vec![(2, 5), (7, 12), (15, u64::MAX)])
        );
    }
}
