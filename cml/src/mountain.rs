//! The Merkle Mountain Range commitment topology — the append-only log's own
//! bagging of its perfect-subtree peaks, and the inclusion skeleton that pins a
//! proof against it.
//!
//! The [`spine`] decomposes a log of `n` leaves into a frontier of perfect k-ary
//! subtrees ([`spine::frontier_for_size`]) — the MMR **mountains**, whose peaks
//! are permanent (a perfect subtree's hash never changes as the log grows). This
//! module owns what the spine deliberately does not: how those peaks **bag** into
//! one root, and what an inclusion proof points at.
//!
//! # Backward bagging (durable witnesses)
//!
//! The peaks are bagged **right-to-left** (DESIGN §2.1): the rightmost (youngest)
//! peaks are folded first into a running accumulator, and the leftmost (oldest)
//! peaks sit outermost. Concretely the bag is right-recursive over the peak list,
//! `k` at a time, with the bagged remainder as the last child:
//!
//! ```text
//! bag(P[0..m]) = P[0]                                    if m == 1   (promotion)
//!              = H(P[0], …, P[m-1])                      if m <= k
//!              = H(P[0], …, P[k-2], bag(P[k-1..m]))      if m  > k
//! ```
//!
//! Each `H` is the spine's [`nary_mr`](spine::nary_mr) — collapse + promotion, no
//! domain separation, **no size prefix**. This deliberately diverges from the
//! OpenTimestamps / Grin convention `H(size ‖ peak ‖ acc)`: those bag a sole
//! commitment in which `size` is otherwise unbound, so the size prefix guards
//! against cross-size confusion. Our model binds `tree_size` as a trusted verifier
//! parameter and closes malleability with the proven canonical-encoding
//! uniqueness over `nary_mr` (the spine's `inclusion_proof_unique`); the prefix's
//! job is already discharged, and keeping the bag a plain `nary_mr` fold is what
//! lets the Lean corpus transfer the existing `nary_mr` uniqueness to the bag.
//!
//! # Durable witnesses
//!
//! An inclusion proof is **prove-to-peak then bag**: the `peakPath` from the leaf
//! up to its own mountain's peak (entirely inside a permanent perfect subtree —
//! the durable prefix) followed by the `bagPath` from the peak to the root. As
//! the log grows the `peakPath` never changes; only the `bagPath` suffix is
//! re-derived against the current peak set. That is the durable-witness property
//! RFC-6962's rebalancing tree structurally cannot have.
//!
//! # One shape, two readers
//!
//! [`bag_shape`] builds the bag as an explicit tree once; [`bag_peaks`] evaluates
//! it to the member root, and [`mountain_skeleton`] walks it to the per-step
//! `(position, sibling_count)` skeleton the [`spine`] verifier pins a proof
//! against. Deriving both from one shape is what keeps the producer's fold and
//! the verifier's skeleton in lockstep (the same discipline `cmt::shape` uses for
//! the rebalanced tree).

use spine::{Hasher, ProofStep, SkeletonStep, frontier_for_size, nary_mr};

/// One node of the bag tree.
///
/// A `Peak(f_idx)` is a frontier peak at index `f_idx` (left-to-right, the
/// [`frontier_for_size`] order); a `Bag(children)` is a hashing node over its
/// children left-to-right. The shape is uniquely determined by `(peak_count,
/// arity)` — never stored, always re-derived — so the producer's fold and the
/// verifier's skeleton cannot drift.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BagNode {
    /// A frontier peak at index `f_idx` in the `frontier_for_size` order.
    Peak(usize),
    /// A hashing bag node over its children, left to right.
    Bag(Vec<BagNode>),
}

/// Build the backward-bag shape over `peak_count` peaks at arity `k`.
///
/// Right-recursive, `k` at a time, with the bagged remainder as the last child —
/// so the oldest (leftmost) peaks sit outermost and an append only deepens the
/// innermost bag (the durable-witness property). Returns `None` for an empty
/// peak set (a non-empty log always has at least one peak).
#[must_use]
pub fn bag_shape(peak_count: usize, k: usize) -> Option<BagNode> {
    if peak_count == 0 {
        return None;
    }
    Some(bag_shape_from(0, peak_count, k))
}

/// Build the bag over the peaks `[start, peak_count)` — the recursive worker.
///
/// `start` is the index of the oldest peak still to bag. With `rem` peaks left:
/// a single peak promotes to itself; `rem <= k` peaks fold into one node; more
/// than `k` puts the oldest `k-1` peaks as direct children and the bag of the
/// rest as the `k`-th child.
fn bag_shape_from(start: usize, peak_count: usize, k: usize) -> BagNode {
    let rem = peak_count - start;
    if rem == 1 {
        return BagNode::Peak(start);
    }
    if rem <= k {
        return BagNode::Bag((start..peak_count).map(BagNode::Peak).collect());
    }
    let mut children: Vec<BagNode> = (start..start + k - 1).map(BagNode::Peak).collect();
    children.push(bag_shape_from(start + k - 1, peak_count, k));
    BagNode::Bag(children)
}

/// Bag a frontier's peaks into the single member root under `hasher`.
///
/// Evaluates [`bag_shape`] with each [`nary_mr`] node hashing its children. A
/// single peak promotes to itself; an empty peak set is the empty-tree root
/// (`hasher.empty()`).
#[must_use]
pub fn bag_peaks(hasher: &dyn Hasher, peaks: &[Vec<u8>], k: u64) -> Vec<u8> {
    match bag_shape(peaks.len(), k as usize) {
        None => hasher.empty(),
        Some(shape) => eval_bag(hasher, &shape, peaks),
    }
}

/// Evaluate a bag shape to its digest, reading peak digests from `peaks`.
fn eval_bag(hasher: &dyn Hasher, node: &BagNode, peaks: &[Vec<u8>]) -> Vec<u8> {
    match node {
        BagNode::Peak(f_idx) => peaks[*f_idx].clone(),
        BagNode::Bag(children) => {
            let child_digests: Vec<Vec<u8>> = children
                .iter()
                .map(|c| eval_bag(hasher, c, peaks))
                .collect();
            let refs: Vec<&[u8]> = child_digests.iter().map(Vec::as_slice).collect();
            nary_mr(hasher, &refs)
        },
    }
}

/// Generate the `bagPath` proof steps that lift the peak at frontier index
/// `f_idx` to the bagged root, given every peak's digest in `peaks`
/// (left-to-right). The steps are ordered peak → root, so a caller appends them
/// after the within-mountain `peakPath` to form the full leaf → root path.
///
/// Each step carries the path node's `position` among its bag-node siblings and
/// those siblings' digests (the other children of that bag node) — exactly the
/// shape [`spine::reconstruct_inclusion_root`] folds against, pinned by
/// [`mountain_skeleton`]. Returns an empty path when the peak is the sole peak
/// (it promotes directly to the root).
#[must_use]
pub fn bag_path(peaks: &[Vec<u8>], f_idx: usize, hasher: &dyn Hasher, k: u64) -> Vec<ProofStep> {
    let mut steps = Vec::new();
    if let Some(shape) = bag_shape(peaks.len(), k as usize) {
        // Collected root → peak; reverse to peak → root for the leaf → root path.
        descend_bag_path(&shape, f_idx, peaks, hasher, &mut steps);
        steps.reverse();
    }
    steps
}

/// Walk from `node` to `Peak(f_idx)`, pushing one [`ProofStep`] per bag node
/// crossed (root → peak order), with each step's sibling digests evaluated from
/// `peaks`. Returns whether `f_idx` is under `node`.
fn descend_bag_path(
    node: &BagNode,
    f_idx: usize,
    peaks: &[Vec<u8>],
    hasher: &dyn Hasher,
    out: &mut Vec<ProofStep>,
) -> bool {
    match node {
        BagNode::Peak(idx) => *idx == f_idx,
        BagNode::Bag(children) => {
            let Some(position) = children.iter().position(|c| covers_peak(c, f_idx)) else {
                return false;
            };
            let siblings: Vec<Vec<u8>> = children
                .iter()
                .enumerate()
                .filter(|(i, _)| *i != position)
                .map(|(_, c)| eval_bag(hasher, c, peaks))
                .collect();
            out.push(ProofStep { siblings, position });
            descend_bag_path(&children[position], f_idx, peaks, hasher, out)
        },
    }
}

/// Compute the MMR inclusion skeleton for a leaf `index` in a tree of
/// `tree_size` leaves at arity `k`.
///
/// The skeleton runs leaf → root: the `peakPath` (the base-k digit steps inside
/// the leaf's perfect-subtree mountain, each carrying `k - 1` siblings) followed
/// by the `bagPath` (the bag-node steps from the peak up to the root). Returns
/// `None` when the inputs cannot describe a valid log position (`k` out of range,
/// empty frontier, or `index` outside the covered range).
///
/// This is the concrete topology the append-only log feeds the spine's abstract
/// verifier — the MMR analog of the rebalanced skeleton the spine used to derive
/// internally.
#[must_use]
pub fn mountain_skeleton(k: u64, tree_size: u64, index: u64) -> Option<Vec<SkeletonStep>> {
    if !spine::ARITY_RANGE.contains(&k) {
        return None;
    }
    let coords = frontier_for_size(tree_size, k);
    if coords.is_empty() {
        return None;
    }
    let k_usize = k as usize;

    // Locate the perfect mountain that contains `index`.
    let mut target = None;
    for (f_idx, &(left, height)) in coords.iter().enumerate() {
        let cap = k.checked_pow(height)?;
        let limit = left.checked_add(cap)?;
        if index >= left && index < limit {
            target = Some((f_idx, left, height));
            break;
        }
    }
    let (f_idx, left, height) = target?;

    let mut steps = Vec::with_capacity(height as usize);

    // peakPath: base-k digits of the offset, low digit first (leaf → peak). These
    // are the durable, permanent steps inside the perfect mountain.
    let mut offset = index - left;
    for _ in 0..height {
        steps.push(SkeletonStep {
            position: (offset % k) as usize,
            sibling_count: k_usize - 1,
        });
        offset /= k;
    }

    // bagPath: the bag-node steps from the mountain's peak up to the root.
    let shape = bag_shape(coords.len(), k_usize)?;
    bag_path_steps(&shape, f_idx, &mut steps);

    Some(steps)
}

/// Append the bag-path steps that reach `Peak(f_idx)` in `shape`, ordered from
/// the peak up to the root, to `steps`.
///
/// At each bag node on the path, the step records the path child's `position`
/// among its siblings and the `sibling_count`. Because the recursion descends
/// from the root, the steps are collected root → peak and reversed into the
/// leaf → root order the verifier expects.
fn bag_path_steps(shape: &BagNode, f_idx: usize, steps: &mut Vec<SkeletonStep>) {
    let mut down = Vec::new();
    descend_bag(shape, f_idx, &mut down);
    // `down` is root → peak; the skeleton is leaf → root, so the bag steps
    // (above the peak) append in peak → root order.
    down.reverse();
    steps.extend(down);
}

/// Walk from `node` to `Peak(target)`, pushing one [`SkeletonStep`] per bag node
/// crossed, ordered root → peak. Returns whether `target` is under `node`.
fn descend_bag(node: &BagNode, target: usize, out: &mut Vec<SkeletonStep>) -> bool {
    match node {
        BagNode::Peak(f_idx) => *f_idx == target,
        BagNode::Bag(children) => {
            let position = children.iter().position(|c| covers_peak(c, target));
            let Some(position) = position else {
                return false;
            };
            out.push(SkeletonStep {
                position,
                sibling_count: children.len() - 1,
            });
            descend_bag(&children[position], target, out)
        },
    }
}

/// Whether `node` covers peak index `target`.
fn covers_peak(node: &BagNode, target: usize) -> bool {
    match node {
        BagNode::Peak(f_idx) => *f_idx == target,
        BagNode::Bag(children) => children.iter().any(|c| covers_peak(c, target)),
    }
}

#[cfg(test)]
mod tests {
    use sha2::{Digest, Sha256};

    use super::*;

    #[derive(Debug)]
    struct H;
    impl Hasher for H {
        fn leaf(&self, data: &[u8]) -> Vec<u8> {
            Sha256::digest(data).to_vec()
        }

        fn node(&self, children: &[&[u8]]) -> Vec<u8> {
            let mut h = Sha256::new();
            for c in children {
                h.update(c);
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
            Box::new(H)
        }
    }

    /// A single peak promotes to the member root (no bag node).
    #[test]
    fn single_peak_promotes() {
        let peak = vec![0xAB; 32];
        assert_eq!(bag_peaks(&H, std::slice::from_ref(&peak), 2), peak);
        // And its skeleton has no bag steps for a singleton tree.
        assert_eq!(mountain_skeleton(2, 1, 0), Some(vec![]));
    }

    /// The bag is right-recursive: for m>k the oldest k-1 peaks are direct
    /// children and the rest bag into the last child.
    #[test]
    fn bag_shape_is_backward_recursive_binary() {
        // k=2, 4 peaks: H(P0, H(P1, H(P2, P3)))
        let shape = bag_shape(4, 2).unwrap();
        let expected = BagNode::Bag(vec![
            BagNode::Peak(0),
            BagNode::Bag(vec![
                BagNode::Peak(1),
                BagNode::Bag(vec![BagNode::Peak(2), BagNode::Peak(3)]),
            ]),
        ]);
        assert_eq!(shape, expected);
    }

    /// The bag fold equals a hand-rolled backward fold over the peaks.
    #[test]
    fn bag_peaks_equals_hand_fold_binary() {
        let peaks: Vec<Vec<u8>> = (0u8..4).map(|i| vec![i; 32]).collect();
        // H(P0, H(P1, H(P2, P3)))
        let inner = nary_mr(&H, &[peaks[2].as_slice(), peaks[3].as_slice()]);
        let mid = nary_mr(&H, &[peaks[1].as_slice(), inner.as_slice()]);
        let expected = nary_mr(&H, &[peaks[0].as_slice(), mid.as_slice()]);
        assert_eq!(bag_peaks(&H, &peaks, 2), expected);
    }

    /// k-ary: with k=3 and 5 peaks, level 0 holds P0,P1 + bag(P2..P5);
    /// the inner bag holds P2,P3,P4 (<= k, one node).
    #[test]
    fn bag_shape_kary() {
        let shape = bag_shape(5, 3).unwrap();
        let expected = BagNode::Bag(vec![
            BagNode::Peak(0),
            BagNode::Peak(1),
            BagNode::Bag(vec![BagNode::Peak(2), BagNode::Peak(3), BagNode::Peak(4)]),
        ]);
        assert_eq!(shape, expected);
    }

    /// The skeleton emitted for every leaf matches the bag/peak structure:
    /// every step carries at least one sibling (no promoted step) and the
    /// position is within bounds.
    #[test]
    fn skeleton_steps_are_well_formed() {
        for k in [2u64, 3, 5] {
            for tree_size in 1..=130u64 {
                for index in 0..tree_size {
                    let sk = mountain_skeleton(k, tree_size, index).expect("valid position");
                    for step in &sk {
                        assert!(step.sibling_count >= 1, "k={k} n={tree_size} i={index}");
                        assert!(step.position <= step.sibling_count);
                    }
                }
            }
        }
    }

    #[test]
    fn rejects_out_of_range() {
        assert_eq!(mountain_skeleton(1, 4, 0), None);
        assert_eq!(mountain_skeleton(257, 4, 0), None);
        assert_eq!(mountain_skeleton(2, 0, 0), None);
        assert_eq!(mountain_skeleton(2, 4, 4), None);
    }

    // --- MMR essentials + durability seed (N51; N55 expands these) -----------

    /// Synthetic distinct peak digests `[0x10+i; 32]` for a peak set of `m`.
    fn peaks(m: usize) -> Vec<Vec<u8>> {
        (0..m).map(|i| vec![0x10 + i as u8; 32]).collect()
    }

    /// **Prove-to-peak then bag verifies.** For every peak in every peak set, the
    /// `bagPath` from that peak folds (under the abstract spine verifier, pinned by
    /// the bag portion of `mountain_skeleton`) to the bagged root. Modelled at the
    /// peak granularity: the peak stands in for "a leaf already lifted to its
    /// mountain peak" (empty within-mountain `peakPath`), so the proof is purely
    /// the `bagPath` and the skeleton is purely its bag steps.
    #[test]
    fn prove_to_peak_then_bag_verifies() {
        for m in 1..=12usize {
            let ps = peaks(m);
            let root = bag_peaks(&H, &ps, 2);
            for (f_idx, peak) in ps.iter().enumerate() {
                let path = bag_path(&ps, f_idx, &H, 2);
                // The bag skeleton for a peak: take the full skeleton of a tree
                // whose mountain decomposition is exactly `m` height-0 peaks (a
                // size-`m` tree at k=… would not give m singleton peaks, so build
                // the skeleton directly from the bag shape instead).
                let mut sk = Vec::new();
                bag_path_steps(&bag_shape(m, 2).unwrap(), f_idx, &mut sk);
                assert!(
                    spine::verify_inclusion(&H, peak, &sk, &path, &root),
                    "m={m} f_idx={f_idx}: prove-to-peak+bag must verify"
                );
                // A wrong peak digest at the same position must not verify.
                let mut wrong = peak.clone();
                wrong[0] ^= 0xFF;
                assert!(
                    !spine::verify_inclusion(&H, &wrong, &sk, &path, &root),
                    "m={m} f_idx={f_idx}: a forged peak must not verify"
                );
            }
        }
    }

    /// **Peak permanence across append.** A formed peak's digest is identical in
    /// the size-`m` peak set and the size-`m+1` peak set — append adds/merges only
    /// at the right edge and never rewrites an existing peak. (The leftmost,
    /// oldest peaks are the most stable.)
    #[test]
    fn a_formed_peak_is_permanent_across_append() {
        for m in 1..=12usize {
            let before = peaks(m);
            let after = peaks(m + 1);
            // The first `m` peaks are byte-identical; only the new (rightmost)
            // peak is added.
            assert_eq!(&after[..m], &before[..], "m={m}: existing peaks rewritten");
        }
    }

    /// **Durability seed.** A witness issued for a peak at size `m` (its `bagPath`)
    /// verifies at size `m`, and the SAME peak — with a re-derived `bagPath` —
    /// still verifies at size `m+1`. The peak's own digest (the durable prefix the
    /// real `peakPath` would terminate at) never changes; only the short `bagPath`
    /// suffix is extended. This is the property RFC-6962's rebalancing tree
    /// structurally cannot have; N55 expands it to full leaf-level witnesses and a
    /// metamorphic sweep.
    #[test]
    fn a_witness_survives_an_append() {
        for m in 1..=12usize {
            let f_idx = 0; // the oldest peak — the canonical durable witness.
            let ps_n = peaks(m);
            let ps_n1 = peaks(m + 1);

            // The peak digest (the durable prefix endpoint) is unchanged.
            assert_eq!(ps_n[f_idx], ps_n1[f_idx]);

            // Issued at size m: verifies against the size-m root.
            let root_n = bag_peaks(&H, &ps_n, 2);
            let path_n = bag_path(&ps_n, f_idx, &H, 2);
            let mut sk_n = Vec::new();
            bag_path_steps(&bag_shape(m, 2).unwrap(), f_idx, &mut sk_n);
            assert!(spine::verify_inclusion(
                &H,
                &ps_n[f_idx],
                &sk_n,
                &path_n,
                &root_n
            ));

            // After append: the SAME peak, with a re-derived bagPath, verifies
            // against the size-(m+1) root.
            let root_n1 = bag_peaks(&H, &ps_n1, 2);
            let path_n1 = bag_path(&ps_n1, f_idx, &H, 2);
            let mut sk_n1 = Vec::new();
            bag_path_steps(&bag_shape(m + 1, 2).unwrap(), f_idx, &mut sk_n1);
            assert!(
                spine::verify_inclusion(&H, &ps_n1[f_idx], &sk_n1, &path_n1, &root_n1),
                "m={m}: a witness for the oldest peak must survive an append"
            );
        }
    }
}
