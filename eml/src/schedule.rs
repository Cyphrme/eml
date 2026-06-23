//! Base-k carry reduction schedule algorithm.

/// Number of k-ary merges after appending an item at 0-based index `n`.
///
/// Controls the frontier stack reduction for a configured log arity `k >= 2`.
///
/// # Panics
///
/// Panics if `k < 2` as the arity must be at least 2.
#[must_use]
pub fn reduction_count(n: u64, k: u64) -> u32 {
    assert!(k >= 2, "log arity k must be >= 2");
    let mut count = 0;
    let mut m = (n as u128) + 1; // 1-based index
    let k_u128 = k as u128;
    while m % k_u128 == 0 {
        count += 1;
        m /= k_u128;
    }
    count
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_reduction_count_k2() {
        // Equivalent to EML's count_trailing_ones
        let expected = vec![
            0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0,
            1, 0, 5,
        ];
        for (n, &exp) in expected.iter().enumerate() {
            assert_eq!(reduction_count(n as u64, 2), exp, "failed for k=2, n={}", n);
        }
    }

    #[test]
    fn test_reduction_count_k3() {
        let expected = vec![
            0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0,
            1, 0, 0,
        ];
        for (n, &exp) in expected.iter().enumerate() {
            assert_eq!(reduction_count(n as u64, 3), exp, "failed for k=3, n={}", n);
        }
    }

    #[test]
    fn test_reduction_count_k4() {
        let expected = vec![
            0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0,
            0, 0, 2,
        ];
        for (n, &exp) in expected.iter().enumerate() {
            assert_eq!(reduction_count(n as u64, 4), exp, "failed for k=4, n={}", n);
        }
    }

    #[test]
    #[should_panic(expected = "log arity k must be >= 2")]
    fn test_reduction_count_invalid_k() {
        let _ = reduction_count(0, 1);
    }

    /// Rust twin of every Lean `#guard` in `proofs/lean/EMLProof/Kary.lean`
    /// (`section SanityChecks`).
    ///
    /// These are the *same vectors*, transcribed value-for-value, so that
    /// definitional drift between the Lean topology model and the Rust source
    /// breaks a build on **either** side rather than going silent. Each Lean
    /// `#guard` is reproduced below in source order; if one is added there, add
    /// its twin here. Argument order differs by design: Lean takes the arity
    /// first (`frontierForSizeT k n`, `reductionCount k n`,
    /// `inclusionSkeleton k treeSize index`), the Rust API takes it last
    /// (`frontier_for_size(n, k)`, `reduction_count(n, k)`) or first
    /// (`inclusion_skeleton(k, tree_size, index)`).
    ///
    /// This guard couples both crates: `reduction_count` lives here in EML
    /// (the frontier carry); `frontier_for_size` / `inclusion_skeleton` /
    /// `SkeletonStep` live in the `pmt` kernel. It stays where it can reach
    /// both.
    #[test]
    fn lean_guard_parity() {
        use pmt::topology::{SkeletonStep, frontier_for_size, inclusion_skeleton};

        let step = |position: usize, sibling_count: usize| SkeletonStep {
            position,
            sibling_count,
        };

        // frontierForSizeT k n  ⟷  frontier_for_size(n, k)
        assert_eq!(frontier_for_size(5, 2), vec![(0u64, 2u32), (4, 0)]);
        assert_eq!(frontier_for_size(5, 3), vec![(0, 1), (3, 0), (4, 0)]);
        assert_eq!(frontier_for_size(0, 2), Vec::<(u64, u32)>::new());

        // (List.range _).map (reductionCount k)  ⟷  reduction_count(n, k)
        let rc2: Vec<u32> = (0..8).map(|n| reduction_count(n, 2)).collect();
        assert_eq!(rc2, vec![0, 1, 0, 2, 0, 1, 0, 3]);
        let rc3: Vec<u32> = (0..9).map(|n| reduction_count(n, 3)).collect();
        assert_eq!(rc3, vec![0, 0, 1, 0, 0, 1, 0, 0, 2]);

        // inclusionSkeleton k treeSize index  ⟷  inclusion_skeleton(k, tree_size, index)
        // Each Lean pair `(position, siblingCount)` maps to one `SkeletonStep`.
        assert_eq!(inclusion_skeleton(2, 1, 0), Some(vec![])); // singleton: empty path
        assert_eq!(inclusion_skeleton(2, 5, 4), Some(vec![step(1, 1)])); // lone height-0 node
        assert_eq!(
            inclusion_skeleton(2, 4, 1),
            Some(vec![step(1, 1), step(0, 1)])
        ); // two digit steps
        assert_eq!(inclusion_skeleton(3, 4, 3), Some(vec![step(1, 1)]));
        assert_eq!(inclusion_skeleton(2, 4, 4), None); // index out of range
        assert_eq!(inclusion_skeleton(1, 4, 0), None); // arity out of range
    }
}
