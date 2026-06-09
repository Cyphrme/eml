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
    let mut m = n + 1; // 1-based index
    while m % k == 0 {
        count += 1;
        m /= k;
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
}
