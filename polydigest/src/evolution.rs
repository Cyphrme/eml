//! The epoch-coupled append-only evolution surface.
//!
//! The structural append-only [`ConsistencyProof`](cml::proof::ConsistencyProof)
//! is the CML engine's — it proves a tree at `old_size` is a prefix of one at
//! `new_size`, with no timeline. This module owns the two checks that *need* the
//! committed epoch timeline, and so belong to the combinator:
//!
//! - [`verify_epoch_evolution`] — the temporal analog of consistency over the committed timeline;
//! - [`verify_consistency_with_coupling`] — structural consistency composed with the coupling-proof
//!   opening of the combined root at each size.

use spine::Hasher;

use crate::root::{CouplingProof, VerifierConfig, validate_committed_epochs};

/// Verify that a committed epoch timeline at `new_size` is an append-only
/// evolution of one previously committed at `old_size` — the temporal analog
/// of a consistency proof.
///
/// Allowed transitions per algorithm: the old intervals are preserved
/// verbatim, except that an interval open at the old snapshot may since have
/// closed at or after `old_size`; additional intervals and newly registered
/// algorithms may only begin at or after `old_size`; algorithms never
/// disappear. Both timelines must be well-formed at their respective sizes.
#[must_use]
pub fn verify_epoch_evolution(
    old_epochs: &[(u64, Vec<(u64, u64)>)],
    old_size: u64,
    new_epochs: &[(u64, Vec<(u64, u64)>)],
    new_size: u64,
) -> bool {
    if old_size > new_size {
        return false;
    }
    if !validate_committed_epochs(old_epochs, old_size)
        || !validate_committed_epochs(new_epochs, new_size)
    {
        return false;
    }
    let lookup = |timeline: &[(u64, Vec<(u64, u64)>)], id: u64| {
        timeline
            .binary_search_by_key(&id, |&(tid, _)| tid)
            .ok()
            .map(|i| timeline[i].1.clone())
    };
    for (id, old) in old_epochs {
        let Some(new) = lookup(new_epochs, *id) else {
            return false;
        };
        if new.len() < old.len() {
            return false;
        }
        let last = old.len() - 1;
        if new[..last] != old[..last] {
            return false;
        }
        let (o_start, o_end) = old[last];
        let (n_start, n_end) = new[last];
        if n_start != o_start {
            return false;
        }
        if o_end == u64::MAX {
            // Open at the old snapshot: may remain open, or close at/after it.
            if n_end != u64::MAX && n_end < old_size {
                return false;
            }
        } else if n_end != o_end {
            return false;
        }
        if new[old.len()..].iter().any(|&(start, _)| start < old_size) {
            return false;
        }
    }
    for (id, new) in new_epochs {
        if lookup(old_epochs, *id).is_none()
            && new.first().is_some_and(|&(start, _)| start < old_size)
        {
            return false;
        }
    }
    true
}

/// Helper wrapper demonstrating consistency verification with decoupled coupling proofs.
#[must_use]
#[allow(clippy::too_many_arguments)]
pub fn verify_consistency_with_coupling(
    hasher: &dyn Hasher,
    alg_id: u64,
    old_size: u64,
    new_size: u64,
    arity: u64,
    boundary_hash: &[u8],
    peak_path: &[spine::ProofStep],
    new_peaks: &[Vec<u8>],
    split_index: usize,
    old_coupling: &CouplingProof,
    new_coupling: &CouplingProof,
    old_combined_root: &[u8],
    new_combined_root: &[u8],
    old_expected_active_algs: &[u64],
    new_expected_active_algs: &[u64],
    config: VerifierConfig,
) -> bool {
    let old_res = old_coupling.verify(
        hasher,
        alg_id,
        old_size,
        arity,
        old_combined_root,
        old_expected_active_algs,
        config,
    );
    let new_res = new_coupling.verify(
        hasher,
        alg_id,
        new_size,
        arity,
        new_combined_root,
        new_expected_active_algs,
        config,
    );

    match (old_res, new_res) {
        (Some(old_raw_root), Some(new_raw_root)) => cml::verify_consistency(
            hasher,
            old_size,
            new_size,
            arity,
            boundary_hash,
            peak_path,
            new_peaks,
            split_index,
            &old_raw_root,
            &new_raw_root,
        ),
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const MAX: u64 = u64::MAX;

    #[test]
    fn test_verify_epoch_evolution() {
        let old = vec![(0u64, vec![(0u64, MAX)])];
        // Stays open; closes at/after the old snapshot; gains a resume.
        assert!(verify_epoch_evolution(&old, 5, &[(0, vec![(0, MAX)])], 9));
        assert!(verify_epoch_evolution(&old, 5, &[(0, vec![(0, 5)])], 9));
        assert!(verify_epoch_evolution(&old, 5, &[(0, vec![(0, 7)])], 9));
        assert!(verify_epoch_evolution(
            &old,
            5,
            &[(0, vec![(0, 6), (8, MAX)])],
            9
        ));
        // New algorithm registered after the old snapshot.
        assert!(verify_epoch_evolution(
            &old,
            5,
            &[(0, vec![(0, MAX)]), (1, vec![(5, MAX)])],
            9
        ));

        // Rewritten activation boundary.
        assert!(!verify_epoch_evolution(&old, 5, &[(0, vec![(1, MAX)])], 9));
        // Closed before the old snapshot (the old snapshot witnessed it open).
        assert!(!verify_epoch_evolution(&old, 5, &[(0, vec![(0, 4)])], 9));
        // Algorithm disappeared.
        assert!(!verify_epoch_evolution(&old, 5, &[(1, vec![(5, MAX)])], 9));
        // Backdated resume.
        assert!(!verify_epoch_evolution(
            &[(0, vec![(0, 2)])],
            5,
            &[(0, vec![(0, 2), (3, MAX)])],
            9
        ));
        // Backdated new algorithm (would have appeared in the old snapshot).
        assert!(!verify_epoch_evolution(
            &old,
            5,
            &[(0, vec![(0, MAX)]), (1, vec![(2, MAX)])],
            9
        ));
        // Closed interval mutated.
        assert!(!verify_epoch_evolution(
            &[(0, vec![(0, 3)])],
            5,
            &[(0, vec![(0, 4)])],
            9
        ));
        // Shrinking snapshot sizes.
        assert!(!verify_epoch_evolution(&old, 9, &old, 5));
    }
}
