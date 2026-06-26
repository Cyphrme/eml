//! Acceptance tests for the MMR-native consistency proof shape.
//!
//! The consistency proof carries `(boundary_hash, peak_path, new_peaks,
//! split_index)`: the old tree's last peak included at one new frontier slot,
//! plus the new peaks to bag. These tests pin the load-bearing invariant — the
//! reshape moves no root — and the adversarial rejection surface.

use eml::{Hasher, MemoryStorage, NaryMerkleLog, TreeConfig};
use sha2::{Digest, Sha256};

#[derive(Debug)]
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
        Box::new(Sha256Hasher)
    }
}

/// Build a log of `n` leaves at arity `k` and return its member root. The leaf
/// payloads are a deterministic function of `(k, i)` so independently built logs
/// of the same size have byte-identical roots.
async fn root_at(k: u64, n: u64) -> Vec<u8> {
    let mut log = NaryMerkleLog::new(
        MemoryStorage::new(),
        Box::new(Sha256Hasher),
        TreeConfig { arity: k },
    )
    .await
    .unwrap();
    for i in 0..n {
        log.append_leaf(format!("leaf_{k}_{i}").as_bytes())
            .await
            .unwrap();
    }
    log.root()
}

/// The critical guard: across arities, sizes, and old-sizes, the reshaped proof's
/// reconstructed `old_root`/`new_root` equal the genuinely built roots at those
/// sizes (which equal `compute_root`). The wire format moved no root.
#[test]
fn reshaped_roots_equal_built_roots() {
    smol::block_on(async {
        for k in 2..=5u64 {
            let mut log = NaryMerkleLog::new(
                MemoryStorage::new(),
                Box::new(Sha256Hasher),
                TreeConfig { arity: k },
            )
            .await
            .unwrap();
            let mut roots_at = vec![log.root()]; // index 0 == empty tree
            for i in 0..33u64 {
                log.append_leaf(format!("leaf_{k}_{i}").as_bytes())
                    .await
                    .unwrap();
                roots_at.push(log.root());
            }

            for new in 2..=33u64 {
                let new_root = &roots_at[new as usize];
                for old in 1..new {
                    let proof = log.consistency_proof(old, new).await.unwrap().unwrap();
                    let (old_r, new_r) = eml::reconstruct_consistency_roots(
                        &Sha256Hasher,
                        old,
                        new,
                        k,
                        &proof.boundary_hash,
                        &proof.peak_path,
                        &proof.new_peaks,
                        proof.split_index,
                    )
                    .expect("honest proof must reconstruct");
                    assert_eq!(
                        &old_r, &roots_at[old as usize],
                        "old root moved: k={k} old={old} new={new}"
                    );
                    assert_eq!(
                        &new_r, new_root,
                        "new root moved: k={k} old={old} new={new}"
                    );
                }
            }
        }
    });
}

/// Round-trip plus baseline failures: an honest proof verifies; a mutated
/// `peak_path` sibling, a wrong `split_index`, or a swapped `new_peaks` entry all
/// reject. Cases span boundary-merges-leftward and no-merge (shared-peak) shapes.
#[test]
fn baseline_failures_reject() {
    smol::block_on(async {
        // (k, old, new): mixes single-peak merges, multi-peak merges, and a
        // no-climb shared-peak boundary (old=6,new=7 at k=2).
        for &(k, old, new) in &[
            (2u64, 3u64, 8u64),
            (2, 3, 7),
            (2, 6, 7),
            (3, 7, 9),
            (4, 5, 20),
        ] {
            let new_root = root_at(k, new).await;
            let old_root = root_at(k, old).await;
            let mut log = NaryMerkleLog::new(
                MemoryStorage::new(),
                Box::new(Sha256Hasher),
                TreeConfig { arity: k },
            )
            .await
            .unwrap();
            for i in 0..new {
                log.append_leaf(format!("leaf_{k}_{i}").as_bytes())
                    .await
                    .unwrap();
            }
            let proof = log.consistency_proof(old, new).await.unwrap().unwrap();

            let verify = |p: &eml::ConsistencyProof| {
                eml::verify_consistency(
                    &Sha256Hasher,
                    old,
                    new,
                    k,
                    &p.boundary_hash,
                    &p.peak_path,
                    &p.new_peaks,
                    p.split_index,
                    &old_root,
                    &new_root,
                )
            };

            assert!(
                verify(&proof),
                "honest proof must verify: k={k} old={old} new={new}"
            );

            // (a) Flip a byte in the first non-empty peak_path sibling.
            if let Some(step_idx) = proof
                .peak_path
                .iter()
                .position(|s| s.siblings.iter().any(|sib| !sib.is_empty()))
            {
                let mut bad = proof.clone();
                let sib = bad.peak_path[step_idx]
                    .siblings
                    .iter_mut()
                    .find(|s| !s.is_empty())
                    .unwrap();
                sib[0] ^= 0xFF;
                assert!(
                    !verify(&bad),
                    "mutated peak_path sibling must reject: k={k} old={old} new={new}"
                );
            }

            // (b) Wrong split_index.
            if proof.new_peaks.len() >= 2 {
                let mut bad = proof.clone();
                bad.split_index = (proof.split_index + 1) % proof.new_peaks.len();
                assert!(
                    !verify(&bad),
                    "wrong split_index must reject: k={k} old={old} new={new}"
                );
            }

            // (c) Swap two new_peaks entries.
            if proof.new_peaks.len() >= 2 {
                let mut bad = proof.clone();
                let last = bad.new_peaks.len() - 1;
                bad.new_peaks.swap(0, last);
                assert!(
                    !verify(&bad),
                    "swapped new_peaks must reject: k={k} old={old} new={new}"
                );
            }
        }
    });
}

/// Regression pin for the old-root reconstruction. When the boundary peak merges
/// leftward (here k=2, old=3, new=4: peaks `[(0,1),(2,0)]` collapse into the lone
/// new peak `(0,2)`), the older peaks that merged in ride along as the
/// `peak_path`'s left-siblings. Bagging only `new_peaks[..split_index]` plus the
/// boundary — omitting those merged peaks — yields a *different* root, so the old
/// root must be rebuilt from the inclusion path's left-siblings.
#[test]
fn old_root_needs_merged_left_siblings() {
    smol::block_on(async {
        let (k, old, new) = (2u64, 3u64, 4u64);
        let old_root = root_at(k, old).await;
        let mut log = NaryMerkleLog::new(
            MemoryStorage::new(),
            Box::new(Sha256Hasher),
            TreeConfig { arity: k },
        )
        .await
        .unwrap();
        for i in 0..new {
            log.append_leaf(format!("leaf_{k}_{i}").as_bytes())
                .await
                .unwrap();
        }
        let proof = log.consistency_proof(old, new).await.unwrap().unwrap();

        // The boundary genuinely merged leftward: it is the sole new peak's slot.
        assert_eq!(proof.split_index, 0);
        assert!(!proof.peak_path.is_empty(), "boundary must climb");

        // The naive "bag(new_peaks[..split] ++ [boundary])" set omits the merged
        // peak and so diverges from the true old root.
        let mut naive: Vec<Vec<u8>> = proof.new_peaks[..proof.split_index].to_vec();
        naive.push(proof.boundary_hash.clone());
        let naive_root = eml::bag_peaks(&Sha256Hasher, &naive, k);
        assert_ne!(
            naive_root, old_root,
            "merge case must diverge from the naive old-root formula"
        );

        // The real reconstruction (gathering the left-siblings) matches.
        let (old_r, _) = eml::reconstruct_consistency_roots(
            &Sha256Hasher,
            old,
            new,
            k,
            &proof.boundary_hash,
            &proof.peak_path,
            &proof.new_peaks,
            proof.split_index,
        )
        .unwrap();
        assert_eq!(old_r, old_root);
    });
}
