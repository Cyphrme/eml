//! Combinator driver behavior ported from the pre-decomposition `eml::tree`
//! unit tests: live leaf proofs accept/reject, structural node storage, and the
//! `resume`-from-`Sealed` round-trip with a consistency proof bridging the
//! resume boundary. These exercise the `NaryMerkleLog` driver over the CML
//! engine end to end.

use polydigest::{Hasher, MemoryStorage, NaryMerkleLog, Storage, TreeConfig};
use sha2::{Digest, Sha256};

#[derive(Debug, Clone)]
struct Sha256Hasher;
impl Hasher for Sha256Hasher {
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
        Box::new(self.clone())
    }
}

// A live leaf proof accepts the legitimate leaf at every position and rejects a
// forged leaf at the same position, across a sweep of positions.
#[test]
fn leaf_proof_accepts_legit_and_rejects_forged() {
    smol::block_on(async {
        let mut log = NaryMerkleLog::new(
            MemoryStorage::new(),
            Box::new(Sha256Hasher),
            TreeConfig { arity: 2 },
        )
        .await
        .unwrap();

        let payloads: Vec<Vec<u8>> = (0..12u64)
            .map(|i| format!("item-{i}").into_bytes())
            .collect();
        for p in &payloads {
            log.append_leaf(p).await.unwrap();
        }

        let size = payloads.len() as u64;
        let root = log.root_for_at(0, size).await.unwrap();
        let h = Sha256Hasher;

        for index in 0..size {
            let proof = log
                .leaf_proof(index, size)
                .await
                .unwrap()
                .expect("in range");
            assert_eq!(proof.index, index);
            assert_eq!(proof.tree_size, size);
            assert_eq!(proof.arity, 2);
            // The log's concrete MMR skeleton for this leaf's trusted position.
            let sk = polydigest::mountain_skeleton(2, size, index).expect("valid position");
            assert!(proof.verify(&h, &sk, &root), "index={index}");
            let mut forged = proof.clone();
            forged.leaf_hash = h.leaf(b"forged-item");
            assert!(!forged.verify(&h, &sk, &root), "index={index}");
        }

        // Out of range yields no proof.
        assert!(log.leaf_proof(size, size).await.unwrap().is_none());
    });
}

// The structural node id `(alg_id, left, height)` is what the combinator's store
// is keyed by; a 2-leaf binary log seals one internal node at coordinate (0, 1).
#[test]
fn structural_node_id_storage() {
    smol::block_on(async {
        let mut log = NaryMerkleLog::new(
            MemoryStorage::new(),
            Box::new(Sha256Hasher),
            TreeConfig { arity: 2 },
        )
        .await
        .unwrap();

        log.append_leaf(b"a").await.unwrap();
        log.append_leaf(b"b").await.unwrap();

        let node_hash = log.storage().get_node(0, 0, 1).await.unwrap();
        assert!(
            node_hash.is_some(),
            "node at coordinate (0, 1) should be stored"
        );
    });
}

async fn eml_with(n: u64, k: usize) -> NaryMerkleLog<MemoryStorage> {
    let mut log = NaryMerkleLog::new(
        MemoryStorage::new(),
        Box::new(Sha256Hasher),
        TreeConfig { arity: k as u64 },
    )
    .await
    .unwrap();
    for i in 0..n {
        log.append_leaf(format!("leaf-{i}").as_bytes())
            .await
            .unwrap();
    }
    log
}

// RESUME from an EML-origin Sealed: the resumed log reproduces the sealed member
// root, appends forward, and a consistency proof bridges the resume boundary.
// Swept across sizes and arities — resume has no failure conditions.
#[test]
fn resume_from_eml_origin_reproduces_root_and_appends() {
    smol::block_on(async {
        let h = Sha256Hasher;
        for k in [2usize, 3, 4] {
            for n in 1u64..16 {
                let log = eml_with(n, k).await;
                let sealed_member = log.root_for_at(0, n).await.unwrap();
                let sealed = log.seal().await.unwrap();

                let mut resumed = NaryMerkleLog::resume(
                    &sealed,
                    MemoryStorage::new(),
                    vec![(0, Box::new(Sha256Hasher))],
                )
                .await
                .expect("resume never fails for a well-formed Sealed");

                assert_eq!(resumed.count(), n);
                assert_eq!(
                    resumed.root_for_at(0, n).await.unwrap(),
                    sealed_member,
                    "resumed root must reproduce the sealed member root (n={n}, k={k})"
                );

                resumed
                    .append_subtree(&polydigest::Subtree::Leaf(b"fwd-0".to_vec()))
                    .await
                    .unwrap();
                resumed
                    .append_subtree(&polydigest::Subtree::Leaf(b"fwd-1".to_vec()))
                    .await
                    .unwrap();
                assert_eq!(resumed.count(), n + 2);

                // Consistency across the resume boundary holds.
                let proof = resumed.consistency_proof(n, n + 2).await.unwrap();
                assert!(
                    proof.is_some(),
                    "consistency must bridge resume (n={n}, k={k})"
                );
                let old_root = sealed_member.clone();
                let new_root = resumed.root_for_at(0, n + 2).await.unwrap();
                let proof = proof.unwrap();
                assert!(
                    polydigest::verify_consistency(
                        &h,
                        n,
                        n + 2,
                        k as u64,
                        &proof.boundary_hash,
                        &proof.peak_path,
                        &proof.new_peaks,
                        proof.split_index,
                        &old_root,
                        &new_root,
                    ),
                    "consistency proof must verify across resume (n={n}, k={k})"
                );
            }
        }
    });
}

// A missing hasher for an algorithm in the frontier is the one rejection.
#[test]
fn resume_rejects_missing_hasher() {
    smol::block_on(async {
        let log = eml_with(4, 2).await;
        let sealed = log.seal().await.unwrap();
        let err = NaryMerkleLog::resume(&sealed, MemoryStorage::new(), vec![])
            .await
            .unwrap_err();
        assert_eq!(err, polydigest::LogError::UnknownAlgorithm(0));
    });
}
