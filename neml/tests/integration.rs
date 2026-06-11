use neml::{Hasher, MemoryStorage, NaryMerkleLog, Storage, Subtree, TreeConfig};
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

#[test]
fn test_vector_1_single_leaf() {
    smol::block_on(async {
        let hasher = Sha256Hasher;
        let storage = MemoryStorage::new();
        let config = TreeConfig { log_arity: 2 };
        let mut log = NaryMerkleLog::new(storage, Box::new(hasher), config)
            .await
            .unwrap();

        log.append_leaf(b"hello").await.unwrap();
        let root = log.root();
        let expected = vec![
            0x2c, 0xf2, 0x4d, 0xba, 0x5f, 0xb0, 0xa3, 0x0e, 0x26, 0xe8, 0x3b, 0x2a, 0xc5, 0xb9,
            0xe2, 0x9e, 0x1b, 0x16, 0x1e, 0x5c, 0x1f, 0xa7, 0x42, 0x5e, 0x73, 0x04, 0x33, 0x62,
            0x93, 0x8b, 0x98, 0x24,
        ];
        assert_eq!(root, expected);
    });
}

#[test]
fn test_vector_2_two_leaves_k2() {
    smol::block_on(async {
        let hasher = Sha256Hasher;
        let storage = MemoryStorage::new();
        let config = TreeConfig { log_arity: 2 };
        let mut log = NaryMerkleLog::new(storage, Box::new(hasher), config)
            .await
            .unwrap();

        log.append_leaf(b"a").await.unwrap();
        log.append_leaf(b"b").await.unwrap();
        let root = log.root();

        let h_a = Sha256::digest(b"a");
        let h_b = Sha256::digest(b"b");
        let mut h = Sha256::new();
        h.update(h_a);
        h.update(h_b);
        let expected = h.finalize().to_vec();

        assert_eq!(root, expected);
    });
}

#[test]
fn test_vector_3_three_leaves_k2() {
    smol::block_on(async {
        let hasher = Sha256Hasher;
        let storage = MemoryStorage::new();
        let config = TreeConfig { log_arity: 2 };
        let mut log = NaryMerkleLog::new(storage, Box::new(hasher), config)
            .await
            .unwrap();

        log.append_leaf(b"a").await.unwrap();
        log.append_leaf(b"b").await.unwrap();
        log.append_leaf(b"c").await.unwrap();
        let root = log.root();

        let h_a = Sha256::digest(b"a");
        let h_b = Sha256::digest(b"b");
        let h_ab = Sha256::digest([h_a.as_slice(), h_b.as_slice()].concat());
        let h_c = Sha256::digest(b"c");

        let mut h = Sha256::new();
        h.update(h_ab);
        h.update(h_c);
        let expected = h.finalize().to_vec();

        assert_eq!(root, expected);
    });
}

#[test]
fn test_vector_4_singleton_promotion() {
    let hasher = Sha256Hasher;
    let tree = Subtree::Node(vec![Subtree::Leaf(b"x".to_vec())]);
    let evaluated = neml::evaluate(&hasher, &tree);
    let expected = Sha256::digest(b"x").to_vec();
    assert_eq!(evaluated, expected);
}

#[test]
fn test_vector_5_nested_promotion() {
    let hasher = Sha256Hasher;
    let tree = Subtree::Node(vec![Subtree::Node(vec![Subtree::Leaf(b"x".to_vec())])]);
    let evaluated = neml::evaluate(&hasher, &tree);
    let expected = Sha256::digest(b"x").to_vec();
    assert_eq!(evaluated, expected);
}

#[test]
fn test_vector_6_subtree_append_k2() {
    smol::block_on(async {
        let hasher = Sha256Hasher;
        let storage = MemoryStorage::new();
        let config = TreeConfig { log_arity: 2 };
        let mut log = NaryMerkleLog::new(storage, Box::new(hasher), config)
            .await
            .unwrap();

        let subtree0 = Subtree::Node(vec![
            Subtree::Leaf(b"a".to_vec()),
            Subtree::Leaf(b"b".to_vec()),
        ]);
        let subtree1 = Subtree::Node(vec![Subtree::Leaf(b"c".to_vec())]);

        log.append_subtree(&subtree0).await.unwrap();
        log.append_subtree(&subtree1).await.unwrap();
        let root = log.root();

        let h_a = Sha256::digest(b"a");
        let h_b = Sha256::digest(b"b");
        let h_ab = Sha256::digest([h_a.as_slice(), h_b.as_slice()].concat());
        let h_c = Sha256::digest(b"c");

        let mut h = Sha256::new();
        h.update(h_ab);
        h.update(h_c);
        let expected = h.finalize().to_vec();

        assert_eq!(root, expected);
    });
}

#[test]
fn test_vector_7_null_constant() {
    let hasher = Sha256Hasher;
    let null = hasher.null();
    let expected = neml::null_digest(&hasher);
    assert_eq!(null, expected);
}

#[test]
fn test_vector_8_three_leaves_k3_ternary() {
    smol::block_on(async {
        let hasher = Sha256Hasher;
        let storage = MemoryStorage::new();
        let config = TreeConfig { log_arity: 3 };
        let mut log = NaryMerkleLog::new(storage, Box::new(hasher), config)
            .await
            .unwrap();

        log.append_leaf(b"a").await.unwrap();
        log.append_leaf(b"b").await.unwrap();
        log.append_leaf(b"c").await.unwrap();
        let root = log.root();

        let h_a = Sha256::digest(b"a");
        let h_b = Sha256::digest(b"b");
        let h_c = Sha256::digest(b"c");

        let mut h = Sha256::new();
        h.update(h_a);
        h.update(h_b);
        h.update(h_c);
        let expected = h.finalize().to_vec();

        assert_eq!(root, expected);
    });
}

// Prefix-free binary MTH helper
fn manual_prefix_free_mth(hasher: &dyn Hasher, leaves: &[Vec<u8>]) -> Vec<u8> {
    if leaves.is_empty() {
        return hasher.empty();
    }
    if leaves.len() == 1 {
        return leaves[0].clone();
    }
    let n = leaves.len();
    let k = n.next_power_of_two() / 2;
    let k = if k == n { k / 2 } else { k };

    let left = manual_prefix_free_mth(hasher, &leaves[0..k]);
    let right = manual_prefix_free_mth(hasher, &leaves[k..n]);
    hasher.node(&[&left, &right])
}

#[test]
fn test_binary_compatibility_random_sizes() {
    smol::block_on(async {
        for size in 1..=16 {
            let storage = MemoryStorage::new();
            let config = TreeConfig { log_arity: 2 };
            let mut log = NaryMerkleLog::new(storage, Box::new(Sha256Hasher), config)
                .await
                .unwrap();

            let mut leaves = Vec::new();
            for i in 0..size {
                let data = format!("leaf_{}", i).into_bytes();
                log.append_leaf(&data).await.unwrap();
                leaves.push(Sha256Hasher.leaf(&data));
            }

            let mth_root = manual_prefix_free_mth(&Sha256Hasher, &leaves);
            assert_eq!(log.root(), mth_root, "binary MTH mismatch at size {}", size);
        }
    });
}

#[test]
fn test_inclusion_and_consistency_proofs_simple() {
    smol::block_on(async {
        let hasher = Sha256Hasher;
        let storage = MemoryStorage::new();
        let config = TreeConfig { log_arity: 2 };
        let mut log = NaryMerkleLog::new(storage, Box::new(hasher), config)
            .await
            .unwrap();

        log.append_leaf(b"a").await.unwrap();
        log.append_leaf(b"b").await.unwrap();
        log.append_leaf(b"c").await.unwrap();
        log.append_leaf(b"d").await.unwrap();

        let proof = log.inclusion_proof(2, 4).await.unwrap().unwrap();
        let leaf_hash = Sha256Hasher.leaf(b"c");
        let root = log.root();
        assert!(neml::verify_inclusion(
            &Sha256Hasher,
            &leaf_hash,
            2,
            4,
            2,
            &proof.path,
            &root
        ));

        let cons_proof = log.consistency_proof(2, 4).await.unwrap().unwrap();
        let old_root = {
            let mut temp_log = NaryMerkleLog::new(
                MemoryStorage::new(),
                Box::new(Sha256Hasher),
                TreeConfig { log_arity: 2 },
            )
            .await
            .unwrap();
            temp_log.append_leaf(b"a").await.unwrap();
            temp_log.append_leaf(b"b").await.unwrap();
            temp_log.root()
        };
        assert!(neml::verify_consistency(
            &Sha256Hasher,
            2,
            4,
            2,
            &cons_proof.start_hash,
            &cons_proof.path,
            &old_root,
            &root
        ));
    });
}

#[test]
fn test_inclusion_and_consistency_proofs_various_arities() {
    smol::block_on(async {
        for k in 2..=4 {
            for size in 1..=15 {
                let storage = MemoryStorage::new();
                let config = TreeConfig { log_arity: k };
                let mut log = NaryMerkleLog::new(storage, Box::new(Sha256Hasher), config)
                    .await
                    .unwrap();

                let mut leaves = Vec::new();
                for i in 0..size {
                    let data = format!("leaf_{}_{}", k, i).into_bytes();
                    log.append_leaf(&data).await.unwrap();
                    leaves.push(Sha256Hasher.leaf(&data));
                }

                let root = log.root();

                // Verify inclusion proof for every index
                for idx in 0..size {
                    let proof = log.inclusion_proof(idx, size).await.unwrap().unwrap();
                    assert!(neml::verify_inclusion(
                        &Sha256Hasher,
                        &leaves[idx as usize],
                        idx,
                        size,
                        k as u64,
                        &proof.path,
                        &root
                    ));
                }

                // Verify consistency proof for every valid old size
                for old_size in 1..size {
                    let cons_proof = log
                        .consistency_proof(old_size, size)
                        .await
                        .unwrap()
                        .unwrap();
                    let old_root = {
                        let mut temp_log = NaryMerkleLog::new(
                            MemoryStorage::new(),
                            Box::new(Sha256Hasher),
                            TreeConfig { log_arity: k },
                        )
                        .await
                        .unwrap();
                        for i in 0..old_size {
                            let data = format!("leaf_{}_{}", k, i).into_bytes();
                            temp_log.append_leaf(&data).await.unwrap();
                        }
                        temp_log.root()
                    };
                    if !neml::verify_consistency(
                        &Sha256Hasher,
                        old_size,
                        size,
                        k as u64,
                        &cons_proof.start_hash,
                        &cons_proof.path,
                        &old_root,
                        &root,
                    ) {
                        panic!(
                            "verify_consistency failed for k={}, size={}, old_size={}, \
                             cons_proof={:?}, old_root={:?}, root={:?}",
                            k, size, old_size, cons_proof, old_root, root
                        );
                    }
                }
            }
        }
    });
}

#[test]
fn test_inclusion_proofs_subtree_log_mode() {
    smol::block_on(async {
        let storage = MemoryStorage::new();
        let config = TreeConfig { log_arity: 2 };
        let mut log = NaryMerkleLog::new(storage, Box::new(Sha256Hasher), config)
            .await
            .unwrap();

        // Subtree 0: Subtree::Node([Leaf("a"), Leaf("b")])
        let subtree0 = Subtree::Node(vec![
            Subtree::Leaf(b"a".to_vec()),
            Subtree::Leaf(b"b".to_vec()),
        ]);

        // Subtree 1: Subtree::Node([Node([Leaf("c"), Leaf("d")]), Leaf("e")])
        let subtree1 = Subtree::Node(vec![
            Subtree::Node(vec![
                Subtree::Leaf(b"c".to_vec()),
                Subtree::Leaf(b"d".to_vec()),
            ]),
            Subtree::Leaf(b"e".to_vec()),
        ]);

        log.append_subtree(&subtree0).await.unwrap();
        log.append_subtree(&subtree1).await.unwrap();

        let root = log.root();

        // Generate within-subtree path
        let mut path = neml::within_subtree_path(&Sha256Hasher, &subtree1, 1).unwrap();

        // Generate log-level inclusion proof for Subtree 1
        let log_proof = log.inclusion_proof(1, 2).await.unwrap().unwrap();

        // Combine
        path.extend(log_proof.path);

        let leaf_hash = Sha256Hasher.leaf(b"d");
        let full_proof = neml::InclusionProof {
            path,
        };

        assert!(neml::verify_inclusion(
            &Sha256Hasher,
            &leaf_hash,
            1,
            2,
            2,
            &full_proof.path,
            &root
        ));
    });
}

#[test]
fn test_epoch_from_storage_single_algorithm() {
    smol::block_on(async {
        let hasher = Sha256Hasher;
        let storage = MemoryStorage::new();
        let config = TreeConfig { log_arity: 2 };
        let mut log = NaryMerkleLog::new(storage, Box::new(hasher), config)
            .await
            .unwrap();

        for i in 0..20u8 {
            log.append_leaf(&[i]).await.unwrap();
        }

        let original_root = log.root_for(0).unwrap();
        let original_size = log.size();

        let storage = log.into_storage();
        let reconstructed = NaryMerkleLog::from_storage(storage, vec![(0, Box::new(Sha256Hasher))])
            .await
            .unwrap();

        assert_eq!(reconstructed.size(), original_size);
        assert_eq!(reconstructed.root_for(0).unwrap(), original_root);
    });
}

#[test]
fn test_epoch_from_storage_multi_algorithm_frozen_active() {
    smol::block_on(async {
        let storage = MemoryStorage::new();
        let config = TreeConfig { log_arity: 3 };
        let mut log = NaryMerkleLog::new(storage, Box::new(Sha256Hasher), config)
            .await
            .unwrap();
        log.add_algorithm(1, Box::new(Sha256Hasher)).await.unwrap();

        for i in 0..10u8 {
            log.append_leaf(&[i]).await.unwrap();
        }

        // Freeze algorithm 1.
        log.remove_algorithm(1).await.unwrap();

        for i in 10..20u8 {
            log.append_leaf(&[i]).await.unwrap();
        }

        let root0 = log.root_for(0).unwrap();
        let root1 = log.root_for(1).unwrap();

        let storage = log.into_storage();
        let reconstructed = NaryMerkleLog::from_storage_with_config(
            storage,
            vec![(0, Box::new(Sha256Hasher)), (1, Box::new(Sha256Hasher))],
            config,
        )
        .await
        .unwrap();

        assert_eq!(reconstructed.root_for(0).unwrap(), root0);
        assert_eq!(reconstructed.root_for(1).unwrap(), root1);
    });
}

#[test]
fn test_epoch_from_storage_resume_after_gap() {
    smol::block_on(async {
        let storage = MemoryStorage::new();
        let config = TreeConfig { log_arity: 2 };
        let mut log = NaryMerkleLog::new(storage, Box::new(Sha256Hasher), config)
            .await
            .unwrap();

        for i in 0..4u8 {
            log.append_leaf(&[i]).await.unwrap();
        }
        log.remove_algorithm(0).await.unwrap();

        // Add a second algorithm to keep appends going.
        log.add_algorithm(1, Box::new(Sha256Hasher)).await.unwrap();
        for i in 4..8u8 {
            log.append_leaf(&[i]).await.unwrap();
        }

        log.resume_algorithm(0).await.unwrap();
        for i in 8..16u8 {
            log.append_leaf(&[i]).await.unwrap();
        }

        let root0 = log.root_for(0).unwrap();
        let root1 = log.root_for(1).unwrap();

        let storage = log.into_storage();
        let reconstructed = NaryMerkleLog::from_storage(
            storage,
            vec![(0, Box::new(Sha256Hasher)), (1, Box::new(Sha256Hasher))],
        )
        .await
        .unwrap();

        assert_eq!(reconstructed.root_for(0).unwrap(), root0);
        assert_eq!(reconstructed.root_for(1).unwrap(), root1);
    });
}

#[test]
fn test_epoch_from_storage_continued_appends() {
    smol::block_on(async {
        let mut original = NaryMerkleLog::new(
            MemoryStorage::new(),
            Box::new(Sha256Hasher),
            TreeConfig { log_arity: 2 },
        )
        .await
        .unwrap();
        for i in 0..10u8 {
            original.append_leaf(&[i]).await.unwrap();
        }

        let storage = original.into_storage();
        let mut reconstructed =
            NaryMerkleLog::from_storage(storage, vec![(0, Box::new(Sha256Hasher))])
                .await
                .unwrap();

        let mut reference = NaryMerkleLog::new(
            MemoryStorage::new(),
            Box::new(Sha256Hasher),
            TreeConfig { log_arity: 2 },
        )
        .await
        .unwrap();
        for i in 0..10u8 {
            reference.append_leaf(&[i]).await.unwrap();
        }

        for i in 10..20u8 {
            reconstructed.append_leaf(&[i]).await.unwrap();
            reference.append_leaf(&[i]).await.unwrap();
        }

        assert_eq!(
            reconstructed.root_for(0).unwrap(),
            reference.root_for(0).unwrap()
        );
        assert_eq!(reconstructed.size(), reference.size());
    });
}

#[test]
fn test_epoch_errors() {
    smol::block_on(async {
        let mut log = NaryMerkleLog::new(
            MemoryStorage::new(),
            Box::new(Sha256Hasher),
            TreeConfig { log_arity: 2 },
        )
        .await
        .unwrap();
        // Duplicate
        assert!(matches!(
            log.add_algorithm(0, Box::new(Sha256Hasher)).await,
            Err(neml::error::Error::DuplicateAlgorithm(0))
        ));
        // Unknown remove
        assert!(matches!(
            log.remove_algorithm(999).await,
            Err(neml::error::Error::UnknownAlgorithm(999))
        ));
        // Unknown resume
        assert!(matches!(
            log.resume_algorithm(999).await,
            Err(neml::error::Error::UnknownAlgorithm(999))
        ));

        log.remove_algorithm(0).await.unwrap();
        // Already frozen
        assert!(matches!(
            log.remove_algorithm(0).await,
            Err(neml::error::Error::FrozenAlgorithm(0))
        ));

        log.resume_algorithm(0).await.unwrap();
        // Already active
        assert!(matches!(
            log.resume_algorithm(0).await,
            Err(neml::error::Error::AlgorithmActive(0))
        ));
    });
}

#[test]
fn test_epoch_subtree_mode() {
    smol::block_on(async {
        let storage = MemoryStorage::new();
        let config = TreeConfig { log_arity: 2 };
        let mut log = NaryMerkleLog::new(storage, Box::new(Sha256Hasher), config)
            .await
            .unwrap();
        log.add_algorithm(1, Box::new(Sha256Hasher)).await.unwrap();

        let subtree0 = Subtree::Node(vec![
            Subtree::Leaf(b"a".to_vec()),
            Subtree::Leaf(b"b".to_vec()),
        ]);
        let subtree1 = Subtree::Node(vec![Subtree::Leaf(b"c".to_vec())]);

        log.append_subtree(&subtree0).await.unwrap();
        log.remove_algorithm(1).await.unwrap();
        log.append_subtree(&subtree1).await.unwrap();

        let root0 = log.root_for(0).unwrap();
        let root1 = log.root_for(1).unwrap(); // frozen at size 1

        let storage = log.into_storage();
        let reconstructed = NaryMerkleLog::from_storage(
            storage,
            vec![(0, Box::new(Sha256Hasher)), (1, Box::new(Sha256Hasher))],
        )
        .await
        .unwrap();

        assert_eq!(reconstructed.subtree_count(), 2);
        assert_eq!(reconstructed.root_for(0).unwrap(), root0);
        assert_eq!(reconstructed.root_for(1).unwrap(), root1);
    });
}

#[test]
fn test_epoch_proofs() {
    smol::block_on(async {
        let storage = MemoryStorage::new();
        let config = TreeConfig { log_arity: 2 };
        let mut log = NaryMerkleLog::new(storage, Box::new(Sha256Hasher), config)
            .await
            .unwrap();
        log.add_algorithm(1, Box::new(Sha256Hasher)).await.unwrap();

        log.append_leaf(b"a").await.unwrap();
        log.append_leaf(b"b").await.unwrap();
        log.remove_algorithm(1).await.unwrap();
        log.append_leaf(b"c").await.unwrap();
        log.append_leaf(b"d").await.unwrap();

        // Verify inclusion proof for algorithm 0 (fully active)
        let proof0 = log.inclusion_proof_for(0, 2, 4).await.unwrap().unwrap();
        let root0 = log.root_for(0).unwrap();
        assert!(neml::verify_inclusion(
            &Sha256Hasher,
            &Sha256Hasher.leaf(b"c"),
            2,
            4,
            2,
            &proof0.path,
            &root0
        ));

        // Verify inclusion proof for algorithm 1 (frozen at size 2)
        let proof1 = log.inclusion_proof_for(1, 1, 2).await.unwrap().unwrap();
        let root1 = log.root_for(1).unwrap();
        assert!(neml::verify_inclusion(
            &Sha256Hasher,
            &Sha256Hasher.leaf(b"b"),
            1,
            2,
            2,
            &proof1.path,
            &root1
        ));

        // For algorithm 1, index 2 (which is in inactive range) should be out of bounds/fail.
        assert!(log.inclusion_proof_for(1, 2, 2).await.unwrap().is_none());
    });
}

#[test]
fn test_resume_persists_mixed_nodes_malt() {
    smol::block_on(async {
        let storage = MemoryStorage::new();
        let config = TreeConfig { log_arity: 2 };
        let mut log = NaryMerkleLog::new(storage, Box::new(Sha256Hasher), config)
            .await
            .unwrap();

        // Epoch 1 active: 3 leaves (0, 1, 2)
        for i in 0..3u8 {
            log.append_leaf(&[i]).await.unwrap();
        }
        log.remove_algorithm(0).await.unwrap();

        // Gap: 5 leaves (3, 4, 5, 6, 7)
        log.add_algorithm(1, Box::new(Sha256Hasher)).await.unwrap();
        for i in 3..8u8 {
            log.append_leaf(&[i]).await.unwrap();
        }

        // Resume algorithm 0: total size = 8
        log.resume_algorithm(0).await.unwrap();

        let storage = log.into_storage();

        // Under size 8 and deactivation 3, mixed nodes are:
        // - [0, 8) height 3: coordinate (0, 0, 3)
        // - [0, 4) height 2: coordinate (0, 0, 2)
        // - [2, 4) height 1: coordinate (0, 2, 1)
        // Active node [0, 2) height 1 is also persisted (from initial appends): coordinate (0, 0,
        // 1)
        assert!(
            storage.nodes.contains_key(&(0, 0, 3)),
            "mixed node [0, 8) height 3 not persisted"
        );
        assert!(
            storage.nodes.contains_key(&(0, 0, 2)),
            "mixed node [0, 4) height 2 not persisted"
        );
        assert!(
            storage.nodes.contains_key(&(0, 2, 1)),
            "mixed node [2, 4) height 1 not persisted"
        );
        assert!(
            storage.nodes.contains_key(&(0, 0, 1)),
            "active node [0, 2) height 1 missing"
        );

        fn nary_mr_local(hasher: &dyn Hasher, children: &[&[u8]]) -> Vec<u8> {
            match children.len() {
                0 => hasher.empty(),
                1 => children[0].to_vec(),
                _ => {
                    let null_const = hasher.null();
                    if children.iter().all(|&c| c == null_const) {
                        null_const
                    } else {
                        hasher.node(children)
                    }
                },
            }
        }

        // Validate hashes match canonical calculation
        let h0 = Sha256Hasher.leaf(&[0]);
        let h1 = Sha256Hasher.leaf(&[1]);
        let h2 = Sha256Hasher.leaf(&[2]);
        let hn = Sha256Hasher.null();

        let n_0_2 = nary_mr_local(&Sha256Hasher, &[h0.as_slice(), h1.as_slice()]);
        let n_2_4 = nary_mr_local(&Sha256Hasher, &[h2.as_slice(), hn.as_slice()]);
        let n_0_4 = nary_mr_local(&Sha256Hasher, &[n_0_2.as_slice(), n_2_4.as_slice()]);

        let n_4_6 = nary_mr_local(&Sha256Hasher, &[hn.as_slice(), hn.as_slice()]);
        let n_6_8 = nary_mr_local(&Sha256Hasher, &[hn.as_slice(), hn.as_slice()]);
        let n_4_8 = nary_mr_local(&Sha256Hasher, &[n_4_6.as_slice(), n_6_8.as_slice()]);

        let n_0_8 = nary_mr_local(&Sha256Hasher, &[n_0_4.as_slice(), n_4_8.as_slice()]);

        assert_eq!(storage.nodes.get(&(0, 0, 3)), Some(&n_0_8));
        assert_eq!(storage.nodes.get(&(0, 0, 2)), Some(&n_0_4));
        assert_eq!(storage.nodes.get(&(0, 2, 1)), Some(&n_2_4));
    });
}

#[test]
fn test_promotion_proofs_malt() {
    smol::block_on(async {
        let storage = MemoryStorage::new();
        let config = TreeConfig { log_arity: 3 };
        let mut log = NaryMerkleLog::new(storage, Box::new(Sha256Hasher), config)
            .await
            .unwrap();

        log.append_leaf(b"x").await.unwrap();
        let root = log.root();

        let proof = log.inclusion_proof_for(0, 0, 1).await.unwrap().unwrap();
        // Single leaf tree with arity 3 has empty path steps (direct leaf-to-root promotion)
        assert!(proof.path.is_empty());
        assert!(neml::verify_inclusion(
            &Sha256Hasher,
            &Sha256Hasher.leaf(b"x"),
            0,
            1,
            3,
            &proof.path,
            &root
        ));

        // Append two more leaves: size 3 (which fills one 3-ary level)
        log.append_leaf(b"y").await.unwrap();
        log.append_leaf(b"z").await.unwrap();
        let root = log.root();

        // Inclusion proof for index 2
        let proof = log.inclusion_proof_for(0, 2, 3).await.unwrap().unwrap();
        assert_eq!(proof.path.len(), 1);
        assert!(neml::verify_inclusion(
            &Sha256Hasher,
            &Sha256Hasher.leaf(b"z"),
            2,
            3,
            3,
            &proof.path,
            &root
        ));
    });
}

#[test]
fn test_subtree_consistency_proofs() {
    smol::block_on(async {
        for k in 2..=4 {
            for size in 2..=15 {
                let storage = MemoryStorage::new();
                let config = TreeConfig { log_arity: k };
                let mut log = NaryMerkleLog::new(storage, Box::new(Sha256Hasher), config)
                    .await
                    .unwrap();

                let mut subtrees = Vec::new();
                for i in 0..size {
                    let subtree = if i % 2 == 0 {
                        Subtree::Node(vec![
                            Subtree::Leaf(format!("a_{}_{}", k, i).into_bytes()),
                            Subtree::Leaf(format!("b_{}_{}", k, i).into_bytes()),
                        ])
                    } else {
                        Subtree::Node(vec![Subtree::Leaf(format!("c_{}_{}", k, i).into_bytes())])
                    };
                    log.append_subtree(&subtree).await.unwrap();
                    subtrees.push(subtree);
                }

                let root = log.root();

                // Verify consistency proof for every valid old size
                for old_size in 1..size {
                    let cons_proof = log
                        .consistency_proof(old_size, size)
                        .await
                        .unwrap()
                        .unwrap();

                    let old_root = {
                        let mut temp_log = NaryMerkleLog::new(
                            MemoryStorage::new(),
                            Box::new(Sha256Hasher),
                            TreeConfig { log_arity: k },
                        )
                        .await
                        .unwrap();
                        for i in 0..old_size {
                            temp_log
                                .append_subtree(&subtrees[i as usize])
                                .await
                                .unwrap();
                        }
                        temp_log.root()
                    };
                    assert!(
                        neml::verify_consistency(
                            &Sha256Hasher,
                            old_size,
                            size,
                            k as u64,
                            &cons_proof.start_hash,
                            &cons_proof.path,
                            &old_root,
                            &root,
                        ),
                        "verify_consistency failed for subtree log: k={}, size={}, old_size={}",
                        k,
                        size,
                        old_size
                    );
                }
            }
        }
    });
}

#[test]
fn test_deep_subtree_inclusion_proofs() {
    smol::block_on(async {
        // Helper to generate nested structure
        fn make_nested_subtree(depth: usize, data: &[u8]) -> Subtree {
            let mut current = Subtree::Leaf(data.to_vec());
            for _ in 0..depth {
                current = Subtree::Node(vec![current]);
            }
            current
        }

        // 1. Verify single leaf at depths 1 to 5
        for depth in 1..=5 {
            let storage = MemoryStorage::new();
            let mut log =
                NaryMerkleLog::new(storage, Box::new(Sha256Hasher), TreeConfig { log_arity: 2 })
                    .await
                    .unwrap();

            let data = format!("depth_{}", depth).into_bytes();
            let subtree = make_nested_subtree(depth, &data);
            log.append_subtree(&subtree).await.unwrap();

            let root = log.root();
            let mut path = neml::within_subtree_path(&Sha256Hasher, &subtree, 0).unwrap();
            let log_proof = log.inclusion_proof(0, 1).await.unwrap().unwrap();
            path.extend(log_proof.path);

            let full_proof = neml::InclusionProof {
                path,
            };

            assert!(
                neml::verify_inclusion(
                    &Sha256Hasher,
                    &Sha256Hasher.leaf(&data),
                    0,
                    1,
                    2,
                    &full_proof.path,
                    &root
                ),
                "Failed single nested leaf inclusion proof verification at depth {}",
                depth
            );
        }

        // 2. Verify multiple leaves at mixed depths
        // Structure:
        //       Node
        //      /    \
        //   Node     c (depth 1)
        //   /  \
        //  a    Node (depth 3)
        //       |
        //      Node
        //       |
        //       b
        let a_data = b"a_nested".to_vec();
        let b_data = b"b_nested".to_vec();
        let c_data = b"c_nested".to_vec();

        let branch_left = Subtree::Node(vec![
            Subtree::Leaf(a_data.clone()),
            Subtree::Node(vec![Subtree::Node(vec![Subtree::Leaf(b_data.clone())])]),
        ]);
        let subtree = Subtree::Node(vec![branch_left, Subtree::Leaf(c_data.clone())]);

        let storage = MemoryStorage::new();
        let mut log =
            NaryMerkleLog::new(storage, Box::new(Sha256Hasher), TreeConfig { log_arity: 3 })
                .await
                .unwrap();
        log.append_subtree(&subtree).await.unwrap();
        log.append_subtree(&Subtree::Node(vec![Subtree::Leaf(b"other_leaf".to_vec())]))
            .await
            .unwrap();

        let root = log.root();

        let test_cases = vec![(0, a_data), (1, b_data), (2, c_data)];

        for (leaf_idx, data) in test_cases {
            let mut path = neml::within_subtree_path(&Sha256Hasher, &subtree, leaf_idx).unwrap();
            let log_proof = log.inclusion_proof(0, 2).await.unwrap().unwrap();
            path.extend(log_proof.path);

            let full_proof = neml::InclusionProof {
                path,
            };

            assert!(
                neml::verify_inclusion(
                    &Sha256Hasher,
                    &Sha256Hasher.leaf(&data),
                    0,
                    2,
                    3,
                    &full_proof.path,
                    &root
                ),
                "Failed nested mixed leaf inclusion proof verification for index {}",
                leaf_idx
            );
        }
    });
}

#[test]
fn test_subtree_appends_k3_k4() {
    smol::block_on(async {
        let hasher = Sha256Hasher;

        // k=3 test
        {
            let storage = MemoryStorage::new();
            let mut log =
                NaryMerkleLog::new(storage, Box::new(Sha256Hasher), TreeConfig { log_arity: 3 })
                    .await
                    .unwrap();

            let s0 = Subtree::Node(vec![
                Subtree::Leaf(b"a".to_vec()),
                Subtree::Leaf(b"b".to_vec()),
            ]);
            let s1 = Subtree::Leaf(b"c".to_vec());
            let s2 = Subtree::Node(vec![
                Subtree::Leaf(b"d".to_vec()),
                Subtree::Leaf(b"e".to_vec()),
                Subtree::Leaf(b"f".to_vec()),
            ]);

            log.append_subtree(&s0).await.unwrap();
            log.append_subtree(&s1).await.unwrap();
            log.append_subtree(&s2).await.unwrap();

            let root = log.root();

            let h0 = neml::evaluate(&hasher, &s0);
            let h1 = neml::evaluate(&hasher, &s1);
            let h2 = neml::evaluate(&hasher, &s2);

            let expected = hasher.node(&[&h0, &h1, &h2]);
            assert_eq!(root, expected, "Root mismatch for k=3 subtree appends");
        }

        // k=4 test
        {
            let storage = MemoryStorage::new();
            let mut log =
                NaryMerkleLog::new(storage, Box::new(Sha256Hasher), TreeConfig { log_arity: 4 })
                    .await
                    .unwrap();

            let s0 = Subtree::Leaf(b"a".to_vec());
            let s1 = Subtree::Leaf(b"b".to_vec());
            let s2 = Subtree::Leaf(b"c".to_vec());
            let s3 = Subtree::Leaf(b"d".to_vec());

            log.append_subtree(&s0).await.unwrap();
            log.append_subtree(&s1).await.unwrap();
            log.append_subtree(&s2).await.unwrap();
            log.append_subtree(&s3).await.unwrap();

            let root = log.root();

            let h0 = neml::evaluate(&hasher, &s0);
            let h1 = neml::evaluate(&hasher, &s1);
            let h2 = neml::evaluate(&hasher, &s2);
            let h3 = neml::evaluate(&hasher, &s3);

            let expected = hasher.node(&[&h0, &h1, &h2, &h3]);
            assert_eq!(root, expected, "Root mismatch for k=4 subtree appends");
        }
    });
}

#[test]
fn test_epoch_resume_subtree_gaps() {
    smol::block_on(async {
        let storage = MemoryStorage::new();
        let config = TreeConfig { log_arity: 2 };
        let mut log = NaryMerkleLog::new(storage, Box::new(Sha256Hasher), config)
            .await
            .unwrap();

        // 1. Initial subtrees while both algorithms active
        log.add_algorithm(1, Box::new(Sha256Hasher)).await.unwrap();

        let s0 = Subtree::Node(vec![
            Subtree::Leaf(b"a".to_vec()),
            Subtree::Leaf(b"b".to_vec()),
        ]);
        log.append_subtree(&s0).await.unwrap();

        // 2. Remove algorithm 0
        log.remove_algorithm(0).await.unwrap();

        // 3. Append subtree (gap for algorithm 0)
        let s1 = Subtree::Leaf(b"c".to_vec());
        log.append_subtree(&s1).await.unwrap();

        // 4. Resume algorithm 0
        log.resume_algorithm(0).await.unwrap();

        // 5. Append more subtrees
        let s2 = Subtree::Node(vec![Subtree::Leaf(b"d".to_vec())]);
        log.append_subtree(&s2).await.unwrap();

        let root0 = log.root_for(0).unwrap();
        let root1 = log.root_for(1).unwrap();

        // 6. Reconstruct from storage and verify roots match
        let storage = log.into_storage();
        let reconstructed = NaryMerkleLog::from_storage(
            storage,
            vec![(0, Box::new(Sha256Hasher)), (1, Box::new(Sha256Hasher))],
        )
        .await
        .unwrap();

        assert_eq!(reconstructed.root_for(0).unwrap(), root0);
        assert_eq!(reconstructed.root_for(1).unwrap(), root1);
    });
}

#[test]
fn test_multi_algorithm_subtree_proofs() {
    smol::block_on(async {
        let storage = MemoryStorage::new();
        let config = TreeConfig { log_arity: 2 };
        let mut log = NaryMerkleLog::new(storage, Box::new(Sha256Hasher), config)
            .await
            .unwrap();
        log.add_algorithm(1, Box::new(Sha256Hasher)).await.unwrap();

        let s0 = Subtree::Node(vec![
            Subtree::Leaf(b"a".to_vec()),
            Subtree::Leaf(b"b".to_vec()),
        ]);
        let s1 = Subtree::Leaf(b"c".to_vec());

        log.append_subtree(&s0).await.unwrap();

        // Remove algorithm 1 (creates a gap/inactive range)
        log.remove_algorithm(1).await.unwrap();

        log.append_subtree(&s1).await.unwrap();

        let root0 = log.root_for(0).unwrap();
        let root1 = log.root_for(1).unwrap(); // frozen at size 1

        // 1. Verify inclusion proof for Algorithm 0 (fully active)
        let mut path0 = neml::within_subtree_path(&Sha256Hasher, &s1, 0).unwrap();
        let log_proof0 = log.inclusion_proof_for(0, 1, 2).await.unwrap().unwrap();
        path0.extend(log_proof0.path);

        let full_proof0 = neml::InclusionProof {
            path: path0,
        };
        assert!(neml::verify_inclusion(
            &Sha256Hasher,
            &Sha256Hasher.leaf(b"c"),
            1,
            2,
            2,
            &full_proof0.path,
            &root0
        ));

        // 2. Verify inclusion proof for Algorithm 1 (frozen at size 1)
        assert!(log.inclusion_proof_for(1, 1, 2).await.unwrap().is_none());

        let mut path1 = neml::within_subtree_path(&Sha256Hasher, &s0, 1).unwrap();
        let log_proof1 = log.inclusion_proof_for(1, 0, 1).await.unwrap().unwrap();
        path1.extend(log_proof1.path);

        let full_proof1 = neml::InclusionProof {
            path: path1,
        };
        assert!(neml::verify_inclusion(
            &Sha256Hasher,
            &Sha256Hasher.leaf(b"b"),
            0,
            1,
            2,
            &full_proof1.path,
            &root1
        ));

        // 3. Consistency proofs
        let cons0 = log.consistency_proof_for(0, 1, 2).await.unwrap().unwrap();
        let old_root0 = {
            let mut temp_log = NaryMerkleLog::new(
                MemoryStorage::new(),
                Box::new(Sha256Hasher),
                TreeConfig { log_arity: 2 },
            )
            .await
            .unwrap();
            temp_log.append_subtree(&s0).await.unwrap();
            temp_log.root_for(0).unwrap()
        };
        assert!(neml::verify_consistency(
            &Sha256Hasher,
            1,
            2,
            2,
            &cons0.start_hash,
            &cons0.path,
            &old_root0,
            &root0
        ));

        assert!(log.consistency_proof_for(1, 1, 2).await.unwrap().is_none());
    });
}

#[test]
fn test_proof_error_edge_cases() {
    smol::block_on(async {
        let storage = MemoryStorage::new();
        let config = TreeConfig { log_arity: 2 };
        let mut log = NaryMerkleLog::new(storage, Box::new(Sha256Hasher), config)
            .await
            .unwrap();

        // 1. Empty tree proof generation
        assert!(log.inclusion_proof(0, 0).await.unwrap().is_none());
        assert!(log.inclusion_proof(0, 1).await.unwrap().is_none());
        assert!(log.consistency_proof(0, 0).await.unwrap().is_none());
        assert!(log.consistency_proof(0, 1).await.unwrap().is_none());

        // Append one leaf to make it size 1
        log.append_leaf(b"hello").await.unwrap();

        // 2. OOB/invalid index queries
        assert!(log.inclusion_proof(1, 1).await.unwrap().is_none());
        assert!(log.inclusion_proof(0, 2).await.unwrap().is_none());
        assert!(log.consistency_proof(1, 1).await.unwrap().is_none());
        assert!(log.consistency_proof(2, 1).await.unwrap().is_none());
        assert!(log.consistency_proof(0, 1).await.unwrap().is_none());

        // 3. within_subtree_path edge cases
        let leaf_subtree = Subtree::Leaf(b"x".to_vec());
        assert!(neml::within_subtree_path(&Sha256Hasher, &leaf_subtree, 0).is_some());
        assert!(neml::within_subtree_path(&Sha256Hasher, &leaf_subtree, 1).is_none());

        let node_subtree = Subtree::Node(vec![
            Subtree::Leaf(b"a".to_vec()),
            Subtree::Leaf(b"b".to_vec()),
        ]);
        assert!(neml::within_subtree_path(&Sha256Hasher, &node_subtree, 1).is_some());
        assert!(neml::within_subtree_path(&Sha256Hasher, &node_subtree, 2).is_none());

        // 4. Verifier input validation failures
        let empty_proof = neml::InclusionProof {
            path: Vec::new(),
        };
        assert!(!neml::verify_inclusion(
            &Sha256Hasher,
            &Sha256Hasher.leaf(b"x"),
            1,
            1,
            2,
            &empty_proof.path,
            &[0; 32]
        ));

        let empty_cons_proof = neml::ConsistencyProof {
            start_hash: vec![0; 32],
            path: Vec::new(),
        };
        assert!(!neml::verify_consistency(
            &Sha256Hasher,
            0,
            2,
            2,
            &empty_cons_proof.start_hash,
            &empty_cons_proof.path,
            &[0; 32],
            &[0; 32]
        ));

        let empty_cons_proof_invalid_sizes = neml::ConsistencyProof {
            start_hash: vec![0; 32],
            path: Vec::new(),
        };
        assert!(!neml::verify_consistency(
            &Sha256Hasher,
            2,
            2,
            2,
            &empty_cons_proof_invalid_sizes.start_hash,
            &empty_cons_proof_invalid_sizes.path,
            &[0; 32],
            &[0; 32]
        ));

        let empty_cons_proof_invalid_arity = neml::ConsistencyProof {
            start_hash: vec![0; 32],
            path: Vec::new(),
        };
        assert!(!neml::verify_consistency(
            &Sha256Hasher,
            1,
            2,
            1,
            &empty_cons_proof_invalid_arity.start_hash,
            &empty_cons_proof_invalid_arity.path,
            &[0; 32],
            &[0; 32]
        ));
    });
}

#[test]
fn test_power_of_k_boundaries() {
    smol::block_on(async {
        // k=3: sizes 3, 9, 27
        {
            let storage = MemoryStorage::new();
            let config = TreeConfig { log_arity: 3 };
            let mut log = NaryMerkleLog::new(storage, Box::new(Sha256Hasher), config)
                .await
                .unwrap();

            let mut leaves = Vec::new();
            for i in 0..27 {
                let data = format!("leaf_3_{}", i).into_bytes();
                log.append_leaf(&data).await.unwrap();
                leaves.push(Sha256Hasher.leaf(&data));
            }

            let boundary_sizes = vec![3, 9, 27];
            for &size in &boundary_sizes {
                let root = {
                    let mut temp_log = NaryMerkleLog::new(
                        MemoryStorage::new(),
                        Box::new(Sha256Hasher),
                        TreeConfig { log_arity: 3 },
                    )
                    .await
                    .unwrap();
                    for i in 0..size {
                        temp_log
                            .append_leaf(&format!("leaf_3_{}", i).into_bytes())
                            .await
                            .unwrap();
                    }
                    temp_log.root()
                };

                for idx in 0..size {
                    let proof = log.inclusion_proof(idx, size).await.unwrap().unwrap();
                    assert!(neml::verify_inclusion(
                        &Sha256Hasher,
                        &leaves[idx as usize],
                        idx,
                        size,
                        3,
                        &proof.path,
                        &root
                    ));
                }
            }

            let proof_3_9 = log.consistency_proof(3, 9).await.unwrap().unwrap();
            let root_3 = {
                let mut temp_log = NaryMerkleLog::new(
                    MemoryStorage::new(),
                    Box::new(Sha256Hasher),
                    TreeConfig { log_arity: 3 },
                )
                .await
                .unwrap();
                for i in 0..3 {
                    temp_log
                        .append_leaf(&format!("leaf_3_{}", i).into_bytes())
                        .await
                        .unwrap();
                }
                temp_log.root()
            };
            let root_9 = {
                let mut temp_log = NaryMerkleLog::new(
                    MemoryStorage::new(),
                    Box::new(Sha256Hasher),
                    TreeConfig { log_arity: 3 },
                )
                .await
                .unwrap();
                for i in 0..9 {
                    temp_log
                        .append_leaf(&format!("leaf_3_{}", i).into_bytes())
                        .await
                        .unwrap();
                }
                temp_log.root()
            };
            assert!(neml::verify_consistency(
                &Sha256Hasher,
                3,
                9,
                3,
                &proof_3_9.start_hash,
                &proof_3_9.path,
                &root_3,
                &root_9
            ));

            let proof_9_27 = log.consistency_proof(9, 27).await.unwrap().unwrap();
            let root_27 = log.root();
            assert!(neml::verify_consistency(
                &Sha256Hasher,
                9,
                27,
                3,
                &proof_9_27.start_hash,
                &proof_9_27.path,
                &root_9,
                &root_27
            ));
        }

        // k=4: sizes 4, 16, 64
        {
            let storage = MemoryStorage::new();
            let config = TreeConfig { log_arity: 4 };
            let mut log = NaryMerkleLog::new(storage, Box::new(Sha256Hasher), config)
                .await
                .unwrap();

            let mut leaves = Vec::new();
            for i in 0..64 {
                let data = format!("leaf_4_{}", i).into_bytes();
                log.append_leaf(&data).await.unwrap();
                leaves.push(Sha256Hasher.leaf(&data));
            }

            let boundary_sizes = vec![4, 16, 64];
            for &size in &boundary_sizes {
                let root = {
                    let mut temp_log = NaryMerkleLog::new(
                        MemoryStorage::new(),
                        Box::new(Sha256Hasher),
                        TreeConfig { log_arity: 4 },
                    )
                    .await
                    .unwrap();
                    for i in 0..size {
                        temp_log
                            .append_leaf(&format!("leaf_4_{}", i).into_bytes())
                            .await
                            .unwrap();
                    }
                    temp_log.root()
                };

                for idx in 0..size {
                    let proof = log.inclusion_proof(idx, size).await.unwrap().unwrap();
                    assert!(neml::verify_inclusion(
                        &Sha256Hasher,
                        &leaves[idx as usize],
                        idx,
                        size,
                        4,
                        &proof.path,
                        &root
                    ));
                }
            }

            let proof_4_16 = log.consistency_proof(4, 16).await.unwrap().unwrap();
            let root_4 = {
                let mut temp_log = NaryMerkleLog::new(
                    MemoryStorage::new(),
                    Box::new(Sha256Hasher),
                    TreeConfig { log_arity: 4 },
                )
                .await
                .unwrap();
                for i in 0..4 {
                    temp_log
                        .append_leaf(&format!("leaf_4_{}", i).into_bytes())
                        .await
                        .unwrap();
                }
                temp_log.root()
            };
            let root_16 = {
                let mut temp_log = NaryMerkleLog::new(
                    MemoryStorage::new(),
                    Box::new(Sha256Hasher),
                    TreeConfig { log_arity: 4 },
                )
                .await
                .unwrap();
                for i in 0..16 {
                    temp_log
                        .append_leaf(&format!("leaf_4_{}", i).into_bytes())
                        .await
                        .unwrap();
                }
                temp_log.root()
            };
            assert!(neml::verify_consistency(
                &Sha256Hasher,
                4,
                16,
                4,
                &proof_4_16.start_hash,
                &proof_4_16.path,
                &root_4,
                &root_16
            ));

            let proof_16_64 = log.consistency_proof(16, 64).await.unwrap().unwrap();
            let root_64 = log.root();
            assert!(neml::verify_consistency(
                &Sha256Hasher,
                16,
                64,
                4,
                &proof_16_64.start_hash,
                &proof_16_64.path,
                &root_16,
                &root_64
            ));
        }
    });
}

#[test]
fn test_combined_root_single_alg_commits_epochs() {
    smol::block_on(async {
        let hasher = Sha256Hasher;
        let storage = MemoryStorage::new();
        let config = TreeConfig { log_arity: 2 };
        let mut log = NaryMerkleLog::new(storage, Box::new(hasher), config)
            .await
            .unwrap();

        log.append_leaf(b"test").await.unwrap();
        let raw_root = log.root();

        // Genesis state: sole registry algorithm, default timeline [(0, MAX)].
        // The metaroot promotes to the raw root — hashing would add no
        // information (same discipline as singleton node promotion).
        let comb_root = log.combined_root().await;
        assert_eq!(comb_root, raw_root);

        // Adding a second algorithm breaks the registry singleton, so the
        // combined root permanently switches to the hashed form — even
        // retroactively for historical sizes where alg 1 was not yet active.
        log.add_algorithm(1, Box::new(Sha256Hasher)).await.unwrap();

        let raw_root_at_1 = log.root_for_at(0, 1).await.unwrap();
        let comb_root_at_1 = log.combined_root_at(0, 1).await.unwrap();
        assert_ne!(comb_root_at_1, raw_root_at_1);

        // Alg 1's epoch [(1, MAX)] appears in committed_epochs_at(1) even
        // though alg 1 was not active at position 0.
        let expected = Sha256Hasher.hash(&neml::combined_root_preimage(
            &[(0, raw_root_at_1)],
            &[(0, vec![(0u64, u64::MAX)]), (1, vec![(1u64, u64::MAX)])],
        ));
        assert_eq!(comb_root_at_1, expected);
    });
}

#[test]
fn test_combined_root_multi_alg() {
    smol::block_on(async {
        let hasher = Sha256Hasher;
        let storage = MemoryStorage::new();
        let config = TreeConfig { log_arity: 2 };
        let mut log = NaryMerkleLog::new(storage, Box::new(hasher), config)
            .await
            .unwrap();

        log.add_algorithm(1, Box::new(Sha256Hasher)).await.unwrap();
        log.append_leaf(b"data").await.unwrap();

        // Retrieve raw roots
        let root_0 = log.root_for_at(0, 1).await.unwrap();
        let root_1 = log.root_for_at(1, 1).await.unwrap();

        // Reconstruct combined root manually from the canonical snapshot
        // serialization: sorted active roots plus the epoch timeline.
        let buf = neml::combined_root_preimage(
            &[(0, root_0), (1, root_1)],
            &[(0, vec![(0, u64::MAX)]), (1, vec![(0, u64::MAX)])],
        );
        let expected_combined = Sha256Hasher.hash(&buf);

        let comb_root = log.combined_root_for(0).await.unwrap();
        assert_eq!(comb_root, expected_combined);
    });
}

#[test]
fn test_combined_root_historical_and_epochs() {
    smol::block_on(async {
        let hasher = Sha256Hasher;
        let storage = MemoryStorage::new();
        let config = TreeConfig { log_arity: 2 };
        let mut log = NaryMerkleLog::new(storage, Box::new(hasher), config)
            .await
            .unwrap();

        log.append_leaf(b"a").await.unwrap(); // size 1: alg 0 active

        log.add_algorithm(1, Box::new(Sha256Hasher)).await.unwrap(); // size 1: alg 0, 1 active
        log.append_leaf(b"b").await.unwrap(); // size 2

        log.remove_algorithm(1).await.unwrap(); // size 2: alg 0 active (alg 1 frozen)
        log.append_leaf(b"c").await.unwrap(); // size 3

        // Historical combined root at size 1: only alg 0 active. Alg 1's
        // interval (1, 2) extends past size 1, so it is committed as open.
        let comb_1 = log.combined_root_at(0, 1).await.unwrap();
        let raw_0_at_1 = log.root_for_at(0, 1).await.unwrap();
        assert_ne!(comb_1, raw_0_at_1);
        let expected_1 = Sha256Hasher.hash(&neml::combined_root_preimage(
            &[(0, raw_0_at_1)],
            &[(0, vec![(0, u64::MAX)]), (1, vec![(1, u64::MAX)])],
        ));
        assert_eq!(comb_1, expected_1);

        // Historical combined root at size 2: alg 0 and 1 active. Alg 1's
        // interval is closed at 2 by the later deactivation.
        let comb_2 = log.combined_root_at(0, 2).await.unwrap();
        assert_ne!(comb_2, log.root_for_at(0, 2).await.unwrap());
        let expected_2 = Sha256Hasher.hash(&neml::combined_root_preimage(
            &[
                (0, log.root_for_at(0, 2).await.unwrap()),
                (1, log.root_for_at(1, 2).await.unwrap()),
            ],
            &[(0, vec![(0, u64::MAX)]), (1, vec![(1, 2)])],
        ));
        assert_eq!(comb_2, expected_2);

        // Historical combined root at size 3: alg 1 is frozen — its root is
        // omitted but its closed timeline stays committed.
        let comb_3 = log.combined_root_at(0, 3).await.unwrap();
        let raw_0_at_3 = log.root_for_at(0, 3).await.unwrap();
        assert_ne!(comb_3, raw_0_at_3);
        let expected_3 = Sha256Hasher.hash(&neml::combined_root_preimage(
            &[(0, raw_0_at_3)],
            &[(0, vec![(0, u64::MAX)]), (1, vec![(1, 2)])],
        ));
        assert_eq!(comb_3, expected_3);
    });
}

#[test]
fn test_coupling_proof_verify_validation() {
    let hasher = Sha256Hasher;
    let raw_root_0 = vec![0; 32];
    let raw_root_1 = vec![1; 32];
    let tree_size = 4u64;
    let epochs = vec![(0u64, vec![(0u64, u64::MAX)]), (1, vec![(0, u64::MAX)])];

    let proof = neml::CouplingProof {
        active_roots: vec![(0, raw_root_0.clone()), (1, raw_root_1.clone())],
        alg_epochs: epochs.clone(),
    };

    // Correct Combined Root computation
    let combined_root = hasher.hash(&neml::combined_root_preimage(
        &proof.active_roots,
        &proof.alg_epochs,
    ));

    let config = neml::VerifierConfig::default();

    // 1. Success case
    let target = proof.verify(&hasher, 0, tree_size, &combined_root, &[0, 1], config);
    assert_eq!(target.unwrap(), raw_root_0);

    // 2. Reject because of maximum active algorithms limit
    let strict_config = neml::VerifierConfig {
        max_active_algorithms: 1,
        ..Default::default()
    };
    let target_dos = proof.verify(&hasher, 0, tree_size, &combined_root, &[0, 1], strict_config);
    assert!(target_dos.is_none());

    // 3. Reject unsorted algorithm IDs
    let unsorted_proof = neml::CouplingProof {
        active_roots: vec![(1, raw_root_1.clone()), (0, raw_root_0.clone())],
        alg_epochs: epochs.clone(),
    };
    assert!(
        unsorted_proof
            .verify(&hasher, 0, tree_size, &combined_root, &[0, 1], config)
            .is_none()
    );

    // 4. Reject duplicate algorithm IDs
    let duplicate_proof = neml::CouplingProof {
        active_roots: vec![(0, raw_root_0.clone()), (0, raw_root_1.clone())],
        alg_epochs: epochs.clone(),
    };
    assert!(
        duplicate_proof
            .verify(&hasher, 0, tree_size, &combined_root, &[0, 1], config)
            .is_none()
    );

    // 5. TAMPERED DATA REJECTION (Collision Resistance / Cryptographic Soundness)
    // Modify one byte in raw_root_0
    let mut bad_root_0 = raw_root_0.clone();
    bad_root_0[0] ^= 0xFF;
    let tampered_proof = neml::CouplingProof {
        active_roots: vec![(0, bad_root_0), (1, raw_root_1.clone())],
        alg_epochs: epochs.clone(),
    };
    assert!(
        tampered_proof
            .verify(&hasher, 0, tree_size, &combined_root, &[0, 1], config)
            .is_none()
    );

    // Modify combined root itself
    let mut bad_combined = combined_root.clone();
    bad_combined[0] ^= 0xFF;
    assert!(
        proof
            .verify(&hasher, 0, tree_size, &bad_combined, &[0, 1], config)
            .is_none()
    );

    // 6. SPLIT-HORIZON PREVENTION REJECTION
    // Expected algorithms has different IDs
    assert!(
        proof
            .verify(&hasher, 0, tree_size, &combined_root, &[0, 2], config)
            .is_none()
    );
    // Expected algorithms is shorter (missing expected alg 1)
    assert!(
        proof
            .verify(&hasher, 0, tree_size, &combined_root, &[0], config)
            .is_none()
    );
    // Expected algorithms is longer (extra expected alg)
    assert!(
        proof
            .verify(&hasher, 0, tree_size, &combined_root, &[0, 1, 2], config)
            .is_none()
    );

    // 7. TARGET ALGORITHM MISSING FROM PROOF
    // Requesting target_alg_id = 2, which is not in active_roots
    assert!(
        proof
            .verify(&hasher, 2, tree_size, &combined_root, &[0, 1], config)
            .is_none()
    );

    // 8. UNSORTED EXPECTED ACTIVE ALGORITHMS
    assert!(
        proof
            .verify(&hasher, 0, tree_size, &combined_root, &[1, 0], config)
            .is_none()
    );

    // 9. DUPLICATE EXPECTED ACTIVE ALGORITHMS
    assert!(
        proof
            .verify(&hasher, 0, tree_size, &combined_root, &[0, 0], config)
            .is_none()
    );

    // 10. EMPTY INPUTS HANDLING
    let empty_proof = neml::CouplingProof {
        active_roots: vec![],
        alg_epochs: vec![],
    };
    assert!(
        empty_proof
            .verify(&hasher, 0, tree_size, &combined_root, &[0, 1], config)
            .is_none()
    );
    assert!(
        proof
            .verify(&hasher, 0, tree_size, &combined_root, &[], config)
            .is_none()
    );

    // 11. SUBSTITUTED EPOCH METADATA REJECTION (Design A+)
    // Shifting an activation boundary must break the combined-root binding:
    // the timeline is inside the hash coverage, so the substituted proof
    // cannot verify against the honest root.
    let substituted_epochs_proof = neml::CouplingProof {
        active_roots: vec![(0, raw_root_0.clone()), (1, raw_root_1.clone())],
        alg_epochs: vec![(0, vec![(0, u64::MAX)]), (1, vec![(2, u64::MAX)])],
    };
    assert!(
        substituted_epochs_proof
            .verify(&hasher, 0, tree_size, &combined_root, &[0, 1], config)
            .is_none()
    );

    // 12. EPOCH / ACTIVE-SET CONSISTENCY REJECTION
    // A timeline that does not cover the final position for a claimed active
    // algorithm is rejected before any hashing.
    let inconsistent_proof = neml::CouplingProof {
        active_roots: vec![(0, raw_root_0.clone()), (1, raw_root_1.clone())],
        alg_epochs: vec![(0, vec![(0, u64::MAX)]), (1, vec![(0, 2)])],
    };
    let inconsistent_root = hasher.hash(&neml::combined_root_preimage(
        &inconsistent_proof.active_roots,
        &inconsistent_proof.alg_epochs,
    ));
    assert!(
        inconsistent_proof
            .verify(&hasher, 0, tree_size, &inconsistent_root, &[0, 1], config)
            .is_none()
    );

    // 13. ILL-FORMED EPOCHS REJECTION (overlapping intervals)
    let ill_formed_proof = neml::CouplingProof {
        active_roots: vec![(0, raw_root_0.clone()), (1, raw_root_1.clone())],
        alg_epochs: vec![(0, vec![(0, 3), (2, u64::MAX)]), (1, vec![(0, u64::MAX)])],
    };
    let ill_formed_root = hasher.hash(&neml::combined_root_preimage(
        &ill_formed_proof.active_roots,
        &ill_formed_proof.alg_epochs,
    ));
    assert!(
        ill_formed_proof
            .verify(&hasher, 0, tree_size, &ill_formed_root, &[0, 1], config)
            .is_none()
    );

    // 14. SIZE-ZERO REJECTION (nothing is committed at size zero)
    assert!(
        proof
            .verify(&hasher, 0, 0, &combined_root, &[0, 1], config)
            .is_none()
    );

    // 15. VARIABLE LENGTH ROOTS (Length-Ambiguity Check)
    let var_root_0 = vec![9; 20]; // 20-byte root (e.g. RIPEMD-160)
    let var_root_1 = vec![5; 32]; // 32-byte root (e.g. SHA-256)
    let var_proof = neml::CouplingProof {
        active_roots: vec![(0, var_root_0.clone()), (1, var_root_1.clone())],
        alg_epochs: epochs.clone(),
    };
    let var_combined = hasher.hash(&neml::combined_root_preimage(
        &var_proof.active_roots,
        &var_proof.alg_epochs,
    ));

    let target_var = var_proof.verify(&hasher, 0, tree_size, &var_combined, &[0, 1], config);
    assert_eq!(target_var.unwrap(), var_root_0);

    // 16. EMPTY ROOTS HANDLING
    let empty_root_proof = neml::CouplingProof {
        active_roots: vec![(0, vec![]), (1, var_root_1.clone())],
        alg_epochs: epochs.clone(),
    };
    let empty_combined = hasher.hash(&neml::combined_root_preimage(
        &empty_root_proof.active_roots,
        &empty_root_proof.alg_epochs,
    ));

    let target_empty =
        empty_root_proof.verify(&hasher, 0, tree_size, &empty_combined, &[0, 1], config);
    assert_eq!(target_empty.unwrap(), Vec::<u8>::new());
}

#[test]
fn test_verify_inclusion_with_coupling() {
    smol::block_on(async {
        let hasher = Sha256Hasher;
        let storage = MemoryStorage::new();
        let config = TreeConfig { log_arity: 2 };
        let mut log = NaryMerkleLog::new(storage, Box::new(hasher), config)
            .await
            .unwrap();

        log.append_leaf(b"test").await.unwrap();

        let raw_root = log.root();
        let combined_root = log.combined_root().await;
        let inclusion_proof = log.inclusion_proof(0, 1).await.unwrap().unwrap();
        let coupling_proof = neml::CouplingProof {
            active_roots: vec![(0, raw_root.clone())],
            alg_epochs: log.committed_epochs_at(1),
        };

        let verifier_config = neml::VerifierConfig::default();
        let ok = neml::verify_inclusion_with_coupling(
            &Sha256Hasher,
            0,
            &Sha256Hasher.leaf(b"test"),
            0,
            1,
            2,
            &inclusion_proof.path,
            &coupling_proof,
            &combined_root,
            &[0],
            verifier_config,
        );
        assert!(ok);
    });
}

#[test]
fn test_verify_non_divergence() {
    smol::block_on(async {
        let hasher = Sha256Hasher;
        let storage = MemoryStorage::new();
        let config = TreeConfig { log_arity: 2 };
        let mut log = NaryMerkleLog::new(storage, Box::new(hasher), config)
            .await
            .unwrap();

        log.append_leaf(b"a").await.unwrap();
        let root_0 = log.root();

        // 1. Success verification from 0 to 1
        let ok = log.verify_non_divergence(None, &[]).await.unwrap();
        assert!(ok);

        // 2. Success verification starting from checkpoint size 1
        let ok_checkpoint = log
            .verify_non_divergence(Some(1), &[(0, root_0)])
            .await
            .unwrap();
        assert!(ok_checkpoint);

        // 3. Failure verification: passing a mismatching trusted root
        let bad_root = vec![0x99; 32];
        let ok_bad_checkpoint = log
            .verify_non_divergence(Some(1), &[(0, bad_root)])
            .await
            .unwrap();
        assert!(!ok_bad_checkpoint);
    });
}

#[test]
fn test_combined_root_size_0() {
    smol::block_on(async {
        let hasher = Sha256Hasher;
        let storage = MemoryStorage::new();
        let config = TreeConfig { log_arity: 2 };
        let log = NaryMerkleLog::new(storage, Box::new(hasher), config)
            .await
            .unwrap();

        // Size 0 combined root query should return the empty hash
        let root_at_0 = log.combined_root_at(0, 0).await.unwrap();
        assert_eq!(root_at_0, Sha256Hasher.empty());
    });
}

#[test]
fn test_verify_consistency_with_coupling() {
    smol::block_on(async {
        let hasher = Sha256Hasher;
        let storage = MemoryStorage::new();
        let config = TreeConfig { log_arity: 2 };
        let mut log = NaryMerkleLog::new(storage, Box::new(hasher), config)
            .await
            .unwrap();

        log.append_leaf(b"a").await.unwrap();
        let root_a = log.root();
        let coupling_a = neml::CouplingProof {
            active_roots: vec![(0, root_a.clone())],
            alg_epochs: log.committed_epochs_at(1),
        };

        log.append_leaf(b"b").await.unwrap();
        let root_b = log.root();
        let coupling_b = neml::CouplingProof {
            active_roots: vec![(0, root_b.clone())],
            alg_epochs: log.committed_epochs_at(2),
        };

        let combined_a = log.combined_root_at(0, 1).await.unwrap();
        let combined_b = log.combined_root_at(0, 2).await.unwrap();

        let consistency_proof = log.consistency_proof(1, 2).await.unwrap().unwrap();

        let verifier_config = neml::VerifierConfig::default();
        let ok = neml::verify_consistency_with_coupling(
            &Sha256Hasher,
            0,
            1,
            2,
            2,
            &consistency_proof.start_hash,
            &consistency_proof.path,
            &coupling_a,
            &coupling_b,
            &combined_a,
            &combined_b,
            &[0],
            &[0],
            verifier_config,
        );
        assert!(ok);
    });
}

#[test]
fn test_consistency_proof_overflow_panic() {
    let proof = neml::ConsistencyProof {
        start_hash: vec![0; 32],
        path: vec![
            neml::ProofStep {
                siblings: vec![vec![0; 32]; 4],
                position: 4,
            };
            62
        ],
    };
    let ok = neml::verify_consistency(&Sha256Hasher, 1, 1 << 62, 2, &proof.start_hash, &proof.path, &[0; 32], &[0; 32]);
    assert!(!ok);
}

#[test]
fn test_consistency_proof_huge_siblings_dos() {
    let proof = neml::ConsistencyProof {
        start_hash: vec![0; 32],
        path: vec![
            neml::ProofStep {
                siblings: vec![vec![0; 32]; 100_000],
                position: 0,
            };
            1
        ],
    };
    let ok = neml::verify_consistency(&Sha256Hasher, 1, 2, 2, &proof.start_hash, &proof.path, &[0; 32], &[0; 32]);
    assert!(!ok);

    // Path length > 256
    let proof_huge_path = neml::ConsistencyProof {
        start_hash: vec![0; 32],
        path: vec![
            neml::ProofStep {
                siblings: vec![vec![0; 32]],
                position: 0,
            };
            257
        ],
    };
    let ok = neml::verify_consistency(&Sha256Hasher, 1, 2, 2, &proof_huge_path.start_hash, &proof_huge_path.path, &[0; 32], &[0; 32]);
    assert!(!ok);

    // Invalid log arity < 2 (e.g. 1)
    let proof_invalid_arity_low = neml::ConsistencyProof {
        start_hash: vec![0; 32],
        path: Vec::new(),
    };
    let ok = neml::verify_consistency(&Sha256Hasher, 1, 2, 1, &proof_invalid_arity_low.start_hash, &proof_invalid_arity_low.path, &[0; 32], &[0; 32]);
    assert!(!ok);

    // Invalid log arity > 256
    let proof_invalid_arity_high = neml::ConsistencyProof {
        start_hash: vec![0; 32],
        path: Vec::new(),
    };
    let ok = neml::verify_consistency(&Sha256Hasher, 1, 2, 257, &proof_invalid_arity_high.start_hash, &proof_invalid_arity_high.path, &[0; 32], &[0; 32]);
    assert!(!ok);
}

#[test]
fn test_inclusion_proof_dos_prevention() {
    let hasher = Sha256Hasher;
    let leaf_hash = hasher.leaf(b"test");
    let root = hasher.empty();

    // Large log arity > 256
    let proof = neml::InclusionProof {
        path: Vec::new(),
    };
    let ok = neml::verify_inclusion(&hasher, &leaf_hash, 0, 1_000_000_000_000, 1_000_000_000_001, &proof.path, &root);
    assert!(!ok);

    // Invalid log arity = 1
    let proof = neml::InclusionProof {
        path: Vec::new(),
    };
    let ok = neml::verify_inclusion(&hasher, &leaf_hash, 0, 10, 1, &proof.path, &root);
    assert!(!ok);

    // Path length > 256
    let proof_huge_path = neml::InclusionProof {
        path: vec![
            neml::ProofStep {
                siblings: vec![vec![0; 32]],
                position: 0,
            };
            257
        ],
    };
    let ok = neml::verify_inclusion(&hasher, &leaf_hash, 0, 10, 2, &proof_huge_path.path, &root);
    assert!(!ok);

    // Sibling count > 256
    let proof_huge_siblings = neml::InclusionProof {
        path: vec![neml::ProofStep {
            siblings: vec![vec![0; 32]; 257],
            position: 0,
        }],
    };
    let ok = neml::verify_inclusion(&hasher, &leaf_hash, 0, 10, 2, &proof_huge_siblings.path, &root);
    assert!(!ok);
}

#[test]
fn test_tree_new_error_propagation() {
    let storage = neml::MemoryStorage::new();
    // Invalid arity 1 should return Err, not panic
    let res = smol::block_on(neml::NaryMerkleLog::new(
        storage.clone(),
        Box::new(Sha256Hasher),
        neml::TreeConfig { log_arity: 1 },
    ));
    assert!(res.is_err());

    // Invalid arity 257 should return Err, not panic
    let res = smol::block_on(neml::NaryMerkleLog::new(
        storage,
        Box::new(Sha256Hasher),
        neml::TreeConfig { log_arity: 257 },
    ));
    assert!(res.is_err());
}

#[test]
fn test_node_coordinate_storage_roundtrip() {
    // Verify that nodes at left >= 2^48 do not collide with left % 2^48.
    smol::block_on(async {
        let mut storage = neml::MemoryStorage::new();

        let left1 = 0u64;
        let height1 = 0u32;
        let left2 = 1u64 << 48;
        let height2 = 0u32;

        storage
            .store_node(0, left1, height1, b"hash1")
            .await
            .unwrap();
        storage
            .store_node(0, left2, height2, b"hash2")
            .await
            .unwrap();

        let h1 = storage.get_node(0, left1, height1).await.unwrap().unwrap();
        let h2 = storage.get_node(0, left2, height2).await.unwrap().unwrap();

        assert_eq!(h1, b"hash1");
        assert_eq!(h2, b"hash2");
    });
}

struct MockStorage {
    metas: Result<neml::AlgorithmMetas, neml::storage::MemoryStorageError>,
    len: u64,
}

impl Storage for MockStorage {
    type Error = neml::storage::MemoryStorageError;

    async fn store_leaf(&mut self, _index: u64, _data: &[u8]) -> Result<(), Self::Error> {
        Ok(())
    }

    async fn get_leaf(&self, _index: u64) -> Result<Vec<u8>, Self::Error> {
        Ok(Vec::new())
    }

    async fn len(&self) -> u64 {
        self.len
    }

    async fn store_node(
        &mut self,
        _alg_id: u64,
        _left: u64,
        _height: u32,
        _hash: &[u8],
    ) -> Result<(), Self::Error> {
        Ok(())
    }

    async fn get_node(
        &self,
        _alg_id: u64,
        _left: u64,
        _height: u32,
    ) -> Result<Option<Vec<u8>>, Self::Error> {
        Ok(None)
    }

    async fn store_algorithm_meta(
        &mut self,
        _alg_id: u64,
        _epochs: &[(u64, u64)],
    ) -> Result<(), Self::Error> {
        Ok(())
    }

    async fn load_algorithm_metas(&self) -> Result<neml::AlgorithmMetas, Self::Error> {
        self.metas.clone()
    }
}

#[test]
fn test_from_storage_initialization_errors() {
    smol::block_on(async {
        // 1. Duplicate algorithm error
        let storage_dup = MockStorage {
            metas: Ok(vec![(0, vec![(0, 0)]), (0, vec![(0, 0)])]),
            len: 0,
        };
        let res =
            neml::NaryMerkleLog::from_storage(storage_dup, vec![(0, Box::new(Sha256Hasher))]).await;
        assert!(matches!(
            res,
            Err(neml::error::Error::DuplicateAlgorithm(0))
        ));

        // 2. Orphaned metadata error (metas has alg 0, but no hasher for alg 0 is passed)
        let storage_orphaned = MockStorage {
            metas: Ok(vec![(0, vec![(0, 0)])]),
            len: 0,
        };
        let res = neml::NaryMerkleLog::from_storage(storage_orphaned, Vec::new()).await;
        assert!(matches!(res, Err(neml::error::Error::OrphanedMetadata(0))));

        // 3. Unknown metadata error (hasher passed for alg 1, but metas only has alg 0)
        let storage_unknown = MockStorage {
            metas: Ok(vec![(0, vec![(0, 0)])]),
            len: 0,
        };
        let res = neml::NaryMerkleLog::from_storage(
            storage_unknown,
            vec![(0, Box::new(Sha256Hasher)), (1, Box::new(Sha256Hasher))],
        )
        .await;
        assert!(matches!(res, Err(neml::error::Error::UnknownMetadata(1))));

        // 4. Corrupted metadata error (invalid log arity < 2)
        let storage_corrupt = MockStorage {
            metas: Ok(vec![(0, vec![(0, 0)])]),
            len: 0,
        };
        let res = neml::NaryMerkleLog::from_storage_with_config(
            storage_corrupt,
            vec![(0, Box::new(Sha256Hasher))],
            TreeConfig { log_arity: 1 },
        )
        .await;
        assert!(matches!(
            res,
            Err(neml::error::Error::CorruptedMetadata { alg_id: 0, .. })
        ));

        // 5. Storage error propagation
        let storage_err = MockStorage {
            metas: Err(neml::storage::MemoryStorageError {
                index: 0,
                stored: 0,
            }),
            len: 0,
        };
        let res =
            neml::NaryMerkleLog::from_storage(storage_err, vec![(0, Box::new(Sha256Hasher))]).await;
        assert!(matches!(
            res,
            Err(neml::error::Error::Storage(
                neml::storage::MemoryStorageError {
                    index: 0,
                    stored: 0
                }
            ))
        ));
    });
}

#[test]
fn test_null_preimage_collision() {
    let hasher = Sha256Hasher;
    // With null constant as a simple fixed value, preimage resistance is not required.
    // Thus, leaf(b"null") is allowed to collide with the null digest.
    assert_eq!(hasher.leaf(b"null"), hasher.null());
}

#[test]
fn test_inclusion_proof_arity_zero_index_spoofing() {
    let hasher = Sha256Hasher;
    let leaf_a = hasher.leaf(b"A");
    let leaf_b = hasher.leaf(b"B");

    // root = nary_mr(&[leaf_a, leaf_b])
    let root = neml::mr::nary_mr(&hasher, &[&leaf_a, &leaf_b]);

    // This proof asserts leaf_a is at index 1 (which is false, it's at index 0)
    // By setting log_arity: 0, verify_inclusion_path_structure is bypassed,
    // but the verifier should reject it because log_arity < 2 is invalid!
    let spoofed_proof = neml::InclusionProof {
        path: vec![neml::ProofStep {
            siblings: vec![leaf_b.clone()],
            position: 0, // position 0 means leaf_a is at the left (index 0)
        }],
    };

    let coupling = neml::CouplingProof {
        active_roots: vec![(0, root.clone())],
        alg_epochs: vec![(0, vec![(0, u64::MAX)])],
    };
    let combined_root = hasher.hash(&neml::combined_root_preimage(
        &coupling.active_roots,
        &coupling.alg_epochs,
    ));

    let is_valid = neml::verify_inclusion_with_coupling(
        &hasher,
        0,
        &leaf_a,
        1,
        2,
        0,
        &spoofed_proof.path,
        &coupling,
        &combined_root,
        &[0],
        neml::VerifierConfig::default(),
    );
    assert!(!is_valid, "Expected arity zero proof to be rejected by verifier API");
}

#[test]
fn test_proof_sibling_digest_length_mismatch() {
    let hasher = Sha256Hasher;
    let leaf_a = hasher.leaf(b"A");
    let leaf_b = hasher.leaf(b"B");
    let root = neml::mr::nary_mr(&hasher, &[&leaf_a, &leaf_b]);

    // Proof with malformed sibling digest length (e.g. 16 bytes instead of 32)
    let malformed_proof = neml::InclusionProof {
        path: vec![neml::ProofStep {
            siblings: vec![vec![0; 16]], // invalid sibling size
            position: 0,
        }],
    };

    let is_valid = neml::verify_inclusion(&hasher, &leaf_a, 0, 2, 2, &malformed_proof.path, &root);
    assert!(!is_valid, "Expected proof with invalid sibling size to be rejected");
}

#[test]
fn test_determine_global_size_probing_out_of_sync() {
    smol::block_on(async {
        let mut storage = MemoryStorage::new();

        // Setup metadata for alg 0 and alg 1, both active starting at size 0
        storage.store_algorithm_meta(0, &[(0, u64::MAX)]).await.unwrap();
        storage.store_algorithm_meta(1, &[(0, u64::MAX)]).await.unwrap();

        // Write nodes for alg 0 up to index 2 (size 3)
        let node_val = vec![1; 32];
        storage.store_node(0, 0, 0, &node_val).await.unwrap();
        storage.store_node(0, 1, 0, &node_val).await.unwrap();
        storage.store_node(0, 2, 0, &node_val).await.unwrap();

        // Write nodes for alg 1 only up to index 1 (size 2, index 2 is missing!)
        storage.store_node(1, 0, 0, &node_val).await.unwrap();
        storage.store_node(1, 1, 0, &node_val).await.unwrap();

        // Load tree from storage
        let hashers: Vec<(u64, Box<dyn neml::Hasher>)> = vec![
            (0, Box::new(Sha256Hasher)),
            (1, Box::new(Sha256Hasher)),
        ];

        // This fails with CorruptedMetadata as expected under R10.
        let reconstructed = NaryMerkleLog::from_storage_with_config(
            storage.clone(),
            hashers,
            TreeConfig { log_arity: 2 },
        )
        .await;

        assert!(reconstructed.is_err(), "Expected from_storage to fail due to out of sync algorithm frontier nodes");
    });
}

#[derive(Clone)]
struct ErrorMaskingStorage {
    inner: MemoryStorage,
    mask_len_to_zero: std::sync::Arc<std::sync::atomic::AtomicBool>,
}

impl neml::Storage for ErrorMaskingStorage {
    type Error = neml::storage::MemoryStorageError;

    async fn store_leaf(&mut self, index: u64, data: &[u8]) -> Result<(), Self::Error> {
        if index < self.inner.leaves.len() as u64 {
            self.inner.leaves[index as usize] = data.to_vec();
            Ok(())
        } else {
            self.inner.store_leaf(index, data).await
        }
    }

    async fn get_leaf(&self, index: u64) -> Result<Vec<u8>, Self::Error> {
        self.inner.get_leaf(index).await
    }

    async fn len(&self) -> u64 {
        if self.mask_len_to_zero.load(std::sync::atomic::Ordering::SeqCst) {
            0
        } else {
            self.inner.len().await
        }
    }

    async fn store_node(
        &mut self,
        alg_id: u64,
        left: u64,
        height: u32,
        hash: &[u8],
    ) -> Result<(), Self::Error> {
        self.inner.store_node(alg_id, left, height, hash).await
    }

    async fn get_node(
        &self,
        alg_id: u64,
        left: u64,
        height: u32,
    ) -> Result<Option<Vec<u8>>, Self::Error> {
        self.inner.get_node(alg_id, left, height).await
    }

    async fn store_algorithm_meta(
        &mut self,
        alg_id: u64,
        epochs: &[(u64, u64)],
    ) -> Result<(), Self::Error> {
        self.inner.store_algorithm_meta(alg_id, epochs).await
    }

    async fn load_algorithm_metas(&self) -> Result<neml::AlgorithmMetas, Self::Error> {
        self.inner.load_algorithm_metas().await
    }
}

#[test]
fn test_storage_len_error_masking_overwrite() {
    smol::block_on(async {
        let mut log = NaryMerkleLog::new(MemoryStorage::new(), Box::new(Sha256Hasher), TreeConfig::default())
            .await
            .unwrap();
        log.append_leaf(b"leaf0").await.unwrap();
        log.append_leaf(b"leaf1").await.unwrap();
        let inner = log.into_storage();

        let mask = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
        let storage = ErrorMaskingStorage {
            inner,
            mask_len_to_zero: mask.clone(),
        };

        // Initially we reconstruct size 2
        {
            let reconstructed = NaryMerkleLog::from_storage(storage.clone(), vec![(0, Box::new(Sha256Hasher))])
                .await
                .unwrap();
            assert_eq!(reconstructed.size(), 2);
        }

        // Now mask len to zero, simulating a transient error
        mask.store(true, std::sync::atomic::Ordering::SeqCst);

        // Reconstruct from storage.
        let mut corrupted_log = NaryMerkleLog::from_storage(storage.clone(), vec![(0, Box::new(Sha256Hasher))])
            .await
            .unwrap();
        assert_eq!(corrupted_log.size(), 0);
        assert_eq!(corrupted_log.subtree_count(), 2);

        // Attempting append_leaf in Subtree Log Mode should fail and prevent overwrite.
        let append_result = corrupted_log.append_leaf(b"leaf_overwrite").await;
        assert!(append_result.is_err(), "Expected append_leaf to fail in Subtree Log Mode");

        // The original leaf0 remains untouched
        let untouched_leaf = corrupted_log.storage().get_leaf(0).await.unwrap();
        assert_eq!(untouched_leaf, b"leaf0");
    });
}

#[test]
fn test_boundary_sizes_and_high_arities() {
    smol::block_on(async {
        for &k in &[3u64, 5, 128, 256] {
            let config = TreeConfig { log_arity: k as usize };
            
            // Boundary sizes around K^1 and K^2
            let mut sizes = vec![k - 1, k, k + 1];
            if k * k <= 512 {
                sizes.extend_from_slice(&[k * k - 1, k * k, k * k + 1]);
            }
            sizes.retain(|&s| s > 0);
            sizes.sort_unstable();
            sizes.dedup();
            
            let max_size = *sizes.last().unwrap();
            let storage = MemoryStorage::new();
            let mut log = NaryMerkleLog::new(storage, Box::new(Sha256Hasher), config)
                .await
                .unwrap();
                
            let mut leaves = Vec::new();
            for i in 0..max_size {
                let data = format!("leaf_{}_{}", k, i).into_bytes();
                log.append_leaf(&data).await.unwrap();
                leaves.push(Sha256Hasher.leaf(&data));
            }
            
            for &size in &sizes {
                let root = log.root_for_at(0, size).await.unwrap();
                
                // Verify inclusion proof for every index in the tree of this size
                for idx in 0..size {
                    let proof = log.inclusion_proof_for(0, idx, size).await.unwrap().unwrap();
                    assert!(neml::verify_inclusion(
                        &Sha256Hasher,
                        &leaves[idx as usize],
                        idx,
                        size,
                        k as u64,
                        &proof.path,
                        &root
                    ), "Inclusion failed for k={}, size={}, idx={}", k, size, idx);
                }
                
                // Verify consistency proofs between all smaller valid sizes
                for &old_size in &sizes {
                    if old_size >= size {
                        break;
                    }
                    let old_root = log.root_for_at(0, old_size).await.unwrap();
                    let proof = log.consistency_proof_for(0, old_size, size).await.unwrap().unwrap();
                    assert!(neml::verify_consistency(
                        &Sha256Hasher,
                        old_size,
                        size,
                        k as u64,
                        &proof.start_hash,
                        &proof.path,
                        &old_root,
                        &root
                    ), "Consistency failed for k={}, old_size={}, new_size={}", k, old_size, size);
                }
            }
        }
    });
}

#[test]
fn test_null_digest() {
    let hasher = Sha256Hasher;
    let d = neml::null_digest(&hasher);
    assert_eq!(d, hasher.hash(b"null"));
}

#[test]
fn test_proof_malleability_path_extension() {
    smol::block_on(async {
        let hasher = Sha256Hasher;
        let storage = MemoryStorage::new();
        let config = TreeConfig { log_arity: 2 };
        let mut log = NaryMerkleLog::new(storage, Box::new(hasher), config)
            .await
            .unwrap();

        log.append_leaf(b"a").await.unwrap();
        log.append_leaf(b"b").await.unwrap();
        log.append_leaf(b"c").await.unwrap();
        log.append_leaf(b"d").await.unwrap();

        let proof = log.inclusion_proof(2, 4).await.unwrap().unwrap();
        let leaf_hash = Sha256Hasher.leaf(b"c");
        let root = log.root();

        // 1. Original proof verifies successfully
        assert!(neml::verify_inclusion(
            &Sha256Hasher,
            &leaf_hash,
            2,
            4,
            2,
            &proof.path,
            &root
        ));

        // 2. Prepend a dummy step with empty siblings.
        let mut malleable_path = vec![
            neml::ProofStep {
                siblings: vec![],
                position: 42,
            }
        ];
        malleable_path.extend(proof.path.clone());

        // 3. Verifies should fail because of path length mismatch or position spoofing
        let verified = neml::verify_inclusion(
            &Sha256Hasher,
            &leaf_hash,
            2,
            4,
            2,
            &malleable_path,
            &root
        );
        assert!(!verified, "Malleable proof verification should fail");
    });
}

#[test]
fn test_proof_malleability_position_spoofing() {
    smol::block_on(async {
        let hasher = Sha256Hasher;
        let storage = MemoryStorage::new();
        let config = TreeConfig { log_arity: 2 };
        let mut log = NaryMerkleLog::new(storage, Box::new(hasher), config)
            .await
            .unwrap();

        // Subtree: Node([Leaf("a")]) (promoted node)
        let subtree = Subtree::Node(vec![Subtree::Leaf(b"a".to_vec())]);
        log.append_subtree(&subtree).await.unwrap();

        let root = log.root();
        let path = neml::within_subtree_path(&Sha256Hasher, &subtree, 0).unwrap();
        // Since subtree has 1 leaf, the path has 1 promoted node step with position 0
        assert_eq!(path[0].siblings.len(), 0);
        assert_eq!(path[0].position, 0);

        let log_proof = log.inclusion_proof(0, 1).await.unwrap().unwrap();
        let mut full_path = path;
        full_path.extend(log_proof.path);

        let leaf_hash = Sha256Hasher.leaf(b"a");
        assert!(neml::verify_inclusion(
            &Sha256Hasher,
            &leaf_hash,
            0,
            1,
            2,
            &full_path,
            &root
        ));

        // Spoof the promoted node step's position to 42
        let mut spoofed_path = full_path.clone();
        spoofed_path[0].position = 42;

        assert!(!neml::verify_inclusion(
            &Sha256Hasher,
            &leaf_hash,
            0,
            1,
            2,
            &spoofed_path,
            &root
        ), "Spoofed promoted position must be rejected");
    });
}

#[test]
fn test_reduction_count_overflow() {
    // Assert it returns 0 (since 2^64 does not divide by k=2)
    // and does not panic or loop infinitely
    let res = neml::reduction_count(u64::MAX, 2);
    assert_eq!(res, 0);
}

#[test]
fn test_reconstruct_index_oom_dos() {
    // Large log_arity must be rejected without OOMing or panicking
    let large_k = 1u64 << 32;
    let res = neml::reconstruct_consistency_roots(&Sha256Hasher, 1, 2, large_k, &[0; 32], &[]);
    assert_eq!(res, None);
}


