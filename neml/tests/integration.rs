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

/// Verify that `verify_non_divergence` correctly handles a late-activated
/// algorithm (registered at size M > 0) when the checkpoint `start` falls
/// before activation (0 < start < M) or after (M < start < N).
///
/// The carry schedule must be driven by the global leaf index, not a
/// per-algorithm-relative index.  An all-null prefix of size S has the
/// same frontier geometry as a tree of S real leaves (by null promotion),
/// so `alg_size` must be initialized to `start`, not 0, at checkpoint time.
///
/// Parametrized over k ∈ {2, 3, 256} with activation at a carry boundary
/// (size k^2) to catch off-by-one alignment errors.
#[test]
fn test_late_activated_alg_checkpoint() {
    smol::block_on(async {
        // (k, M) pairs: M = k^2 aligns activation with a 2-carry boundary.
        // k=256 uses M=k to keep the test fast while still hitting the
        // first carry boundary in the null prefix.
        let cases: &[(usize, u64)] = &[(2, 4), (3, 9), (256, 256)];

        for &(k, m) in cases {
            let n = m + m; // total leaves: M null-prefix + M active
            let start_pre = m / 2; // checkpoint strictly before activation
            let start_post = m + m / 2; // checkpoint strictly after activation

            let config = TreeConfig { log_arity: k };

            // ── Build log ──────────────────────────────────────────────────
            let mut log = NaryMerkleLog::new(
                MemoryStorage::new(),
                Box::new(Sha256Hasher),
                config,
            )
            .await
            .unwrap();

            // Append M leaves with only algorithm 0.
            for i in 0u64..m {
                log.append_leaf(&i.to_le_bytes()).await.unwrap();
            }

            // Register algorithm 1 at size M (late activation).
            log.add_algorithm(1, Box::new(Sha256Hasher)).await.unwrap();

            // Append M more leaves; both algorithms process them.
            for i in m..n {
                log.append_leaf(&i.to_le_bytes()).await.unwrap();
            }

            // ── Honest: checkpoint before activation ───────────────────────
            // Algorithm 1 was not yet registered at start_pre; the verifier
            // derives its expected root (null) internally — no entry needed.
            let trusted_pre = vec![
                (0u64, log.root_for_at(0, start_pre).await.unwrap()),
            ];
            let ok = log
                .verify_non_divergence(Some(start_pre), &trusted_pre)
                .await
                .unwrap();
            assert!(
                ok,
                "k={k} M={m} start={start_pre}: honest log failed pre-activation checkpoint"
            );

            // ── Honest: checkpoint after activation ────────────────────────
            let trusted_post = vec![
                (0u64, log.root_for_at(0, start_post).await.unwrap()),
                (1u64, log.root_for_at(1, start_post).await.unwrap()),
            ];
            let ok_post = log
                .verify_non_divergence(Some(start_post), &trusted_post)
                .await
                .unwrap();
            assert!(
                ok_post,
                "k={k} M={m} start={start_post}: honest log failed post-activation checkpoint"
            );

            // ── Tamper: corrupt a leaf in algorithm 1's active range ───────
            // Overwrite the stored leaf hash for algorithm 1 at position M
            // (its first real leaf) with a wrong value.
            let bad_hash = vec![0xab_u8; 32];
            log.storage_mut().nodes.insert((1u64, m, 0), bad_hash);

            let ok_tampered = log
                .verify_non_divergence(Some(start_pre), &trusted_pre)
                .await
                .unwrap();
            assert!(
                !ok_tampered,
                "k={k} M={m}: tampered log should have failed verification"
            );
        }
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

    async fn store_log_meta(&mut self, _count: u64, _kind: u8) -> Result<(), Self::Error> {
        Ok(())
    }

    async fn load_log_meta(&self) -> Result<Option<(u64, u8)>, Self::Error> {
        Ok(None)
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

    async fn store_log_meta(&mut self, count: u64, kind: u8) -> Result<(), Self::Error> {
        self.inner.store_log_meta(count, kind).await
    }

    async fn load_log_meta(&self) -> Result<Option<(u64, u8)>, Self::Error> {
        self.inner.load_log_meta().await
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

        // Mask len to zero, simulating a transient read error on the leaf keyspace.
        mask.store(true, std::sync::atomic::Ordering::SeqCst);

        // With persisted log_meta, from_storage reads the authoritative (count, kind)
        // directly and does not rely on len() for mode inference.
        let log_after_mask = NaryMerkleLog::from_storage(storage.clone(), vec![(0, Box::new(Sha256Hasher))])
            .await
            .unwrap();
        assert_eq!(log_after_mask.size(), 2, "persisted log_meta wins over masked len()");
        assert_eq!(log_after_mask.subtree_count(), 0);
        assert_eq!(log_after_mask.kind(), neml::LogKind::Flat);
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

        // Subtree wrapping a single leaf: the unary node is promoted, so under
        // canonical proof encoding it contributes no proof step.
        let subtree = Subtree::Node(vec![Subtree::Leaf(b"a".to_vec())]);
        log.append_subtree(&subtree).await.unwrap();

        let root = log.root();
        let path = neml::within_subtree_path(&Sha256Hasher, &subtree, 0).unwrap();
        assert!(path.is_empty(), "promoted unary node must emit no proof step");

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

        // Canonical encoding: a promoted (zero-sibling) step is a hash no-op, so
        // prepending one leaves the computed root unchanged — yet it must be
        // rejected to keep the accepting path unique.
        for position in [0usize, 42] {
            let mut spoofed = full_path.clone();
            spoofed.insert(
                0,
                neml::ProofStep {
                    siblings: vec![],
                    position,
                },
            );
            assert!(
                !neml::verify_inclusion(&Sha256Hasher, &leaf_hash, 0, 1, 2, &spoofed, &root),
                "prepended promoted step (position {position}) must be rejected"
            );
        }
    });
}

/// Removing a log-skeleton step must be rejected: the verifier knows the exact
/// skeleton length from the trusted `(index, tree_size, arity)`.
#[test]
fn test_inclusion_truncated_skeleton_rejected() {
    smol::block_on(async {
        let storage = MemoryStorage::new();
        let mut log =
            NaryMerkleLog::new(storage, Box::new(Sha256Hasher), TreeConfig { log_arity: 2 })
                .await
                .unwrap();
        for d in [b"a".as_ref(), b"b", b"c", b"d"] {
            log.append_leaf(d).await.unwrap();
        }
        let root = log.root();

        let proof = log.inclusion_proof(2, 4).await.unwrap().unwrap();
        let leaf = Sha256Hasher.leaf(b"c");
        assert!(neml::verify_inclusion(&Sha256Hasher, &leaf, 2, 4, 2, &proof.path, &root));

        assert!(!proof.path.is_empty());
        let truncated = &proof.path[..proof.path.len() - 1];
        assert!(
            !neml::verify_inclusion(&Sha256Hasher, &leaf, 2, 4, 2, truncated, &root),
            "a proof missing a skeleton step must be rejected"
        );
    });
}

/// The last leaf of a non-full ternary tree reaches the root through a *partial*
/// (fewer-than-k children) grouping node. Its sibling count is pinned exactly, so
/// an off-by-one there — the highest-risk forgery — must be rejected.
#[test]
fn test_partial_rightmost_node_sibling_count() {
    smol::block_on(async {
        let storage = MemoryStorage::new();
        let mut log =
            NaryMerkleLog::new(storage, Box::new(Sha256Hasher), TreeConfig { log_arity: 3 })
                .await
                .unwrap();
        for d in [b"a".as_ref(), b"b", b"c", b"d"] {
            log.append_leaf(d).await.unwrap();
        }
        let root = log.root();

        let proof = log.inclusion_proof(3, 4).await.unwrap().unwrap();
        let leaf = Sha256Hasher.leaf(b"d");
        assert!(neml::verify_inclusion(&Sha256Hasher, &leaf, 3, 4, 3, &proof.path, &root));

        // The root joins two frontier nodes here, so the rightmost step carries
        // exactly one sibling.
        let last = proof.path.last().unwrap();
        assert_eq!(last.siblings.len(), 1);

        // One sibling too many: claiming the root has three children is a forgery.
        let mut extra = proof.path.clone();
        extra.last_mut().unwrap().siblings.push(vec![0u8; 32]);
        assert!(
            !neml::verify_inclusion(&Sha256Hasher, &leaf, 3, 4, 3, &extra, &root),
            "an extra rightmost sibling must be rejected"
        );

        // One sibling too few (also a zero-sibling step).
        let mut fewer = proof.path.clone();
        fewer.last_mut().unwrap().siblings.clear();
        assert!(
            !neml::verify_inclusion(&Sha256Hasher, &leaf, 3, 4, 3, &fewer, &root),
            "a missing rightmost sibling must be rejected"
        );
    });
}

/// Spoofing a *skeleton* step's position breaks the topological binding to the
/// trusted index, even though the step still hashes.
#[test]
fn test_skeleton_position_spoof_rejected() {
    smol::block_on(async {
        let storage = MemoryStorage::new();
        let mut log =
            NaryMerkleLog::new(storage, Box::new(Sha256Hasher), TreeConfig { log_arity: 2 })
                .await
                .unwrap();
        for d in [b"a".as_ref(), b"b", b"c", b"d"] {
            log.append_leaf(d).await.unwrap();
        }
        let root = log.root();

        let proof = log.inclusion_proof(2, 4).await.unwrap().unwrap();
        let leaf = Sha256Hasher.leaf(b"c");
        assert!(neml::verify_inclusion(&Sha256Hasher, &leaf, 2, 4, 2, &proof.path, &root));

        let mut spoofed = proof.path.clone();
        spoofed[0].position ^= 1;
        assert!(
            !neml::verify_inclusion(&Sha256Hasher, &leaf, 2, 4, 2, &spoofed, &root),
            "a spoofed skeleton position must be rejected"
        );
    });
}

/// Canonical encoding: a promotion-heavy subtree verifies with its unary chain
/// omitted, and a zero-sibling step inserted *anywhere* in the path is rejected.
#[test]
fn test_canonical_encoding_promotion_chain() {
    smol::block_on(async {
        let storage = MemoryStorage::new();
        let mut log =
            NaryMerkleLog::new(storage, Box::new(Sha256Hasher), TreeConfig { log_arity: 2 })
                .await
                .unwrap();
        // "x" sits under a two-level unary chain that contributes no proof steps.
        let subtree = Subtree::Node(vec![
            Subtree::Node(vec![Subtree::Node(vec![Subtree::Leaf(b"x".to_vec())])]),
            Subtree::Leaf(b"y".to_vec()),
        ]);
        log.append_subtree(&subtree).await.unwrap();
        log.append_subtree(&Subtree::Node(vec![Subtree::Leaf(b"z".to_vec())]))
            .await
            .unwrap();
        let root = log.root();

        let mut path = neml::within_subtree_path(&Sha256Hasher, &subtree, 0).unwrap();
        assert_eq!(path.len(), 1, "the unary chain above x must be omitted");
        let log_proof = log.inclusion_proof(0, 2).await.unwrap().unwrap();
        path.extend(log_proof.path);

        let leaf = Sha256Hasher.leaf(b"x");
        assert!(neml::verify_inclusion(&Sha256Hasher, &leaf, 0, 2, 2, &path, &root));

        for pos in 0..=path.len() {
            let mut tampered = path.clone();
            tampered.insert(
                pos,
                neml::ProofStep {
                    siblings: vec![],
                    position: 0,
                },
            );
            assert!(
                !neml::verify_inclusion(&Sha256Hasher, &leaf, 0, 2, 2, &tampered, &root),
                "a zero-sibling step at offset {pos} must be rejected"
            );
        }
    });
}

#[test]
fn test_reduction_count_overflow() {
    // u64::MAX + 1 == 2^64, which is divisible by 2 exactly 64 times.
    // Verify the function returns the correct count without panicking or
    // looping infinitely.
    let res = neml::reduction_count(u64::MAX, 2);
    assert_eq!(res, 64);
}

#[test]
fn test_reconstruct_index_oom_dos() {
    // Large log_arity must be rejected without OOMing or panicking
    let large_k = 1u64 << 32;
    let res = neml::reconstruct_consistency_roots(&Sha256Hasher, 1, 2, large_k, &[0; 32], &[]);
    assert_eq!(res, None);
}

// ── Design A+ acceptance tests (epoch commitment for inactivity soundness) ──

/// The equivocation attack that motivates Design A+: two histories that share
/// the same carrier (Y=0) produce byte-identical raw roots for the target
/// algorithm (X=1) at the same tree size, because `leaf(b"null") == null()`.
/// The combined root and audit payload must differ, proving that the epoch
/// timeline binding breaks the equivocation.
#[test]
fn test_two_histories_equivocation() {
    smol::block_on(async {
        let log_id = [0u8; 32];
        let cfg = TreeConfig { log_arity: 2 };

        // History 1: X=1 added before any appends (active from pos 0).
        // Append b"null" at pos 0 → leaf("null") == null() for X.
        let mut h1 = NaryMerkleLog::new(
            MemoryStorage::new(), Box::new(Sha256Hasher), cfg,
        ).await.unwrap();
        h1.add_algorithm(1, Box::new(Sha256Hasher)).await.unwrap();
        h1.append_leaf(b"null").await.unwrap();
        h1.append_leaf(b"data1").await.unwrap();

        // History 2: append b"null" first (pos 0, X inactive), then add X=1
        // at size 1 so X's pre-activation null projection at pos 0 also equals
        // null(). Append b"data1" at pos 1.
        let mut h2 = NaryMerkleLog::new(
            MemoryStorage::new(), Box::new(Sha256Hasher), cfg,
        ).await.unwrap();
        h2.append_leaf(b"null").await.unwrap();
        h2.add_algorithm(1, Box::new(Sha256Hasher)).await.unwrap();
        h2.append_leaf(b"data1").await.unwrap();

        // X's raw roots at size 2 must be identical — the equivocation is real.
        let raw_x_h1 = h1.root_for_at(1, 2).await.unwrap();
        let raw_x_h2 = h2.root_for_at(1, 2).await.unwrap();
        assert_eq!(raw_x_h1, raw_x_h2, "raw X roots must collide");

        // The epoch timelines differ (X active from 0 vs from 1), so the
        // combined roots and audit payloads must differ.
        let cr_h1 = h1.combined_root_at(0, 2).await.unwrap();
        let cr_h2 = h2.combined_root_at(0, 2).await.unwrap();
        assert_ne!(cr_h1, cr_h2, "combined roots must differ");

        let ap_h1 = h1.audit_payload(log_id).await.unwrap();
        let ap_h2 = h2.audit_payload(log_id).await.unwrap();
        assert_ne!(ap_h1, ap_h2);
        assert_ne!(ap_h1.alg_epochs, ap_h2.alg_epochs);
    });
}

/// An auditor cannot forge a checkpoint that claims X was inactive at a
/// position where the stored tree cell is non-null.
#[test]
fn test_attestation_rejects_contradiction() {
    smol::block_on(async {
        let log_id = [1u8; 32];
        let cfg = TreeConfig { log_arity: 2 };

        // Honest log: X=1 active from pos 0, one real (non-"null") leaf.
        let mut log = NaryMerkleLog::new(
            MemoryStorage::new(), Box::new(Sha256Hasher), cfg,
        ).await.unwrap();
        log.add_algorithm(1, Box::new(Sha256Hasher)).await.unwrap();
        log.append_leaf(b"data").await.unwrap();

        let honest = log.audit_payload(log_id).await.unwrap();
        assert!(log.verify_audit_payload(&honest).await.unwrap());

        // Variant A: keep the honest combined roots but shift X's epoch to
        // start at 1 instead of 0. The combined roots no longer match the
        // shifted preimage → root mismatch rejection.
        let mut var_a = honest.clone();
        var_a.alg_epochs = vec![
            (0, vec![(0u64, u64::MAX)]),
            (1, vec![(1u64, u64::MAX)]),
        ];
        // With X inactive at pos 0, only alg 0 is active at size 1.
        var_a.active_algs = vec![0];
        var_a.combined_roots = vec![(0, log.combined_root_at(0, 1).await.unwrap())];
        assert!(!log.verify_audit_payload(&var_a).await.unwrap(),
            "shifted epoch with honest roots must be rejected");

        // Variant B: build a second log where X really activates at size 1,
        // obtaining combined roots that DO match the shifted epochs.
        let mut log2 = NaryMerkleLog::new(
            MemoryStorage::new(), Box::new(Sha256Hasher), cfg,
        ).await.unwrap();
        log2.append_leaf(b"data").await.unwrap();
        log2.add_algorithm(1, Box::new(Sha256Hasher)).await.unwrap();

        let payload2 = log2.audit_payload(log_id).await.unwrap();
        assert!(log2.verify_audit_payload(&payload2).await.unwrap(),
            "payload2 must be honest for log2");

        // Present log2's payload (epochs claiming X inactive at pos 0) against
        // log1's storage: stored cell at (X, 0, 0) = H("data") ≠ null() →
        // the contradiction is detected.
        assert!(!log.verify_audit_payload(&payload2).await.unwrap(),
            "cross-log payload must be rejected by the cell check");
    });
}

/// Substituting the epoch metadata in a coupling proof breaks the hash
/// binding, causing both inclusion and inactivity verification to fail.
#[test]
fn test_substituted_metadata_fails_proofs() {
    smol::block_on(async {
        let cfg = TreeConfig { log_arity: 2 };

        // Log: Y=0 active from 0; X=1 added at size 1 (inactive at pos 0).
        let mut log = NaryMerkleLog::new(
            MemoryStorage::new(), Box::new(Sha256Hasher), cfg,
        ).await.unwrap();
        log.append_leaf(b"data0").await.unwrap();
        log.add_algorithm(1, Box::new(Sha256Hasher)).await.unwrap();
        log.append_leaf(b"data1").await.unwrap();

        let coupling = log.coupling_proof_at(2).await.unwrap();
        let cr = log.combined_root_at(0, 2).await.unwrap();
        let config = neml::VerifierConfig::default();

        // Honest inactivity proof for X=1 at pos 0 (inactive, null cell).
        let inact_path = log.inclusion_proof_for(1, 0, 2).await.unwrap().unwrap();
        let ok_inact = neml::verify_inactivity_with_coupling(
            &Sha256Hasher, 1, 0, 2, 2,
            &inact_path.path, &coupling, &cr, &[0, 1], config,
        );
        assert!(ok_inact, "honest inactivity proof must verify");

        // Honest inclusion proof for X=1 at pos 1 (active, real data).
        let incl_path = log.inclusion_proof_for(1, 1, 2).await.unwrap().unwrap();
        let leaf_hash = Sha256Hasher.leaf(b"data1");
        let ok_incl = neml::verify_inclusion_with_coupling(
            &Sha256Hasher, 1, &leaf_hash, 1, 2, 2,
            &incl_path.path, &coupling, &cr, &[0, 1], config,
        );
        assert!(ok_incl, "honest inclusion proof must verify");

        // Swap alg_epochs: pretend X was active from position 0.  The
        // preimage hash no longer matches the combined root.
        let mut bad_coupling = coupling.clone();
        bad_coupling.alg_epochs = vec![
            (0, vec![(0u64, u64::MAX)]),
            (1, vec![(0u64, u64::MAX)]),
        ];

        let fail_inact = neml::verify_inactivity_with_coupling(
            &Sha256Hasher, 1, 0, 2, 2,
            &inact_path.path, &bad_coupling, &cr, &[0, 1], config,
        );
        assert!(!fail_inact, "substituted epochs must break inactivity proof");

        let fail_incl = neml::verify_inclusion_with_coupling(
            &Sha256Hasher, 1, &leaf_hash, 1, 2, 2,
            &incl_path.path, &bad_coupling, &cr, &[0, 1], config,
        );
        assert!(!fail_incl, "substituted epochs must break inclusion proof");
    });
}

/// Appending b"null" must succeed and its inclusion proof must verify
/// against an active epoch — the one-directional check (inactive⇒N₀)
/// does not forbid active cells whose payload hashes to the null constant.
#[test]
fn test_null_payload_stays_legal() {
    smol::block_on(async {
        let cfg = TreeConfig { log_arity: 2 };
        let mut log = NaryMerkleLog::new(
            MemoryStorage::new(), Box::new(Sha256Hasher), cfg,
        ).await.unwrap();

        // This append must not be rejected.
        log.append_leaf(b"null").await.unwrap();

        let coupling = log.coupling_proof_at(1).await.unwrap();
        let cr = log.combined_root().await;
        let config = neml::VerifierConfig::default();

        // leaf(b"null") == null() — verify it is accepted by the inclusion
        // check (alg 0 is active at pos 0, so the null-leaf constraint is
        // NOT applied).
        let leaf_hash = Sha256Hasher.leaf(b"null");
        assert_eq!(leaf_hash, Sha256Hasher.null(), "sanity: leaf(null) == null()");

        let path = log.inclusion_proof(0, 1).await.unwrap().unwrap();
        let ok = neml::verify_inclusion_with_coupling(
            &Sha256Hasher, 0, &leaf_hash, 0, 1, 2,
            &path.path, &coupling, &cr, &[0], config,
        );
        assert!(ok, "null-payload inclusion must verify under active epoch");
    });
}

/// Deactivating the sole algorithm at the tip must change the combined root
/// even though the raw tree is unchanged — the epoch timeline encodes the
/// deactivation and switches the metaroot from the promoted form to the
/// hashed form.
#[test]
fn test_frontier_freshness() {
    smol::block_on(async {
        let cfg = TreeConfig { log_arity: 2 };

        // Sole-algorithm variant: identical leaf, deactivated vs live.
        let mut log_live = NaryMerkleLog::new(
            MemoryStorage::new(), Box::new(Sha256Hasher), cfg,
        ).await.unwrap();
        log_live.append_leaf(b"data").await.unwrap();

        let mut log_dead = NaryMerkleLog::new(
            MemoryStorage::new(), Box::new(Sha256Hasher), cfg,
        ).await.unwrap();
        log_dead.append_leaf(b"data").await.unwrap();
        log_dead.remove_algorithm(0).await.unwrap();

        let raw_live = log_live.root();
        let raw_dead = log_dead.root_for_at(0, 1).await.unwrap();
        assert_eq!(raw_live, raw_dead, "raw trees are identical");

        let cr_live = log_live.combined_root_at(0, 1).await.unwrap();
        let cr_dead = log_dead.combined_root_at(0, 1).await.unwrap();
        assert_eq!(cr_live, raw_live, "live sole-alg CR is promoted to raw root");
        assert_ne!(cr_dead, raw_dead, "deactivated sole-alg CR must be hashed");
        assert_ne!(cr_live, cr_dead, "combined roots must differ");

        // committed_is_live distinguishes them.
        let epochs_live = log_live.committed_epochs_at(1);
        let epochs_dead = log_dead.committed_epochs_at(1);
        assert_eq!(neml::committed_is_live(&epochs_live, 0), Some(true));
        assert_eq!(neml::committed_is_live(&epochs_dead, 0), Some(false));

        // Two-algorithm variant: identical leaves, second alg deactivated in one.
        let mut log_a = NaryMerkleLog::new(
            MemoryStorage::new(), Box::new(Sha256Hasher), cfg,
        ).await.unwrap();
        log_a.add_algorithm(1, Box::new(Sha256Hasher)).await.unwrap();
        log_a.append_leaf(b"x").await.unwrap();

        let mut log_b = NaryMerkleLog::new(
            MemoryStorage::new(), Box::new(Sha256Hasher), cfg,
        ).await.unwrap();
        log_b.add_algorithm(1, Box::new(Sha256Hasher)).await.unwrap();
        log_b.append_leaf(b"x").await.unwrap();
        log_b.remove_algorithm(1).await.unwrap();

        let raw0_a = log_a.root_for_at(0, 1).await.unwrap();
        let raw0_b = log_b.root_for_at(0, 1).await.unwrap();
        assert_eq!(raw0_a, raw0_b, "raw trees are identical");

        let cr_a = log_a.combined_root_at(0, 1).await.unwrap();
        let cr_b = log_b.combined_root_at(0, 1).await.unwrap();
        assert_ne!(cr_a, cr_b, "combined roots must differ after deactivation");

        let ep_a = log_a.committed_epochs_at(1);
        let ep_b = log_b.committed_epochs_at(1);
        assert_eq!(neml::committed_is_live(&ep_a, 1), Some(true));
        assert_eq!(neml::committed_is_live(&ep_b, 1), Some(false));
    });
}

/// Genesis promotion boundary conditions:
/// - A sole-algorithm log in its default state has CR == raw root.
/// - Any lifecycle event permanently switches to hashed form.
/// - A promoted-form coupling proof fails against a hashed-form CR, and
///   a hashed-form proof fails against a promoted-form CR.
/// - An active-set singleton whose registry contains more than one
///   algorithm is NOT promoted.
#[test]
fn test_genesis_promotion_boundary() {
    smol::block_on(async {
        let cfg = TreeConfig { log_arity: 2 };

        // Genesis state: CR is promoted to the raw root.
        let mut log = NaryMerkleLog::new(
            MemoryStorage::new(), Box::new(Sha256Hasher), cfg,
        ).await.unwrap();
        log.append_leaf(b"a").await.unwrap();
        let raw_at_1 = log.root();
        let cr_at_1_genesis = log.combined_root_at(0, 1).await.unwrap();
        assert_eq!(cr_at_1_genesis, raw_at_1, "genesis CR must equal raw root");

        // Add a second algorithm: registry-singleton broken, permanent switch.
        log.add_algorithm(1, Box::new(Sha256Hasher)).await.unwrap();
        log.append_leaf(b"b").await.unwrap();

        // CR at size 1 is now hashed (registry has two entries).
        let cr_at_1_after = log.combined_root_at(0, 1).await.unwrap();
        assert_ne!(cr_at_1_after, raw_at_1,
            "CR at historical size 1 must be hashed after second alg registration");

        // CR at size 2 is also hashed.
        let raw_at_2 = log.root_for_at(0, 2).await.unwrap();
        let cr_at_2 = log.combined_root_at(0, 2).await.unwrap();
        assert_ne!(cr_at_2, raw_at_2, "CR at size 2 must be hashed");

        // A promoted-form coupling proof presented against the new hashed CR
        // must be rejected: authenticate computes the promoted form (raw root)
        // but the combined root is the hashed form.
        let raw_root_1 = log.root_for_at(0, 1).await.unwrap();
        let promoted_coupling = neml::CouplingProof {
            active_roots: vec![(0, raw_root_1.clone())],
            alg_epochs: vec![(0, vec![(0u64, u64::MAX)])], // genesis default, 1 entry
        };
        let config = neml::VerifierConfig::default();
        assert!(!promoted_coupling.authenticate(
            &Sha256Hasher, 1, &cr_at_1_after, &[0], config,
        ), "promoted proof against hashed CR must fail");

        // A hashed-form coupling proof presented against the old promoted CR
        // must be rejected.
        let hashed_coupling = neml::CouplingProof {
            active_roots: vec![(0, raw_root_1)],
            alg_epochs: vec![
                (0, vec![(0u64, u64::MAX)]),
                (1, vec![(1u64, u64::MAX)]),
            ], // 2 entries → hashed form
        };
        // cr_at_1_genesis is the promoted form (= raw root).
        assert!(!hashed_coupling.authenticate(
            &Sha256Hasher, 1, &cr_at_1_genesis, &[0], config,
        ), "hashed proof against promoted CR must fail");

        // Active-set singleton with a late-activated algorithm must NOT be
        // promoted.  At size 1, alg 0 is active but alg 1 is registered with
        // epoch (1, MAX) — alg 1 is not active at pos 0.  Registry has two
        // entries → hashed form.
        let cr_active_singleton = log.combined_root_at(0, 1).await.unwrap();
        assert_ne!(cr_active_singleton, log.root_for_at(0, 1).await.unwrap(),
            "active-set singleton must not be promoted when registry has >1 alg");
    });
}

/// Inactivity proofs: mid-gap and frozen-algorithm cases.
#[test]
fn test_inactivity_proofs() {
    smol::block_on(async {
        let cfg = TreeConfig { log_arity: 2 };
        let config = neml::VerifierConfig::default();

        // Build a log with X=1 that has a gap: active at [1,2), inactive
        // at [2,4), re-active at [4, MAX).
        let mut log = NaryMerkleLog::new(
            MemoryStorage::new(), Box::new(Sha256Hasher), cfg,
        ).await.unwrap();
        log.append_leaf(b"a").await.unwrap(); // pos 0: Y active, X not yet registered
        log.add_algorithm(1, Box::new(Sha256Hasher)).await.unwrap(); // X added at size 1
        log.append_leaf(b"b").await.unwrap(); // pos 1: both active
        log.remove_algorithm(1).await.unwrap(); // X deactivated at size 2
        log.append_leaf(b"c").await.unwrap(); // pos 2: only Y active (X in gap)
        log.append_leaf(b"d").await.unwrap(); // pos 3: only Y active (X in gap)
        log.resume_algorithm(1).await.unwrap(); // X resumed at size 4
        log.append_leaf(b"e").await.unwrap(); // pos 4: both active again

        // Mid-gap: X is inactive at pos 2 (in the gap [2,4)).
        let coupling = log.coupling_proof_at(5).await.unwrap();
        let cr = log.combined_root_at(0, 5).await.unwrap();
        let active_algs_5 = neml::committed_active_algs(&coupling.alg_epochs, 5);

        // X is in coupling.active_roots (it is active at pos 4 = size 5 - 1).
        // We need the inclusion proof for the null constant at pos 2 in X's tree.
        let inact_path = log.inclusion_proof_for(1, 2, 5).await.unwrap().unwrap();
        let ok_gap = neml::verify_inactivity_with_coupling(
            &Sha256Hasher, 1, 2, 5, 2,
            &inact_path.path, &coupling, &cr, &active_algs_5, config,
        );
        assert!(ok_gap, "mid-gap inactivity proof must verify");

        // Inactivity proof for an ACTIVE position must fail.
        let active_path = log.inclusion_proof_for(1, 1, 5).await.unwrap().unwrap();
        let fail_active = neml::verify_inactivity_with_coupling(
            &Sha256Hasher, 1, 1, 5, 2,
            &active_path.path, &coupling, &cr, &active_algs_5, config,
        );
        assert!(!fail_active, "inactivity proof for active position must fail");

        // Frozen-algorithm case: build a separate log where X is permanently
        // deactivated and not resumed.
        let mut log_frozen = NaryMerkleLog::new(
            MemoryStorage::new(), Box::new(Sha256Hasher), cfg,
        ).await.unwrap();
        log_frozen.append_leaf(b"a").await.unwrap(); // pos 0: Y only
        log_frozen.add_algorithm(1, Box::new(Sha256Hasher)).await.unwrap(); // X at size 1
        log_frozen.append_leaf(b"b").await.unwrap(); // pos 1: both
        log_frozen.remove_algorithm(1).await.unwrap(); // X frozen at size 2
        log_frozen.append_leaf(b"c").await.unwrap(); // pos 2: only Y
        log_frozen.append_leaf(b"d").await.unwrap(); // pos 3: only Y

        // At size 4, X is frozen (not in active_roots).  An empty path
        // suffices — the committed timeline carries the inactivity claim.
        let coupling_f = log_frozen.coupling_proof_at(4).await.unwrap();
        let cr_f = log_frozen.combined_root_at(0, 4).await.unwrap();
        let active_algs_f = neml::committed_active_algs(&coupling_f.alg_epochs, 4);

        // X is inactive at pos 3 (beyond its epoch [1,2)).
        let ok_frozen = neml::verify_inactivity_with_coupling(
            &Sha256Hasher, 1, 3, 4, 2,
            &[], &coupling_f, &cr_f, &active_algs_f, config,
        );
        assert!(ok_frozen, "frozen-alg inactivity proof (empty path) must verify");

        // Non-empty path for a frozen alg must fail.
        let dummy_path = vec![neml::ProofStep { siblings: vec![vec![0u8; 32]], position: 0 }];
        let fail_frozen = neml::verify_inactivity_with_coupling(
            &Sha256Hasher, 1, 3, 4, 2,
            &dummy_path, &coupling_f, &cr_f, &active_algs_f, config,
        );
        assert!(!fail_frozen, "non-empty path for frozen alg must fail");
    });
}

/// Epoch evolution: a payload's timeline at a later size must be an
/// append-only extension of an earlier one; a rewritten boundary fails.
#[test]
fn test_epoch_evolution() {
    smol::block_on(async {
        let log_id = [2u8; 32];
        let cfg = TreeConfig { log_arity: 2 };

        let mut log = NaryMerkleLog::new(
            MemoryStorage::new(), Box::new(Sha256Hasher), cfg,
        ).await.unwrap();
        log.add_algorithm(1, Box::new(Sha256Hasher)).await.unwrap();
        log.append_leaf(b"x").await.unwrap();
        log.append_leaf(b"y").await.unwrap();

        let p1 = log.audit_payload_at(log_id, 1).await.unwrap();
        let p2 = log.audit_payload_at(log_id, 2).await.unwrap();

        // Forward evolution passes.
        assert!(neml::verify_epoch_evolution(&p1.alg_epochs, 1, &p2.alg_epochs, 2),
            "forward epoch evolution must pass");

        // A rewritten activation boundary must be rejected.
        let mut tampered = p1.alg_epochs.clone();
        // Shift alg 1's activation from 0 to 1 — this is a rewrite, not
        // an allowed extension, so evolution must fail.
        tampered[1].1 = vec![(1u64, u64::MAX)];
        assert!(!neml::verify_epoch_evolution(&tampered, 1, &p2.alg_epochs, 2),
            "rewritten activation boundary must fail evolution check");
    });
}

// ── Deterministic recovery tests ──────────────────────────────────────────────

/// Persisted log_meta makes from_storage return identical count/root
/// regardless of how many times it is called on the same storage.
#[test]
fn test_from_storage_deterministic_repeated() {
    smol::block_on(async {
        let mut log = NaryMerkleLog::new(
            MemoryStorage::new(),
            Box::new(Sha256Hasher),
            TreeConfig { log_arity: 2 },
        )
        .await
        .unwrap();
        log.add_algorithm(1, Box::new(Sha256Hasher)).await.unwrap();
        log.add_algorithm(2, Box::new(Sha256Hasher)).await.unwrap();

        // Build a subtree log; deactivate alg 1, then reactivate it.
        let st = Subtree::Leaf(b"x".to_vec());
        log.append_subtree(&st).await.unwrap();
        log.remove_algorithm(1).await.unwrap();
        log.append_subtree(&st).await.unwrap();
        log.resume_algorithm(1).await.unwrap();
        log.append_subtree(&st).await.unwrap();

        let expected_count = log.count();
        let expected_root = log.root_for(0).unwrap();
        let storage = log.into_storage();

        // Call from_storage several times and assert identity.
        for _ in 0..5 {
            let r = NaryMerkleLog::from_storage(
                storage.clone(),
                vec![
                    (0, Box::new(Sha256Hasher)),
                    (1, Box::new(Sha256Hasher)),
                    (2, Box::new(Sha256Hasher)),
                ],
            )
            .await
            .unwrap();
            assert_eq!(r.count(), expected_count, "count must be identical each load");
            assert_eq!(
                r.root_for(0).unwrap(),
                expected_root,
                "root must be identical each load"
            );
            assert_eq!(r.kind(), neml::LogKind::Subtree);
        }
    });
}

/// LogKind is persisted and restored correctly for both flat and subtree logs.
#[test]
fn test_log_kind_persisted_and_restored() {
    smol::block_on(async {
        // Flat log.
        {
            let mut log = NaryMerkleLog::new(
                MemoryStorage::new(),
                Box::new(Sha256Hasher),
                TreeConfig::default(),
            )
            .await
            .unwrap();
            log.append_leaf(b"a").await.unwrap();
            log.append_leaf(b"b").await.unwrap();
            let expected_root = log.root_for(0).unwrap();
            let storage = log.into_storage();

            let r = NaryMerkleLog::from_storage(storage, vec![(0, Box::new(Sha256Hasher))])
                .await
                .unwrap();
            assert_eq!(r.kind(), neml::LogKind::Flat);
            assert_eq!(r.count(), 2);
            assert_eq!(r.size(), 2);
            assert_eq!(r.subtree_count(), 0);
            assert_eq!(r.root_for(0).unwrap(), expected_root);
        }

        // Subtree log.
        {
            let st = Subtree::Node(vec![
                Subtree::Leaf(b"p".to_vec()),
                Subtree::Leaf(b"q".to_vec()),
            ]);
            let mut log = NaryMerkleLog::new(
                MemoryStorage::new(),
                Box::new(Sha256Hasher),
                TreeConfig::default(),
            )
            .await
            .unwrap();
            log.append_subtree(&st).await.unwrap();
            log.append_subtree(&st).await.unwrap();
            let expected_root = log.root_for(0).unwrap();
            let storage = log.into_storage();

            let r = NaryMerkleLog::from_storage(storage, vec![(0, Box::new(Sha256Hasher))])
                .await
                .unwrap();
            assert_eq!(r.kind(), neml::LogKind::Subtree);
            assert_eq!(r.count(), 2);
            assert_eq!(r.subtree_count(), 2);
            assert_eq!(r.size(), 0);
            assert_eq!(r.root_for(0).unwrap(), expected_root);
        }
    });
}

/// Mixed-append rejection: flat-leaf log rejects subsequent subtree append.
#[test]
fn test_mixed_append_leaf_then_subtree_rejected() {
    smol::block_on(async {
        let mut log = NaryMerkleLog::new(
            MemoryStorage::new(),
            Box::new(Sha256Hasher),
            TreeConfig::default(),
        )
        .await
        .unwrap();
        log.append_leaf(b"a").await.unwrap();
        let result = log.append_subtree(&Subtree::Leaf(b"b".to_vec())).await;
        assert!(result.is_err(), "subtree append after leaf append must fail");
    });
}

/// Mixed-append rejection: subtree log rejects subsequent flat-leaf append.
#[test]
fn test_mixed_append_subtree_then_leaf_rejected() {
    smol::block_on(async {
        let mut log = NaryMerkleLog::new(
            MemoryStorage::new(),
            Box::new(Sha256Hasher),
            TreeConfig::default(),
        )
        .await
        .unwrap();
        log.append_subtree(&Subtree::Leaf(b"a".to_vec())).await.unwrap();
        let result = log.append_leaf(b"b").await;
        assert!(result.is_err(), "leaf append after subtree append must fail");
    });
}

/// Cross-replica: two independently-constructed MemoryStorage instances with
/// the same logical data recover identical size and root.
#[test]
fn test_cross_replica_identical_recovery() {
    smol::block_on(async {
        // Build the reference log.
        let mut log_a = NaryMerkleLog::new(
            MemoryStorage::new(),
            Box::new(Sha256Hasher),
            TreeConfig { log_arity: 2 },
        )
        .await
        .unwrap();
        log_a.add_algorithm(1, Box::new(Sha256Hasher)).await.unwrap();

        let st = Subtree::Leaf(b"data".to_vec());
        log_a.append_subtree(&st).await.unwrap();
        log_a.remove_algorithm(1).await.unwrap();
        log_a.append_subtree(&st).await.unwrap();

        let storage_a = log_a.into_storage();

        // Clone the storage — simulates an independent replica with identical bytes.
        let storage_b = storage_a.clone();

        let r_a = NaryMerkleLog::from_storage(
            storage_a,
            vec![(0, Box::new(Sha256Hasher)), (1, Box::new(Sha256Hasher))],
        )
        .await
        .unwrap();

        let r_b = NaryMerkleLog::from_storage(
            storage_b,
            vec![(0, Box::new(Sha256Hasher)), (1, Box::new(Sha256Hasher))],
        )
        .await
        .unwrap();

        assert_eq!(r_a.count(), r_b.count(), "replicas must agree on count");
        assert_eq!(
            r_a.root_for(0).unwrap(),
            r_b.root_for(0).unwrap(),
            "replicas must agree on root"
        );
        assert_eq!(r_a.kind(), r_b.kind(), "replicas must agree on kind");
    });
}

/// Legacy-probe gap correctness: when no log_meta is present, the linear scan
/// correctly stops at the first absent node even if gaps exist between
/// activation epochs (i.e. the binary search assumption was violated).
#[test]
fn test_legacy_probe_gap_correctness() {
    smol::block_on(async {
        // Build a 3-append subtree log with alg 0 and alg 1, where alg 1
        // is deactivated at position 1 (creating a gap at index 1 for alg 1).
        let mut log = NaryMerkleLog::new(
            MemoryStorage::new(),
            Box::new(Sha256Hasher),
            TreeConfig { log_arity: 2 },
        )
        .await
        .unwrap();
        log.add_algorithm(1, Box::new(Sha256Hasher)).await.unwrap();

        let st = Subtree::Leaf(b"y".to_vec());
        log.append_subtree(&st).await.unwrap(); // index 0 — both algs active
        log.remove_algorithm(1).await.unwrap(); // freeze alg 1 at 1
        log.append_subtree(&st).await.unwrap(); // index 1 — only alg 0 active
        log.resume_algorithm(1).await.unwrap(); // reactivate alg 1 at 2
        log.append_subtree(&st).await.unwrap(); // index 2 — both algs active

        let expected_count = log.count();
        let expected_root = log.root_for(0).unwrap();

        // Remove log_meta to simulate a legacy store; recovery must use probe.
        let mut storage = log.into_storage();
        storage.log_meta = None;

        let r = NaryMerkleLog::from_storage(
            storage,
            vec![(0, Box::new(Sha256Hasher)), (1, Box::new(Sha256Hasher))],
        )
        .await
        .unwrap();

        assert_eq!(r.count(), expected_count, "legacy probe must recover correct count");
        assert_eq!(
            r.root_for(0).unwrap(),
            expected_root,
            "legacy probe must recover correct root"
        );
    });
}
