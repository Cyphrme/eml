use cyphr_malt::{Hasher, MemoryStorage, NaryMerkleLog, Subtree, TreeConfig};
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

    fn null(&self) -> Vec<u8> {
        Sha256::digest([0x02]).to_vec()
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
        let mut log = NaryMerkleLog::new(storage, Box::new(hasher), config).await;

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
        let mut log = NaryMerkleLog::new(storage, Box::new(hasher), config).await;

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
        let mut log = NaryMerkleLog::new(storage, Box::new(hasher), config).await;

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
    let evaluated = cyphr_malt::evaluate(&hasher, &tree);
    let expected = Sha256::digest(b"x").to_vec();
    assert_eq!(evaluated, expected);
}

#[test]
fn test_vector_5_nested_promotion() {
    let hasher = Sha256Hasher;
    let tree = Subtree::Node(vec![Subtree::Node(vec![Subtree::Leaf(b"x".to_vec())])]);
    let evaluated = cyphr_malt::evaluate(&hasher, &tree);
    let expected = Sha256::digest(b"x").to_vec();
    assert_eq!(evaluated, expected);
}

#[test]
fn test_vector_6_subtree_append_k2() {
    smol::block_on(async {
        let hasher = Sha256Hasher;
        let storage = MemoryStorage::new();
        let config = TreeConfig { log_arity: 2 };
        let mut log = NaryMerkleLog::new(storage, Box::new(hasher), config).await;

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
    let expected = vec![
        0xdb, 0xc1, 0xb4, 0xc9, 0x00, 0xff, 0xe4, 0x8d, 0x57, 0x5b, 0x5d, 0xa5, 0xc6, 0x38, 0x04,
        0x01, 0x25, 0xf6, 0x5d, 0xb0, 0xfe, 0x3e, 0x24, 0x49, 0x4b, 0x76, 0xea, 0x98, 0x64, 0x57,
        0xd9, 0x86,
    ];
    assert_eq!(null, expected);
}

#[test]
fn test_vector_8_three_leaves_k3_ternary() {
    smol::block_on(async {
        let hasher = Sha256Hasher;
        let storage = MemoryStorage::new();
        let config = TreeConfig { log_arity: 3 };
        let mut log = NaryMerkleLog::new(storage, Box::new(hasher), config).await;

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
            let mut log = NaryMerkleLog::new(storage, Box::new(Sha256Hasher), config).await;

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
        let mut log = NaryMerkleLog::new(storage, Box::new(hasher), config).await;

        log.append_leaf(b"a").await.unwrap();
        log.append_leaf(b"b").await.unwrap();
        log.append_leaf(b"c").await.unwrap();
        log.append_leaf(b"d").await.unwrap();

        let proof = log.inclusion_proof(2, 4).await.unwrap().unwrap();
        let leaf_hash = Sha256Hasher.leaf(b"c");
        let root = log.root();
        assert!(cyphr_malt::verify_inclusion(
            &Sha256Hasher,
            &leaf_hash,
            &proof,
            &root
        ));

        let cons_proof = log.consistency_proof(2, 4).await.unwrap().unwrap();
        let old_root = {
            let mut temp_log = NaryMerkleLog::new(
                MemoryStorage::new(),
                Box::new(Sha256Hasher),
                TreeConfig { log_arity: 2 },
            )
            .await;
            temp_log.append_leaf(b"a").await.unwrap();
            temp_log.append_leaf(b"b").await.unwrap();
            temp_log.root()
        };
        assert!(cyphr_malt::verify_consistency(
            &Sha256Hasher,
            &cons_proof,
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
                let mut log = NaryMerkleLog::new(storage, Box::new(Sha256Hasher), config).await;

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
                    assert!(cyphr_malt::verify_inclusion(
                        &Sha256Hasher,
                        &leaves[idx as usize],
                        &proof,
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
                        .await;
                        for i in 0..old_size {
                            let data = format!("leaf_{}_{}", k, i).into_bytes();
                            temp_log.append_leaf(&data).await.unwrap();
                        }
                        temp_log.root()
                    };
                    if !cyphr_malt::verify_consistency(&Sha256Hasher, &cons_proof, &old_root, &root)
                    {
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
fn test_inclusion_proofs_commit_tree_mode() {
    smol::block_on(async {
        let storage = MemoryStorage::new();
        let config = TreeConfig { log_arity: 2 };
        let mut log = NaryMerkleLog::new(storage, Box::new(Sha256Hasher), config).await;

        // Commit 0: Subtree::Node([Leaf("a"), Leaf("b")])
        let commit0 = Subtree::Node(vec![
            Subtree::Leaf(b"a".to_vec()),
            Subtree::Leaf(b"b".to_vec()),
        ]);

        // Commit 1: Subtree::Node([Node([Leaf("c"), Leaf("d")]), Leaf("e")])
        let commit1 = Subtree::Node(vec![
            Subtree::Node(vec![
                Subtree::Leaf(b"c".to_vec()),
                Subtree::Leaf(b"d".to_vec()),
            ]),
            Subtree::Leaf(b"e".to_vec()),
        ]);

        log.append_subtree(&commit0).await.unwrap();
        log.append_subtree(&commit1).await.unwrap();

        let root = log.root();

        // Generate within-commit path
        let mut path = cyphr_malt::within_commit_path(&Sha256Hasher, &commit1, 1).unwrap();

        // Generate log-level inclusion proof for Commit 1
        let log_proof = log.inclusion_proof(1, 2).await.unwrap().unwrap();

        // Combine
        path.extend(log_proof.path);

        let leaf_hash = Sha256Hasher.leaf(b"d");
        let full_proof = cyphr_malt::InclusionProof {
            index: 3,
            tree_size: 5,
            path,
        };

        assert!(cyphr_malt::verify_inclusion(
            &Sha256Hasher,
            &leaf_hash,
            &full_proof,
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
        let mut log = NaryMerkleLog::new(storage, Box::new(hasher), config).await;

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
        let mut log = NaryMerkleLog::new(storage, Box::new(Sha256Hasher), config).await;
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
        let mut log = NaryMerkleLog::new(storage, Box::new(Sha256Hasher), config).await;

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
        .await;
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
        .await;
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
        .await;
        // Duplicate
        assert!(matches!(
            log.add_algorithm(0, Box::new(Sha256Hasher)).await,
            Err(cyphr_malt::error::Error::DuplicateAlgorithm(0))
        ));
        // Unknown remove
        assert!(matches!(
            log.remove_algorithm(999).await,
            Err(cyphr_malt::error::Error::UnknownAlgorithm(999))
        ));
        // Unknown resume
        assert!(matches!(
            log.resume_algorithm(999).await,
            Err(cyphr_malt::error::Error::UnknownAlgorithm(999))
        ));

        log.remove_algorithm(0).await.unwrap();
        // Already frozen
        assert!(matches!(
            log.remove_algorithm(0).await,
            Err(cyphr_malt::error::Error::FrozenAlgorithm(0))
        ));

        log.resume_algorithm(0).await.unwrap();
        // Already active
        assert!(matches!(
            log.resume_algorithm(0).await,
            Err(cyphr_malt::error::Error::AlgorithmActive(0))
        ));
    });
}

#[test]
fn test_epoch_subtree_commit_mode() {
    smol::block_on(async {
        let storage = MemoryStorage::new();
        let config = TreeConfig { log_arity: 2 };
        let mut log = NaryMerkleLog::new(storage, Box::new(Sha256Hasher), config).await;
        log.add_algorithm(1, Box::new(Sha256Hasher)).await.unwrap();

        let commit0 = Subtree::Node(vec![
            Subtree::Leaf(b"a".to_vec()),
            Subtree::Leaf(b"b".to_vec()),
        ]);
        let commit1 = Subtree::Node(vec![Subtree::Leaf(b"c".to_vec())]);

        log.append_subtree(&commit0).await.unwrap();
        log.remove_algorithm(1).await.unwrap();
        log.append_subtree(&commit1).await.unwrap();

        let root0 = log.root_for(0).unwrap();
        let root1 = log.root_for(1).unwrap();

        let storage = log.into_storage();
        let reconstructed = NaryMerkleLog::from_storage(
            storage,
            vec![(0, Box::new(Sha256Hasher)), (1, Box::new(Sha256Hasher))],
        )
        .await
        .unwrap();

        assert_eq!(reconstructed.commit_count(), 2);
        assert_eq!(reconstructed.root_for(0).unwrap(), root0);
        assert_eq!(reconstructed.root_for(1).unwrap(), root1);
    });
}

#[test]
fn test_epoch_proofs() {
    smol::block_on(async {
        let storage = MemoryStorage::new();
        let config = TreeConfig { log_arity: 2 };
        let mut log = NaryMerkleLog::new(storage, Box::new(Sha256Hasher), config).await;
        log.add_algorithm(1, Box::new(Sha256Hasher)).await.unwrap();

        log.append_leaf(b"a").await.unwrap();
        log.append_leaf(b"b").await.unwrap();
        log.remove_algorithm(1).await.unwrap();
        log.append_leaf(b"c").await.unwrap();
        log.append_leaf(b"d").await.unwrap();

        // Verify inclusion proof for algorithm 0 (fully active)
        let proof0 = log.inclusion_proof_for(0, 2, 4).await.unwrap().unwrap();
        let root0 = log.root_for(0).unwrap();
        assert!(cyphr_malt::verify_inclusion(
            &Sha256Hasher,
            &Sha256Hasher.leaf(b"c"),
            &proof0,
            &root0
        ));

        // Verify inclusion proof for algorithm 1 (frozen at size 2)
        let proof1 = log.inclusion_proof_for(1, 1, 2).await.unwrap().unwrap();
        let root1 = log.root_for(1).unwrap();
        assert!(cyphr_malt::verify_inclusion(
            &Sha256Hasher,
            &Sha256Hasher.leaf(b"b"),
            &proof1,
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
        let mut log = NaryMerkleLog::new(storage, Box::new(Sha256Hasher), config).await;

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
        // - [0, 8) height 3: node_id = (0 << 16) | 3 = 3
        // - [0, 4) height 2: node_id = (0 << 16) | 2 = 2
        // - [2, 4) height 1: node_id = (2 << 16) | 1 = 131073
        // Active node [0, 2) height 1 is also persisted (from initial appends): node_id = (0 << 16) | 1 = 1
        assert!(storage.nodes.contains_key(&(0, 3)), "mixed node [0, 8) height 3 not persisted");
        assert!(storage.nodes.contains_key(&(0, 2)), "mixed node [0, 4) height 2 not persisted");
        assert!(storage.nodes.contains_key(&(0, 131073)), "mixed node [2, 4) height 1 not persisted");
        assert!(storage.nodes.contains_key(&(0, 1)), "active node [0, 2) height 1 missing");

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
                }
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

        assert_eq!(storage.nodes.get(&(0, 3)), Some(&n_0_8));
        assert_eq!(storage.nodes.get(&(0, 2)), Some(&n_0_4));
        assert_eq!(storage.nodes.get(&(0, 131073)), Some(&n_2_4));
    });
}

#[test]
fn test_promotion_proofs_malt() {
    smol::block_on(async {
        let storage = MemoryStorage::new();
        let config = TreeConfig { log_arity: 3 };
        let mut log = NaryMerkleLog::new(storage, Box::new(Sha256Hasher), config).await;

        log.append_leaf(b"x").await.unwrap();
        let root = log.root();
        
        let proof = log.inclusion_proof_for(0, 0, 1).await.unwrap().unwrap();
        // Single leaf tree with arity 3 has empty path steps (direct leaf-to-root promotion)
        assert!(proof.path.is_empty());
        assert!(cyphr_malt::verify_inclusion(&Sha256Hasher, &Sha256Hasher.leaf(b"x"), &proof, &root));

        // Append two more leaves: size 3 (which fills one 3-ary level)
        log.append_leaf(b"y").await.unwrap();
        log.append_leaf(b"z").await.unwrap();
        let root = log.root();

        // Inclusion proof for index 2
        let proof = log.inclusion_proof_for(0, 2, 3).await.unwrap().unwrap();
        assert_eq!(proof.path.len(), 1);
        assert!(cyphr_malt::verify_inclusion(&Sha256Hasher, &Sha256Hasher.leaf(b"z"), &proof, &root));
    });
}

#[test]
fn test_subtree_consistency_proofs() {
    smol::block_on(async {
        for k in 2..=4 {
            for size in 2..=15 {
                let storage = MemoryStorage::new();
                let config = TreeConfig { log_arity: k };
                let mut log = NaryMerkleLog::new(storage, Box::new(Sha256Hasher), config).await;

                let mut subtrees = Vec::new();
                for i in 0..size {
                    let subtree = if i % 2 == 0 {
                        Subtree::Node(vec![
                            Subtree::Leaf(format!("a_{}_{}", k, i).into_bytes()),
                            Subtree::Leaf(format!("b_{}_{}", k, i).into_bytes()),
                        ])
                    } else {
                        Subtree::Node(vec![
                            Subtree::Leaf(format!("c_{}_{}", k, i).into_bytes()),
                        ])
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
                        .await;
                        for i in 0..old_size {
                            temp_log.append_subtree(&subtrees[i as usize]).await.unwrap();
                        }
                        temp_log.root()
                    };

                    assert!(
                        cyphr_malt::verify_consistency(&Sha256Hasher, &cons_proof, &old_root, &root),
                        "verify_consistency failed for subtree log: k={}, size={}, old_size={}",
                        k, size, old_size
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
            let mut log = NaryMerkleLog::new(storage, Box::new(Sha256Hasher), TreeConfig { log_arity: 2 }).await;

            let data = format!("depth_{}", depth).into_bytes();
            let subtree = make_nested_subtree(depth, &data);
            log.append_subtree(&subtree).await.unwrap();

            let root = log.root();
            let mut path = cyphr_malt::within_commit_path(&Sha256Hasher, &subtree, 0).unwrap();
            let log_proof = log.inclusion_proof(0, 1).await.unwrap().unwrap();
            path.extend(log_proof.path);

            let full_proof = cyphr_malt::InclusionProof {
                index: 0,
                tree_size: 1,
                path,
            };

            assert!(
                cyphr_malt::verify_inclusion(&Sha256Hasher, &Sha256Hasher.leaf(&data), &full_proof, &root),
                "Failed single nested leaf inclusion proof verification at depth {}", depth
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
        let subtree = Subtree::Node(vec![
            branch_left,
            Subtree::Leaf(c_data.clone()),
        ]);

        let storage = MemoryStorage::new();
        let mut log = NaryMerkleLog::new(storage, Box::new(Sha256Hasher), TreeConfig { log_arity: 3 }).await;
        log.append_subtree(&subtree).await.unwrap();
        log.append_subtree(&Subtree::Node(vec![Subtree::Leaf(b"other_leaf".to_vec())])).await.unwrap();

        let root = log.root();
        
        let test_cases = vec![
            (0, a_data),
            (1, b_data),
            (2, c_data),
        ];

        for (leaf_idx, data) in test_cases {
            let mut path = cyphr_malt::within_commit_path(&Sha256Hasher, &subtree, leaf_idx).unwrap();
            let log_proof = log.inclusion_proof(0, 2).await.unwrap().unwrap();
            path.extend(log_proof.path);

            let full_proof = cyphr_malt::InclusionProof {
                index: leaf_idx,
                tree_size: 4, // 3 leaves in subtree + 1 flat leaf = 4 total leaves
                path,
            };

            assert!(
                cyphr_malt::verify_inclusion(&Sha256Hasher, &Sha256Hasher.leaf(&data), &full_proof, &root),
                "Failed nested mixed leaf inclusion proof verification for index {}", leaf_idx
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
            let mut log = NaryMerkleLog::new(storage, Box::new(Sha256Hasher), TreeConfig { log_arity: 3 }).await;

            let s0 = Subtree::Node(vec![Subtree::Leaf(b"a".to_vec()), Subtree::Leaf(b"b".to_vec())]);
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

            let h0 = cyphr_malt::evaluate(&hasher, &s0);
            let h1 = cyphr_malt::evaluate(&hasher, &s1);
            let h2 = cyphr_malt::evaluate(&hasher, &s2);

            let expected = hasher.node(&[&h0, &h1, &h2]);
            assert_eq!(root, expected, "Root mismatch for k=3 subtree appends");
        }

        // k=4 test
        {
            let storage = MemoryStorage::new();
            let mut log = NaryMerkleLog::new(storage, Box::new(Sha256Hasher), TreeConfig { log_arity: 4 }).await;

            let s0 = Subtree::Leaf(b"a".to_vec());
            let s1 = Subtree::Leaf(b"b".to_vec());
            let s2 = Subtree::Leaf(b"c".to_vec());
            let s3 = Subtree::Leaf(b"d".to_vec());

            log.append_subtree(&s0).await.unwrap();
            log.append_subtree(&s1).await.unwrap();
            log.append_subtree(&s2).await.unwrap();
            log.append_subtree(&s3).await.unwrap();

            let root = log.root();

            let h0 = cyphr_malt::evaluate(&hasher, &s0);
            let h1 = cyphr_malt::evaluate(&hasher, &s1);
            let h2 = cyphr_malt::evaluate(&hasher, &s2);
            let h3 = cyphr_malt::evaluate(&hasher, &s3);

            let expected = hasher.node(&[&h0, &h1, &h2, &h3]);
            assert_eq!(root, expected, "Root mismatch for k=4 subtree appends");
        }
    });
}



