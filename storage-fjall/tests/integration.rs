use polydigest::{Hasher, NaryMerkleLog, NodeWrite, Storage, TreeConfig, WriteOp};
use sha2::{Digest, Sha256};
use storage_fjall::FjallStorage;
use tempfile::tempdir;

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
fn test_fjall_storage_basic_ops() {
    smol::block_on(async {
        let dir = tempdir().unwrap();
        let mut storage = FjallStorage::open(dir.path()).unwrap();

        // Init
        assert_eq!(storage.len().await.unwrap(), 0);

        // Leaf ops, one `AppendLeaf` op each; the second carries an
        // otherwise-unrelated node write too -- `nodes` is not required to
        // sit at the op's own `at` position, only to land atomically with it.
        storage
            .apply(&[WriteOp::AppendLeaf {
                at: 0,
                data: b"leaf0",
                nodes: &[],
            }])
            .await
            .unwrap();
        storage
            .apply(&[WriteOp::AppendLeaf {
                at: 1,
                data: b"leaf1",
                nodes: &[NodeWrite {
                    alg_id: 0,
                    left: 100,
                    height: 0,
                    hash: b"hash100",
                }],
            }])
            .await
            .unwrap();
        assert_eq!(storage.len().await.unwrap(), 2);
        assert_eq!(storage.get_leaf(0).await.unwrap(), b"leaf0");
        assert_eq!(storage.get_leaf(1).await.unwrap(), b"leaf1");

        // Node ops
        assert_eq!(
            storage.get_node(0, 100, 0).await.unwrap().unwrap(),
            b"hash100"
        );
        assert!(storage.get_node(0, 999, 0).await.unwrap().is_none());

        // Metadata ops
        let epochs = vec![(0, 10), (15, 20)];
        storage
            .apply(&[WriteOp::AddAlgorithm {
                alg_id: 0,
                epochs: &epochs,
            }])
            .await
            .unwrap();
        let loaded = storage.load_algorithm_metas().await.unwrap();
        assert_eq!(loaded.len(), 1);
        assert_eq!(loaded[0].0, 0);
        assert_eq!(loaded[0].1, epochs);
    });
}

#[test]
fn test_fjall_log_integration_and_recovery() {
    smol::block_on(async {
        let dir = tempdir().unwrap();

        // Step 1: Build a log and write elements
        let root0;
        let root1;
        {
            let storage = FjallStorage::open(dir.path()).unwrap();
            let config = TreeConfig { arity: 2 };
            let mut log = NaryMerkleLog::new(storage, Box::new(Sha256Hasher), config)
                .await
                .unwrap();

            log.add_algorithm(1, Box::new(Sha256Hasher)).await.unwrap();

            log.append_leaf(b"hello").await.unwrap();
            log.append_leaf(b"world").await.unwrap();

            log.remove_algorithm(1).await.unwrap();

            log.append_leaf(b"rust").await.unwrap();

            root0 = log.root_for(0).unwrap();
            root1 = log.root_for(1).unwrap();

            assert_eq!(log.size(), 3);
        }

        // Step 2: Open a new log with the same storage and check recovery
        {
            let storage = FjallStorage::open(dir.path()).unwrap();
            let reconstructed = NaryMerkleLog::from_storage(
                storage,
                vec![(0, Box::new(Sha256Hasher)), (1, Box::new(Sha256Hasher))],
            )
            .await
            .unwrap();

            assert_eq!(reconstructed.size(), 3);
            assert_eq!(reconstructed.root_for(0).unwrap(), root0);
            assert_eq!(reconstructed.root_for(1).unwrap(), root1);
        }
    });
}

#[test]
fn test_fjall_metadata_corruption() {
    smol::block_on(async {
        let dir = tempdir().unwrap();

        // 1. Write corrupted key length (< 8 bytes)
        {
            let db = fjall::Database::builder(dir.path()).open().unwrap();
            let metadata = db
                .keyspace("eml_metadata", fjall::KeyspaceCreateOptions::default)
                .unwrap();
            metadata.insert(b"short", [0; 16]).unwrap();
        }

        let storage = FjallStorage::open(dir.path()).unwrap();
        let metas_res = storage.load_algorithm_metas().await;
        assert!(metas_res.is_err());

        // Try from_storage
        let log_res = NaryMerkleLog::from_storage(storage, vec![(0, Box::new(Sha256Hasher))]).await;
        assert!(log_res.is_err());
    });

    smol::block_on(async {
        let dir = tempdir().unwrap();

        // 2. Write corrupted value length (not a multiple of 16)
        {
            let db = fjall::Database::builder(dir.path()).open().unwrap();
            let metadata = db
                .keyspace("eml_metadata", fjall::KeyspaceCreateOptions::default)
                .unwrap();
            metadata.insert(0u64.to_be_bytes(), [0; 15]).unwrap();
        }

        let storage = FjallStorage::open(dir.path()).unwrap();
        let metas_res = storage.load_algorithm_metas().await;
        assert!(metas_res.is_err());

        // Try from_storage
        let log_res = NaryMerkleLog::from_storage(storage, vec![(0, Box::new(Sha256Hasher))]).await;
        assert!(log_res.is_err());
    });
}

// FjallStorage is intentionally not Clone; single-writer ownership is
// enforced at compile time.  The concurrent-clone race test that existed
// here was testing the unsound behaviour we eliminated; it is removed.

#[test]
fn test_fjall_storage_scoped_prefix_isolation() {
    smol::block_on(async {
        let dir = tempdir().unwrap();
        let db = fjall::Database::builder(dir.path()).open().unwrap();

        let mut tenant_a = FjallStorage::with_database_scoped(db.clone(), "tenant_a").unwrap();
        let mut tenant_b = FjallStorage::with_database_scoped(db, "tenant_b").unwrap();

        // Same positional keys (leaf index 0, node (alg_id=1, left=2, height=3),
        // alg_id 7) written through two independently-scoped instances sharing
        // one physical database must not collide.
        tenant_a
            .apply(&[WriteOp::AppendLeaf {
                at: 0,
                data: b"a-leaf-0",
                nodes: &[NodeWrite {
                    alg_id: 1,
                    left: 2,
                    height: 3,
                    hash: b"a-node",
                }],
            }])
            .await
            .unwrap();
        tenant_b
            .apply(&[WriteOp::AppendLeaf {
                at: 0,
                data: b"b-leaf-0",
                nodes: &[NodeWrite {
                    alg_id: 1,
                    left: 2,
                    height: 3,
                    hash: b"b-node",
                }],
            }])
            .await
            .unwrap();
        assert_eq!(tenant_a.get_leaf(0).await.unwrap(), b"a-leaf-0");
        assert_eq!(tenant_b.get_leaf(0).await.unwrap(), b"b-leaf-0");
        assert_eq!(
            tenant_a.get_node(1, 2, 3).await.unwrap().unwrap(),
            b"a-node"
        );
        assert_eq!(
            tenant_b.get_node(1, 2, 3).await.unwrap().unwrap(),
            b"b-node"
        );

        let epochs_a = vec![(0, 5)];
        let epochs_b = vec![(10, 20)];
        tenant_a
            .apply(&[WriteOp::AddAlgorithm {
                alg_id: 7,
                epochs: &epochs_a,
            }])
            .await
            .unwrap();
        tenant_b
            .apply(&[WriteOp::AddAlgorithm {
                alg_id: 7,
                epochs: &epochs_b,
            }])
            .await
            .unwrap();
        assert_eq!(
            tenant_a.load_algorithm_metas().await.unwrap(),
            vec![(7, epochs_a)]
        );
        assert_eq!(
            tenant_b.load_algorithm_metas().await.unwrap(),
            vec![(7, epochs_b)]
        );
    });
}

#[test]
fn test_fjall_storage_scoped_prefix_rejects_empty() {
    let dir = tempdir().unwrap();
    let db = fjall::Database::builder(dir.path()).open().unwrap();
    assert!(FjallStorage::with_database_scoped(db, "").is_err());
}

/// A sparse, out-of-order leaf write is no longer a legal `AppendLeaf` op:
/// `WriteOp::AppendLeaf::at` is documented as "the append-only position
/// being written (== the count before this op)", matching
/// `storage-git::GitStorage`'s own in-order requirement (departure 2,
/// `storage-git/src/lib.rs`). What used to be `FjallStorage`'s own more
/// permissive standalone `store_leaf` -- accepting any index, sparse or
/// out-of-order -- is retired along with the standalone method itself:
/// there is now exactly one way to write, and that way is append-only.
#[test]
fn test_fjall_out_of_order_append_is_refused() {
    smol::block_on(async {
        let dir = tempdir().unwrap();
        let mut storage = FjallStorage::open(dir.path()).unwrap();

        let result = storage
            .apply(&[WriteOp::AppendLeaf {
                at: 10,
                data: b"index10",
                nodes: &[],
            }])
            .await;
        assert!(
            result.is_err(),
            "an AppendLeaf at position 10 on a fresh (append_count == 0) store must be refused, \
             not silently accepted as a sparse write"
        );
    });
}
