//! [NO STORED KIND] Head's ruling, 2026-09-17, requirement A/(2): a log's
//! kind is derived from content, never persisted. `storage-fjall`'s
//! metadata keyspace therefore carries the append count alone -- 8 bytes,
//! never 9 -- under its reserved log-metadata key: no kind byte.
//!
//! Passing at HEAD: `FjallStorage`'s write path already stores the
//! append count alone under `LOG_META_KEY` -- an 8-byte value, no kind byte
//! (`storage-fjall/src/lib.rs:15-17`). Checked at the raw keyspace-value-length
//! level, independent of `FjallStorage`'s own `append_count` decoding.
//! Demonstrated by mutation: reverting the write path to the old
//! `write_batch`'s `log_meta: Option<(u64, u8)>` shape (a 9-byte value with
//! a trailing kind byte) turns this red immediately.

use polydigest::{Hasher, NaryMerkleLog, TreeConfig};
use sha2::{Digest, Sha256};
use storage_fjall::FjallStorage;
use tempfile::tempdir;

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

/// The log-metadata value's raw byte length, read directly off the
/// `eml_metadata` keyspace -- independent of `FjallStorage::append_count`'s
/// own decoding (which is exactly the function under scrutiny).
fn log_meta_value_len(dir: &std::path::Path) -> usize {
    const LOG_META_KEY: &[u8; 9] = b"_logmeta_";
    let db = fjall::Database::builder(dir).open().unwrap();
    let metadata = db
        .keyspace("eml_metadata", fjall::KeyspaceCreateOptions::default)
        .unwrap();
    metadata
        .get(LOG_META_KEY)
        .unwrap()
        .expect("log-metadata entry must exist after a write")
        .len()
}

/// [NO STORED KIND] The log-metadata value is exactly 8 bytes (the append
/// count alone) after a genesis write -- demonstrated by mutation:
/// reverting `FjallStorage`'s write path to a 9-byte, kind-carrying shape
/// turns this red.
#[test]
fn log_meta_value_carries_no_kind_byte_at_genesis() {
    smol::block_on(async {
        let dir = tempdir().unwrap();
        let log = NaryMerkleLog::new(
            FjallStorage::open(dir.path()).unwrap(),
            Box::new(Sha256Hasher),
            TreeConfig { arity: 2 },
        )
        .await
        .unwrap();
        drop(log);

        assert_eq!(
            log_meta_value_len(dir.path()),
            8,
            "the log-metadata value must be exactly 8 bytes (the append count alone), no kind byte"
        );
    });
}

/// [NO STORED KIND] The log-metadata value stays 8 bytes across further
/// appends and algorithm add/remove/resume.
#[test]
fn log_meta_value_carries_no_kind_byte_across_the_lifecycle() {
    smol::block_on(async {
        let dir = tempdir().unwrap();
        let mut log = NaryMerkleLog::new(
            FjallStorage::open(dir.path()).unwrap(),
            Box::new(Sha256Hasher),
            TreeConfig { arity: 2 },
        )
        .await
        .unwrap();

        log.append_leaf(b"one").await.unwrap();
        drop(log);
        assert_eq!(log_meta_value_len(dir.path()), 8);

        let mut log = NaryMerkleLog::from_storage(
            FjallStorage::open(dir.path()).unwrap(),
            vec![(0, Box::new(Sha256Hasher) as Box<dyn Hasher>)],
        )
        .await
        .unwrap();
        log.add_algorithm(1, Box::new(Sha256Hasher)).await.unwrap();
        log.append_leaf(b"two").await.unwrap();
        log.remove_algorithm(1).await.unwrap();
        log.append_leaf(b"three").await.unwrap();
        log.resume_algorithm(1).await.unwrap();
        drop(log);
        assert_eq!(log_meta_value_len(dir.path()), 8);
    });
}
