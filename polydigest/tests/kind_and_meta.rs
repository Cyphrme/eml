//! Kind derivation and non-optional log metadata (head's ruling, 2026-09-17,
//! requirements A and B), on [`MemoryStorage`]. The `storage-git` and
//! `storage-fjall` crates carry the identical claim over their own backends
//! in `tests/kind_and_meta.rs`.
//!
//! [KIND DERIVATION] A log's kind is never stored -- it is derived, on every
//! reconstruction, from content alone: flat iff the store holds any leaf
//! (`Storage::len() > 0`), subtree iff the append count is nonzero with no
//! leaves (a resumed or subtree-appended-from-genesis log), and undecided
//! (either accepted) at count 0. This file reopens one log of each
//! provenance from storage alone and checks the recovered `kind()` matches
//! what the content implies, then checks the append-kind guards
//! (`append_leaf`/`append_subtree`'s own conflict errors) behave exactly as
//! they do on a freshly-built log of the same kind.
//!
//! [NON-OPTIONAL META] `Storage::append_count` returns a plain `u64`, never
//! `Option`: `0` for a fresh store, and the correct total after every
//! operation and after a reopen.

use polydigest::{Hasher, MemoryStorage, NaryMerkleLog, Storage, Subtree, TreeConfig};

#[derive(Debug, Clone)]
struct FixtureHasher;

impl Hasher for FixtureHasher {
    fn leaf(&self, data: &[u8]) -> Vec<u8> {
        use sha2::{Digest, Sha256};
        Sha256::digest(data).to_vec()
    }

    fn node(&self, children: &[&[u8]]) -> Vec<u8> {
        use sha2::{Digest, Sha256};
        let mut h = Sha256::new();
        for c in children {
            h.update(c);
        }
        h.finalize().to_vec()
    }

    fn empty(&self) -> Vec<u8> {
        use sha2::{Digest, Sha256};
        Sha256::digest(b"").to_vec()
    }

    fn hash(&self, data: &[u8]) -> Vec<u8> {
        use sha2::{Digest, Sha256};
        Sha256::digest(data).to_vec()
    }

    fn clone_box(&self) -> Box<dyn Hasher> {
        Box::new(self.clone())
    }
}

fn hashers(ids: impl IntoIterator<Item = u64>) -> Vec<(u64, Box<dyn Hasher>)> {
    ids.into_iter()
        .map(|id| (id, Box::new(FixtureHasher) as Box<dyn Hasher>))
        .collect()
}

async fn reopen(
    storage: MemoryStorage,
    ids: impl IntoIterator<Item = u64>,
) -> NaryMerkleLog<MemoryStorage> {
    NaryMerkleLog::from_storage(storage, hashers(ids))
        .await
        .expect("reopen from storage alone")
}

/// [KIND DERIVATION] A flat log (leaves actually appended) reopens as
/// `LogKind::Flat`: `len() > 0` is the flat signal, independent of anything
/// this log's own in-memory `kind` field ever held before it was dropped.
#[test]
fn flat_log_reopens_as_flat() {
    smol::block_on(async {
        let mut log = NaryMerkleLog::new(
            MemoryStorage::new(),
            Box::new(FixtureHasher),
            TreeConfig { arity: 2 },
        )
        .await
        .unwrap();
        for i in 0..5u32 {
            log.append_leaf(format!("leaf-{i}").as_bytes())
                .await
                .unwrap();
        }
        let expected_count = log.count();
        let expected_root = log.root();
        let storage = log.into_storage();

        assert!(
            storage.len().await.unwrap() > 0,
            "sanity: a flat log's storage must hold leaves"
        );

        let reopened = reopen(storage, [0]).await;
        assert_eq!(reopened.kind(), polydigest::LogKind::Flat);
        assert_eq!(reopened.count(), expected_count);
        assert_eq!(reopened.root(), expected_root);

        // Append-kind guard: a flat-kind log still refuses a subtree append,
        // exactly as a freshly built flat log does.
        let mut reopened = reopened;
        let err = reopened
            .append_subtree(&Subtree::Leaf(b"x".to_vec()))
            .await
            .unwrap_err();
        assert!(matches!(
            err,
            polydigest::LogError::CorruptedMetadata { .. }
        ));
    });
}

/// [KIND DERIVATION] A subtree-appended-from-genesis log (never flat,
/// `NaryMerkleLog::new` followed only by `append_subtree`) reopens as
/// `LogKind::Subtree`: a nonzero append count with `len() == 0`.
#[test]
fn subtree_from_genesis_log_reopens_as_subtree() {
    smol::block_on(async {
        let mut log = NaryMerkleLog::new(
            MemoryStorage::new(),
            Box::new(FixtureHasher),
            TreeConfig { arity: 2 },
        )
        .await
        .unwrap();
        for i in 0..4u32 {
            log.append_subtree(&Subtree::Leaf(format!("s-{i}").into_bytes()))
                .await
                .unwrap();
        }
        let expected_count = log.count();
        let expected_root = log.root();
        let storage = log.into_storage();

        assert_eq!(
            storage.len().await.unwrap(),
            0,
            "sanity: a subtree-kind log never populates the leaf keyspace"
        );
        assert!(storage.append_count().await.unwrap() > 0);

        let reopened = reopen(storage, [0]).await;
        assert_eq!(reopened.kind(), polydigest::LogKind::Subtree);
        assert_eq!(reopened.count(), expected_count);
        assert_eq!(reopened.root(), expected_root);

        let mut reopened = reopened;
        let err = reopened.append_leaf(b"x").await.unwrap_err();
        assert!(matches!(
            err,
            polydigest::LogError::CorruptedMetadata { .. }
        ));
    });
}

/// [KIND DERIVATION] A log resumed from a sealed frontier at a nonzero size
/// reopens as `LogKind::Subtree` too -- the committed past is never
/// materialized as leaves, so `len() == 0` even though `append_count` (the
/// forward appends made after resuming) is nonzero.
#[test]
fn resumed_log_reopens_as_subtree() {
    smol::block_on(async {
        let mut src = NaryMerkleLog::new(
            MemoryStorage::new(),
            Box::new(FixtureHasher),
            TreeConfig { arity: 2 },
        )
        .await
        .unwrap();
        for i in 0..3u32 {
            src.append_leaf(format!("leaf-{i}").as_bytes())
                .await
                .unwrap();
        }
        let sealed = src.seal().await.unwrap();

        let mut resumed = NaryMerkleLog::resume(&sealed, MemoryStorage::new(), hashers([0]))
            .await
            .unwrap();
        for i in 0..2u32 {
            resumed
                .append_subtree(&Subtree::Leaf(format!("fwd-{i}").into_bytes()))
                .await
                .unwrap();
        }
        let expected_count = resumed.count();
        let expected_root = resumed.root();
        let storage = resumed.into_storage();

        assert_eq!(
            storage.len().await.unwrap(),
            0,
            "sanity: a resumed log's inherited prefix and forward subtree appends never populate \
             the leaf keyspace"
        );

        let reopened = reopen(storage, [0]).await;
        assert_eq!(reopened.kind(), polydigest::LogKind::Subtree);
        assert_eq!(reopened.count(), expected_count);
        assert_eq!(reopened.root(), expected_root);
    });
}

/// [KIND DERIVATION] An empty log (`append_count == 0`) has no kind yet: the
/// derivation picks a default (Flat, per `from_storage`'s current
/// implementation) but that default is unobservable through any public
/// accessor -- both append kinds are still accepted, matching a freshly
/// constructed log's own genesis behavior.
#[test]
fn empty_log_reopens_accepting_either_append() {
    smol::block_on(async {
        let src = NaryMerkleLog::new(
            MemoryStorage::new(),
            Box::new(FixtureHasher),
            TreeConfig { arity: 2 },
        )
        .await
        .unwrap();
        let storage = src.into_storage();
        assert_eq!(storage.append_count().await.unwrap(), 0);

        // Reopened, then a flat append must succeed.
        let mut flat_leg = reopen(storage.clone(), [0]).await;
        flat_leg.append_leaf(b"a").await.unwrap();
        assert_eq!(flat_leg.kind(), polydigest::LogKind::Flat);

        // A second, independent reopen of the SAME empty content instead
        // takes the subtree branch -- content at count 0 does not commit to
        // either kind.
        let mut subtree_leg = reopen(storage, [0]).await;
        subtree_leg
            .append_subtree(&Subtree::Leaf(b"b".to_vec()))
            .await
            .unwrap();
        assert_eq!(subtree_leg.kind(), polydigest::LogKind::Subtree);
    });
}

/// [NON-OPTIONAL META] `append_count` is a plain `u64`: `0` for a fresh
/// store, and correct after every one of the five operations and after a
/// reopen -- never `Option`, so there is no legacy-probe branch to fall back
/// to (`determine_global_size` is gone, checked at compile level by
/// `api_surface.rs`).
#[test]
fn append_count_is_authoritative_after_every_operation_and_reopen() {
    smol::block_on(async {
        let mut log = NaryMerkleLog::new(
            MemoryStorage::new(),
            Box::new(FixtureHasher),
            TreeConfig { arity: 2 },
        )
        .await
        .unwrap();
        assert_eq!(log.storage().append_count().await.unwrap(), 0);

        log.append_leaf(b"a").await.unwrap();
        assert_eq!(log.storage().append_count().await.unwrap(), 1);

        log.add_algorithm(1, Box::new(FixtureHasher)).await.unwrap();
        assert_eq!(
            log.storage().append_count().await.unwrap(),
            1,
            "add_algorithm must not change the append count"
        );

        log.append_leaf(b"b").await.unwrap();
        assert_eq!(log.storage().append_count().await.unwrap(), 2);

        log.remove_algorithm(1).await.unwrap();
        assert_eq!(log.storage().append_count().await.unwrap(), 2);

        log.append_leaf(b"c").await.unwrap();
        log.resume_algorithm(1).await.unwrap();
        assert_eq!(log.storage().append_count().await.unwrap(), 3);

        let storage = log.into_storage();
        let reopened = reopen(storage, [0, 1]).await;
        assert_eq!(reopened.storage().append_count().await.unwrap(), 3);
        assert_eq!(reopened.count(), 3);
    });
}
