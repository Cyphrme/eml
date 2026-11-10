//! Staged append: compute an append (and an algorithm activation in the same
//! step) in memory, read its roots and size, and only then write it with one
//! atomic `Storage::apply`.
//!
//! The claim these tests back: a caller can read the post-append root before
//! anything durable exists, and the durable write is a single final step that
//! either lands whole (and the log adopts exactly the staged state) or leaves
//! the log and the store as they were.
//!
//! The independent oracle for "the staged root is the right root" is a
//! reopen: `NaryMerkleLog::from_storage_with_config` rebuilds every
//! frontier from the stored nodes and metadata alone, so it cannot share a
//! bug with the in-memory staging path.

use polydigest::storage::MemoryStorageError;
use polydigest::{
    AlgorithmMetas, Hasher, MemoryStorage, NaryMerkleLog, Storage, TreeConfig, WriteOp,
};

#[derive(Debug, Clone)]
struct Sha256Hasher;

impl Hasher for Sha256Hasher {
    fn leaf(&self, data: &[u8]) -> Vec<u8> {
        use sha2::{Digest, Sha256};
        let mut h = Sha256::new();
        h.update([0u8]);
        h.update(data);
        h.finalize().to_vec()
    }

    fn node(&self, children: &[&[u8]]) -> Vec<u8> {
        use sha2::{Digest, Sha256};
        let mut h = Sha256::new();
        h.update([1u8]);
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

fn hasher() -> Box<dyn Hasher> {
    Box::new(Sha256Hasher)
}

/// The shape of one op handed to `apply`, recorded without its borrowed
/// payload.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum OpKind {
    AppendLeaf,
    AppendSubtree,
    AddAlgorithm,
    RemoveAlgorithm,
    ResumeAlgorithm,
    SeedFrontier,
}

/// A `MemoryStorage` that records every `apply` call (the op kinds, in
/// order) and can be told to refuse the next one.
#[derive(Debug, Default, Clone)]
struct Recording {
    inner: MemoryStorage,
    calls: Vec<Vec<OpKind>>,
    fail_next: bool,
}

impl Storage for Recording {
    type Error = MemoryStorageError;

    async fn get_leaf(&self, index: u64) -> Result<Vec<u8>, Self::Error> {
        self.inner.get_leaf(index).await
    }

    async fn len(&self) -> Result<u64, Self::Error> {
        self.inner.len().await
    }

    async fn get_node(
        &self,
        alg_id: u64,
        left: u64,
        height: u32,
    ) -> Result<Option<Vec<u8>>, Self::Error> {
        self.inner.get_node(alg_id, left, height).await
    }

    async fn load_algorithm_metas(&self) -> Result<AlgorithmMetas, Self::Error> {
        self.inner.load_algorithm_metas().await
    }

    async fn append_count(&self) -> Result<u64, Self::Error> {
        self.inner.append_count().await
    }

    async fn apply(&mut self, ops: &[WriteOp<'_>]) -> Result<(), Self::Error> {
        self.calls.push(
            ops.iter()
                .map(|op| match op {
                    WriteOp::AppendLeaf { .. } => OpKind::AppendLeaf,
                    WriteOp::AppendSubtree { .. } => OpKind::AppendSubtree,
                    WriteOp::AddAlgorithm { .. } => OpKind::AddAlgorithm,
                    WriteOp::RemoveAlgorithm { .. } => OpKind::RemoveAlgorithm,
                    WriteOp::ResumeAlgorithm { .. } => OpKind::ResumeAlgorithm,
                    WriteOp::SeedFrontier { .. } => OpKind::SeedFrontier,
                })
                .collect(),
        );
        if std::mem::take(&mut self.fail_next) {
            return Err(MemoryStorageError::InvalidOperation(
                "injected apply failure".to_string(),
            ));
        }
        self.inner.apply(ops).await
    }
}

/// Everything durable in the store, in a comparable form: leaves, sorted
/// nodes, sorted algorithm metas, append count.
type StoreState = (
    Vec<Vec<u8>>,
    Vec<((u64, u64, u32), Vec<u8>)>,
    Vec<(u64, Vec<(u64, u64)>)>,
    u64,
);

fn store_state(s: &MemoryStorage) -> StoreState {
    let mut nodes: Vec<_> = s.nodes.iter().map(|(k, v)| (*k, v.clone())).collect();
    nodes.sort();
    let mut metas: Vec<_> = s
        .algorithm_metas
        .iter()
        .map(|(k, v)| (*k, v.clone()))
        .collect();
    metas.sort();
    (s.leaves.clone(), nodes, metas, s.count)
}

async fn log_with(arity: u64, leaves: u64) -> NaryMerkleLog<Recording> {
    let mut log = NaryMerkleLog::new(Recording::default(), hasher(), TreeConfig { arity })
        .await
        .unwrap();
    for i in 0..leaves {
        log.append_leaf(format!("leaf-{i}").as_bytes())
            .await
            .unwrap();
    }
    log.storage_mut().calls.clear();
    log
}

/// Reopen the log's store from durable state alone: the oracle.
async fn reopen(log: &NaryMerkleLog<Recording>, ids: &[u64]) -> NaryMerkleLog<Recording> {
    let hashers = ids.iter().map(|&id| (id, hasher())).collect();
    NaryMerkleLog::from_storage_with_config(log.storage().clone(), hashers, *log.config())
        .await
        .unwrap()
}

/// Staging writes nothing, and the staged values are the committed ones.
///
/// Across arities 2 and 3 and every size up to 12 (so every carry depth
/// the schedule produces at those sizes), with and without activating a
/// new algorithm in the same step: staging issues zero `apply` calls;
/// dropping the `Staged` leaves size, every root and the store byte-for-byte
/// unchanged; and the staged root per algorithm and staged size equal what
/// a reopen of the committed store reports.
///
/// Red if staging writes anything, if dropping a `Staged` leaks state into
/// the log, or if the staged root differs from the committed one.
#[test]
fn staging_writes_nothing_and_predicts_the_committed_root() {
    smol::block_on(async {
        for arity in [2u64, 3] {
            for n in 0..12u64 {
                for activate in [false, true] {
                    let mut log = log_with(arity, n).await;
                    let before_size = log.size();
                    let before_root = log.root_for(0).unwrap();
                    let before_store = store_state(&log.storage().inner);

                    let mut staged = log.stage();
                    if activate {
                        staged.add_algorithm(7, hasher()).unwrap();
                    }
                    staged.append_leaf(b"next").unwrap();
                    let staged_size = staged.size();
                    let staged_root0 = staged.root_for(0).unwrap();
                    let staged_root7 = staged.root_for(7).ok();
                    assert_eq!(log.storage().calls.len(), 0, "staging wrote");
                    assert_eq!(staged_size, n + 1);
                    assert_eq!(staged_root7.is_some(), activate);

                    drop(staged);
                    assert_eq!(log.size(), before_size);
                    assert_eq!(log.root_for(0).unwrap(), before_root);
                    assert!(log.root_for(7).is_err());
                    assert_eq!(store_state(&log.storage().inner), before_store);
                    assert_eq!(log.storage().calls.len(), 0, "dropping wrote");

                    // Stage again and commit; the reopen is the oracle.
                    let mut staged = log.stage();
                    if activate {
                        staged.add_algorithm(7, hasher()).unwrap();
                    }
                    staged.append_leaf(b"next").unwrap();
                    log.commit(staged).await.unwrap();

                    let ids: &[u64] = if activate { &[0, 7] } else { &[0] };
                    let oracle = reopen(&log, ids).await;
                    assert_eq!(oracle.size(), staged_size);
                    assert_eq!(oracle.root_for(0).unwrap(), staged_root0);
                    if let Some(r7) = staged_root7 {
                        assert_eq!(oracle.root_for(7).unwrap(), r7);
                    }
                }
            }
        }
    });
}

/// Commit is exactly one `apply` carrying every staged op, and the log
/// adopts the staged state.
///
/// Red if commit splits activation and append into two writes, or if the
/// live root or size after commit differs from what the `Staged` reported.
#[test]
fn commit_is_one_apply_and_adopts_the_staged_state() {
    smol::block_on(async {
        let mut log = log_with(2, 5).await;
        let mut staged = log.stage();
        staged.add_algorithm(7, hasher()).unwrap();
        staged.append_leaf(b"next").unwrap();
        let (size, r0, r7) = (
            staged.size(),
            staged.root_for(0).unwrap(),
            staged.root_for(7).unwrap(),
        );

        log.commit(staged).await.unwrap();

        assert_eq!(
            log.storage().calls,
            vec![vec![OpKind::AddAlgorithm, OpKind::AppendLeaf]]
        );
        assert_eq!(log.size(), size);
        assert_eq!(log.root_for(0).unwrap(), r0);
        assert_eq!(log.root_for(7).unwrap(), r7);
    });
}

/// A refused `apply` leaves the in-memory log unchanged, and the next
/// append succeeds.
///
/// Red if commit adopts any staged state before the write succeeds (the
/// log would then disagree with its store, and the next append would be
/// refused by the store's position check or produce a root a reopen does
/// not reproduce).
#[test]
fn failed_commit_leaves_the_log_unchanged() {
    smol::block_on(async {
        let mut log = log_with(2, 5).await;
        let before_root = log.root_for(0).unwrap();
        let before_store = store_state(&log.storage().inner);

        let mut staged = log.stage();
        staged.add_algorithm(7, hasher()).unwrap();
        staged.append_leaf(b"next").unwrap();
        log.storage_mut().fail_next = true;
        assert!(log.commit(staged).await.is_err());

        assert_eq!(log.size(), 5);
        assert_eq!(log.root_for(0).unwrap(), before_root);
        assert!(log.root_for(7).is_err(), "activation adopted on failure");
        assert_eq!(store_state(&log.storage().inner), before_store);

        log.append_leaf(b"after").await.unwrap();
        let oracle = reopen(&log, &[0]).await;
        assert_eq!(log.size(), 6);
        assert_eq!(oracle.root_for(0).unwrap(), log.root_for(0).unwrap());
    });
}

/// Committing a `Staged` built against an older generation of the log is a
/// contract breach, caught in debug builds.
///
/// Red if commit silently applies a stale `Staged` in a debug build. Release
/// builds carry no check by design (staleness is not a runtime error); this
/// test exists only where the check does.
#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "stale")]
fn committing_a_stale_staged_panics_in_debug() {
    smol::block_on(async {
        let mut log = log_with(2, 3).await;
        let mut first = log.stage();
        first.append_leaf(b"a").unwrap();
        let mut second = log.stage();
        second.append_leaf(b"b").unwrap();
        log.commit(first).await.unwrap();
        let _ = log.commit(second).await;
    });
}
