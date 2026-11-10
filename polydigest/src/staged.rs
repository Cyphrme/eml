//! The staged append: a log mutation computed in memory, readable before
//! anything durable is written, and written later by one atomic
//! [`Storage::apply`](crate::Storage::apply).
//!
//! [`NaryMerkleLog::stage`](crate::NaryMerkleLog::stage) snapshots the log's
//! frontier state into an owned [`Staged`]; algorithm activations and
//! appends are applied to that copy only, and
//! [`NaryMerkleLog::commit`](crate::NaryMerkleLog::commit) writes every
//! staged op in one `apply` and then adopts the staged state. A caller that
//! must derive something from the post-append root (and refuse before
//! anything is durable) reads it from the `Staged` and drops it to abort.

use std::collections::HashMap;
use std::marker::PhantomData;

use cml::LogKind;
use cml::engine::{self, AlgView};
use spine::{Hasher, Subtree, evaluate, frontier_for_size};

use crate::log_error::{LogError, LogResult as Result};
use crate::storage::{NodeWrite, Storage, WriteOp};

/// A node to persist: `(alg_id, left, height, hash)`.
type OwnedNode = (u64, u64, u32, Vec<u8>);

/// Appends past this count are refused: the coordinate encoding reserves
/// the high bits of a position.
const CAPACITY: u64 = 1 << 47;

/// The log state a [`Staged`] was built from: everything a committed
/// mutation of the log changes (an append moves `count`, and may bind
/// `kind`; an algorithm activation, freeze or resume changes that
/// algorithm's epochs). Two equal generations mean no commit happened in
/// between.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Generation {
    pub(crate) count: u64,
    pub(crate) kind: LogKind,
    /// Every registered algorithm's epochs, sorted by algorithm id.
    pub(crate) epochs: Vec<(u64, Vec<(u64, u64)>)>,
}

impl Generation {
    pub(crate) fn of(count: u64, kind: LogKind, algs: &HashMap<u64, AlgView>) -> Self {
        let mut epochs: Vec<_> = algs.iter().map(|(&id, v)| (id, v.epochs.clone())).collect();
        epochs.sort_unstable_by_key(|&(id, _)| id);
        Self {
            count,
            kind,
            epochs,
        }
    }
}

/// One staged storage op, owned so the [`Staged`] borrows nothing.
#[derive(Debug, Clone)]
pub(crate) enum StagedOp {
    AddAlgorithm {
        alg_id: u64,
        epochs: Vec<(u64, u64)>,
    },
    AppendLeaf {
        at: u64,
        data: Vec<u8>,
        nodes: Vec<OwnedNode>,
    },
    AppendSubtree {
        at: u64,
        nodes: Vec<OwnedNode>,
    },
}

impl StagedOp {
    fn nodes(&self) -> &[OwnedNode] {
        match self {
            Self::AddAlgorithm { .. } => &[],
            Self::AppendLeaf { nodes, .. } | Self::AppendSubtree { nodes, .. } => nodes,
        }
    }
}

/// Write every staged op to `storage` in one atomic [`Storage::apply`].
pub(crate) async fn apply_ops<S: Storage>(
    storage: &mut S,
    ops: &[StagedOp],
) -> std::result::Result<(), S::Error> {
    // The borrowed `NodeWrite`s each `WriteOp` points into must outlive the
    // op slice, so they are built first, one vector per op.
    let node_writes: Vec<Vec<NodeWrite<'_>>> = ops
        .iter()
        .map(|op| {
            op.nodes()
                .iter()
                .map(|(alg_id, left, height, hash)| NodeWrite {
                    alg_id: *alg_id,
                    left: *left,
                    height: *height,
                    hash: hash.as_slice(),
                })
                .collect()
        })
        .collect();
    let write_ops: Vec<WriteOp<'_>> = ops
        .iter()
        .zip(&node_writes)
        .map(|(op, nodes)| match op {
            StagedOp::AddAlgorithm { alg_id, epochs } => WriteOp::AddAlgorithm {
                alg_id: *alg_id,
                epochs,
            },
            StagedOp::AppendLeaf { at, data, .. } => WriteOp::AppendLeaf {
                at: *at,
                data,
                nodes,
            },
            StagedOp::AppendSubtree { at, .. } => WriteOp::AppendSubtree { at: *at, nodes },
        })
        .collect();
    storage.apply(&write_ops).await
}

/// An append (and any algorithm activations) computed in memory against one
/// generation of a [`NaryMerkleLog`](crate::NaryMerkleLog), not yet written.
///
/// A `Staged` owns its state and borrows nothing: it holds the post-mutation
/// frontier of every algorithm, the post-mutation count and kind, the ops
/// to write, and the generation of the log it was staged from. Its
/// [`root_for`](Self::root_for) and [`size`](Self::size) report exactly what
/// the log will report once the `Staged` is committed. Dropping it is the
/// abort: nothing was written, so nothing needs undoing.
///
/// Mutations apply in call order, as the same calls on the log itself
/// would: an algorithm added before an append covers that append, one added
/// after it starts at the following position. Each mutation is
/// all-or-nothing; an `Err` leaves the `Staged` as it was.
///
/// # Contract
///
/// A `Staged` is valid only for the generation of the log it was staged
/// from: [`commit`](crate::NaryMerkleLog::commit) it to that same log
/// before any other mutation of it. Committing a `Staged` after the log
/// has moved on (another commit, append, or algorithm change), or to a
/// different log, is a contract breach. It is caught by a `debug_assert`
/// in debug builds; it is not a runtime error, and release builds do not
/// check it. Holding the log by `&mut` across stage and commit, as a
/// single-writer caller does, makes the breach impossible to write.
#[derive(Debug)]
pub struct Staged<S: Storage> {
    pub(crate) base: Generation,
    pub(crate) arity: u64,
    pub(crate) algs: HashMap<u64, AlgView>,
    pub(crate) count: u64,
    pub(crate) kind: LogKind,
    pub(crate) ops: Vec<StagedOp>,
    // Ties the `Staged` to its log's storage type (for the error type of
    // its fallible methods) without owning or borrowing an `S`; `fn() -> S`
    // keeps `Staged` `Send` and `Sync` regardless of `S`.
    pub(crate) _storage: PhantomData<fn() -> S>,
}

impl<S: Storage> Staged<S> {
    /// Stage the registration of a new algorithm, active from the staged
    /// count.
    ///
    /// # Errors
    ///
    /// Returns [`LogError::DuplicateAlgorithm`] if `alg_id` is already
    /// registered on the log or earlier in this `Staged`.
    pub fn add_algorithm(&mut self, alg_id: u64, hasher: Box<dyn Hasher>) -> Result<(), S::Error> {
        if self.algs.contains_key(&alg_id) {
            return Err(LogError::DuplicateAlgorithm(alg_id));
        }
        let epochs = vec![(self.count, u64::MAX)];
        let frontier_coords = frontier_for_size(self.count, self.arity);
        let frontier = vec![hasher.null(); frontier_coords.len()];
        self.ops.push(StagedOp::AddAlgorithm {
            alg_id,
            epochs: epochs.clone(),
        });
        self.algs.insert(
            alg_id,
            AlgView {
                hasher,
                epochs,
                frontier,
                frontier_coords,
            },
        );
        Ok(())
    }

    /// Stage one flat leaf append.
    ///
    /// # Errors
    ///
    /// Returns [`LogError`] on a kind conflict (the log already holds
    /// subtree appends), capacity overflow, or no active algorithms.
    pub fn append_leaf(&mut self, data: &[u8]) -> Result<(), S::Error> {
        // Kind binds only once an append has happened; an empty log accepts
        // either kind.
        if self.kind == LogKind::Subtree && self.count > 0 {
            return Err(LogError::CorruptedMetadata {
                alg_id: 0,
                reason: "cannot append leaf after subtree appends".to_string(),
            });
        }
        let at = self.count;
        let nodes = self.carry(|alg_id, view| {
            if view.is_active_at(at) {
                let leaf_hash = view.hasher.leaf(data);
                (leaf_hash.clone(), Some((alg_id, at, 0u32, leaf_hash)))
            } else {
                (view.hasher.null(), None)
            }
        })?;
        self.ops.push(StagedOp::AppendLeaf {
            at,
            data: data.to_vec(),
            nodes,
        });
        self.kind = LogKind::Flat;
        Ok(())
    }

    /// Stage one structured subtree append.
    ///
    /// # Errors
    ///
    /// Returns [`LogError`] on a kind conflict (the log already holds flat
    /// leaves), capacity overflow, or no active algorithms.
    pub fn append_subtree(&mut self, subtree: &Subtree) -> Result<(), S::Error> {
        if self.kind == LogKind::Flat && self.count > 0 {
            return Err(LogError::CorruptedMetadata {
                alg_id: 0,
                reason: "cannot append subtree after leaf appends".to_string(),
            });
        }
        let at = self.count;
        let nodes = self.carry(|alg_id, view| {
            if view.is_active_at(at) {
                let root_hash = evaluate(view.hasher.as_ref(), subtree);
                (root_hash.clone(), Some((alg_id, at, 0u32, root_hash)))
            } else {
                (view.hasher.null(), None)
            }
        })?;
        self.ops.push(StagedOp::AppendSubtree { at, nodes });
        self.kind = LogKind::Subtree;
        Ok(())
    }

    /// The staged raw member root for `alg_id`: what
    /// [`NaryMerkleLog::root_for`](crate::NaryMerkleLog::root_for) returns
    /// after this `Staged` is committed.
    ///
    /// # Errors
    ///
    /// Returns [`LogError::UnknownAlgorithm`] if `alg_id` is registered
    /// neither on the log nor in this `Staged`.
    pub fn root_for(&self, alg_id: u64) -> Result<Vec<u8>, S::Error> {
        let view = self
            .algs
            .get(&alg_id)
            .ok_or(LogError::UnknownAlgorithm(alg_id))?;
        Ok(engine::compute_root(view, self.arity as usize))
    }

    /// The staged number of flat leaf appends: what
    /// [`NaryMerkleLog::size`](crate::NaryMerkleLog::size) returns after
    /// this `Staged` is committed (`0` for a subtree-kind log).
    #[must_use]
    pub fn size(&self) -> u64 {
        if self.kind == LogKind::Flat {
            self.count
        } else {
            0
        }
    }

    /// The staged total number of log-level appends: what
    /// [`NaryMerkleLog::count`](crate::NaryMerkleLog::count) returns after
    /// this `Staged` is committed.
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Carry one appended item into every active algorithm's frontier.
    ///
    /// `digest_fn(alg_id, view)` returns the item's digest under that
    /// algorithm and the leaf-level node to persist, if any. The new
    /// frontiers are built on a copy and swapped in only on success, so an
    /// `Err` leaves `self` unchanged. Returns the nodes to persist.
    fn carry<F>(&mut self, digest_fn: F) -> Result<Vec<OwnedNode>, S::Error>
    where
        F: Fn(u64, &AlgView) -> (Vec<u8>, Option<OwnedNode>),
    {
        if self.count >= CAPACITY {
            return Err(LogError::CorruptedMetadata {
                alg_id: 0,
                reason: "log capacity exceeded (max 2^47 items)".to_string(),
            });
        }
        if !self.algs.values().any(AlgView::is_active) {
            return Err(LogError::NoActiveAlgorithms);
        }

        let mut algs = self.algs.clone();
        let mut nodes = Vec::new();
        for (&alg_id, view) in &mut algs {
            if !view.is_active() {
                continue;
            }
            let (digest, leaf_node) = digest_fn(alg_id, view);
            nodes.extend(leaf_node);
            // The single-algorithm frontier carry is the CML engine's; the
            // combinator drives it once per active algorithm over one store.
            engine::carry(view, alg_id, digest, self.count, self.arity, &mut nodes)?;
        }
        self.algs = algs;
        self.count += 1;
        Ok(nodes)
    }
}
