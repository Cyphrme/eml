//! Acceptance test for §4.4's `open_at(tree)` (SG21), from
//! `docs/specs/storage-git.md` alone.
//!
//! Rewritten in this dispatch to stop calling `tree_at` (deleted outright
//! per the head's 2026-09-16 design ruling -- storage-git never renders or
//! reconstructs a tree for a past size): each size's tree id is now
//! recorded directly off the staging ref the instant that size is reached,
//! never through a reconstruction. This is strictly stronger evidence for
//! the same SG21 claim, not a weaker substitute -- the recorded id is
//! exactly what a real checkpoint layer would have committed at that size.

#[path = "acceptance_support/mod.rs"]
mod support;

use support::{FixtureHasher, bare_repo, new_log};

/// [SG21] Reading through a view returned by `open_at(tree)` for some past
/// size `m`'s tree (recorded straight off the staging ref the moment `m`
/// was reached) MUST yield the same leaf and node values `get_leaf`/
/// `get_node` returned when the log was actually at size `m`
/// (durable-witness parity). The view MUST be independent of the
/// instance's own staging ref and current size, and MUST NOT accept or
/// perform any mutation (checked by its type: `GitReadOnlyView` exposes no
/// write method).
#[test]
fn sg21_open_at_yields_durable_witness_parity() {
    smol::block_on(async {
        let dir = tempfile::tempdir().unwrap();
        let repo = bare_repo(dir.path(), gix::hash::Kind::Sha256);
        let staging = "refs/eml/storage/sg21/staging";
        let k = 3u64;
        let mut log = new_log(&repo, staging, k, FixtureHasher::new(32)).await;

        // Record what get_leaf/get_node returned for every size m, as it
        // was actually observed at that size -- before any further append
        // could possibly move the log past it.
        //
        // Lint-only fix: a type alias for the (alg, left, height) -> digest
        // recording, requested by the dispatch that named this file's
        // clippy::type_complexity lint -- no assertion changes.
        type NodeRecording = Vec<((u64, u64, u32), Option<Vec<u8>>)>;
        struct Recorded {
            m: u64,
            tree: gix::ObjectId,
            leaves: Vec<(u64, Vec<u8>)>,
            nodes: NodeRecording,
        }
        let mut recorded = Vec::new();

        for m in 0..15u64 {
            let leaf = format!("leaf-{m}").into_bytes();
            log.append_leaf(&leaf).await.unwrap();

            let tree = support::ref_target(&repo.to_thread_local(), staging)
                .expect("staging ref must exist right after an append");
            let mut leaves = Vec::new();
            for i in 0..=m {
                leaves.push((
                    i,
                    polydigest::Storage::get_leaf(log.storage(), i)
                        .await
                        .unwrap(),
                ));
            }
            let mut nodes = Vec::new();
            for height in 0..4u32 {
                let cap = k.pow(height);
                let mut left = 0u64;
                while left <= m {
                    let value = polydigest::Storage::get_node(log.storage(), 0, left, height)
                        .await
                        .unwrap();
                    nodes.push(((0, left, height), value));
                    left += cap;
                }
            }
            recorded.push(Recorded {
                m: m + 1,
                tree,
                leaves,
                nodes,
            });
        }

        // Now open a read-only view onto each historical size and confirm
        // parity, well after the log has moved past every one of them.
        for r in &recorded {
            let view = log.storage().open_at(r.tree).unwrap();
            assert_eq!(view.tree(), r.tree);

            for (i, expected) in &r.leaves {
                let got = view.get_leaf(*i).await.unwrap();
                assert_eq!(
                    &got, expected,
                    "size {}: open_at(recorded tip).get_leaf({i}) must match the live value",
                    r.m
                );
            }
            for ((alg, left, height), expected) in &r.nodes {
                let got = view.get_node(*alg, *left, *height).await.unwrap();
                assert_eq!(
                    &got, expected,
                    "size {}: open_at(recorded tip).get_node({alg},{left},{height}) must match \
                     the live value",
                    r.m
                );
            }
        }
    });
}
