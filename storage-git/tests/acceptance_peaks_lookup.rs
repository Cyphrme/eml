//! Acceptance tests for §2.4's position-lookup algorithm (SG8), from
//! `docs/specs/storage-git.md` alone.
//!
//! Retired from this file, with justification (per the merge-gate dispatch,
//! `.ledger/deposits/git-backend/lead-maintainer/storage-git-tip-tree-gate.md`):
//! SG2's peak index (`peaks/hex(j,2)/hex(q,2)` MUST equal
//! `frontier_for_size`) is a claim about the peak-and-children hierarchy the
//! ratified key-derived layout ("THE DESIGN", `spike-report.md` and its
//! prototype `storage-git-keyed/`) eliminates outright -- there is no
//! `peaks/` tree, and no frontier-indexed group structure, left to check
//! under that design. `key_derived_layout.rs` supersedes it with the new
//! design's own indexing claim (every node/leaf path is exactly
//! `byte1-be-trim(key)`, checked against an independent set-equality
//! oracle, not a frontier-shaped one). SG8's position-lookup test below is
//! kept as-is: it drives `GitStorage`/`MemoryStorage` through their public
//! `Storage` API only and never navigates `peaks/` directly, so it carries
//! no peak-wired assumption to retire.

#[path = "acceptance_support/mod.rs"]
mod support;

use polydigest::Storage;
use support::{FixtureHasher, bare_repo, new_log, new_memory_log};

/// [SG8] For every valid `(n, i)`, the value at the position-lookup path
/// derived from `frontier_for_size` and base-`k` digit descent MUST match an
/// independent, non-git reference implementation's (`MemoryStorage`) value
/// for the same `(n, i)` — leaves and every sealed node digest.
#[test]
fn sg8_position_lookup_matches_memory_storage_reference() {
    smol::block_on(async {
        for k in [2u64, 3, 4] {
            let dir = tempfile::tempdir().unwrap();
            let repo = bare_repo(dir.path(), gix::hash::Kind::Sha256);
            let staging = format!("refs/eml/storage/sg8-k{k}/staging");
            let mut git_log = new_log(&repo, &staging, k, FixtureHasher::new(32)).await;
            let mut mem_log = new_memory_log(k, FixtureHasher::new(32)).await;

            let n_max = 30u64;
            for n in 0..n_max {
                let leaf = format!("leaf-{n}").into_bytes();
                git_log.append_leaf(&leaf).await.unwrap();
                mem_log.append_leaf(&leaf).await.unwrap();

                // Every leaf appended so far must read back identically.
                for i in 0..=n {
                    let git_leaf = git_log.storage().get_leaf(i).await.unwrap();
                    let mem_leaf = mem_log.storage().get_leaf(i).await.unwrap();
                    assert_eq!(
                        git_leaf,
                        mem_leaf,
                        "k={k}, n={}, i={i}: get_leaf mismatch",
                        n + 1
                    );
                }

                // Sweep every *aligned* (alg_id, left, height) coordinate — a
                // `T(left, height)` node is only ever created at a `left`
                // that is a multiple of `k^height` (the carry's own
                // reduction schedule; §2.4's descent likewise only ever
                // reaches aligned children) — and require agreement
                // (Some == Some with equal bytes, or both None).
                let cur = n + 1;
                for alg_id in [0u64] {
                    for height in 0..6u32 {
                        let cap = k.pow(height);
                        let mut left = 0u64;
                        while left <= cur {
                            let git_node = git_log
                                .storage()
                                .get_node(alg_id, left, height)
                                .await
                                .unwrap();
                            let mem_node = mem_log
                                .storage()
                                .get_node(alg_id, left, height)
                                .await
                                .unwrap();
                            assert_eq!(
                                git_node, mem_node,
                                "k={k}, n={cur}, alg={alg_id}, left={left}, height={height}: \
                                 get_node mismatch"
                            );
                            left += cap;
                        }
                    }
                }
            }
        }
    });
}
