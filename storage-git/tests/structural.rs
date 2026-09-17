//! Structural tests: SG9.
//!
//! Retired from this file, with justification (per the merge-gate dispatch,
//! `.ledger/deposits/git-backend/lead-maintainer/storage-git-tip-tree-gate.md`):
//! `sg4_sg10_materialized_vs_opaque_leaf_node`, `sg5_entry_modes`, and
//! `sg12_sg16_golden_bytes` each navigated `peaks/00/00` (via the now-
//! removed `find`/`FindEntryId` helpers) to reach a node, and the first of
//! the three asserted the materialized-vs-opaque `digest`/`leaf`/`hex(c,2)`
//! shape directly. The ratified key-derived layout ("THE DESIGN",
//! `spike-report.md` and its prototype `storage-git-keyed/`) eliminates
//! both premises at once ("no peak/child wiring, no decomposition, no
//! opacity bookkeeping anywhere"): there is no `peaks/` path to descend and
//! no materialized/opaque node shape left to assert. Their remaining,
//! layout-agnostic content is already covered elsewhere without peak
//! navigation: entry-mode canonicality by
//! `acceptance_layout.rs::sg5_entry_modes_are_canonical_blob_and_tree`
//! (a full recursive walk from the tip, independent of any particular
//! subtree shape); `meta`'s fixed 11-byte encoding (SG12) by
//! `acceptance_encodings.rs::meta_blob_has_one_fixed_shape_regardless_of_resume_history`;
//! leaf byte-identity (SG16) by
//! `acceptance_encodings.rs::sg16_leaf_blob_is_byte_identical_to_input`,
//! rewritten there against the new key-derived leaf path instead of
//! `peaks/00/00`. `sg9_purity_under_reordering` (below) is kept: it never
//! navigates `peaks/` at all, comparing only the two runs' top-level tip
//! tree ids directly.

mod common;

use common::{WideHasher, init_repo};
use gix::hash::Kind as HashKind;
use polydigest::{NaryMerkleLog, TreeConfig};
use storage_git::GitStorage;

fn checkpoint_tree(repo: &gix::ThreadSafeRepository, staging_ref: &str) -> gix::ObjectId {
    let local = repo.to_thread_local();
    let r = local.find_reference(staging_ref).unwrap();
    r.target().id().to_owned()
}

/// SG9: `C(n)`'s object id does not depend on insertion order among
/// operations that reach the same logical state -- here, two algorithm
/// registrations at the same size, in either order.
#[test]
fn sg9_purity_under_reordering() {
    smol::block_on(async {
        let (_dir, repo_a) = init_repo(HashKind::Sha1);
        let staging_a = "refs/eml/storage/a/staging";
        let storage_a = GitStorage::new(repo_a.clone(), staging_a, 2).unwrap();
        let mut log_a =
            NaryMerkleLog::new(storage_a, Box::new(WideHasher), TreeConfig { arity: 2 })
                .await
                .unwrap();
        log_a.add_algorithm(7, Box::new(WideHasher)).await.unwrap();
        log_a.add_algorithm(9, Box::new(WideHasher)).await.unwrap();
        log_a.append_leaf(b"x").await.unwrap();
        let _ = log_a.into_storage();

        let (_dir, repo_b) = init_repo(HashKind::Sha1);
        let staging_b = "refs/eml/storage/b/staging";
        let storage_b = GitStorage::new(repo_b.clone(), staging_b, 2).unwrap();
        let mut log_b =
            NaryMerkleLog::new(storage_b, Box::new(WideHasher), TreeConfig { arity: 2 })
                .await
                .unwrap();
        // Same two algorithms, reversed registration order.
        log_b.add_algorithm(9, Box::new(WideHasher)).await.unwrap();
        log_b.add_algorithm(7, Box::new(WideHasher)).await.unwrap();
        log_b.append_leaf(b"x").await.unwrap();
        let _ = log_b.into_storage();

        let tree_a = checkpoint_tree(&repo_a, staging_a);
        let tree_b = checkpoint_tree(&repo_b, staging_b);
        assert_eq!(
            tree_a, tree_b,
            "reordered-but-equivalent state must yield identical C(n)"
        );
    });
}
