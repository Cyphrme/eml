//! Acceptance tests for `tree_at`'s historical reconstruction (SG20) over
//! logs whose leaves repeat, or whose subtrees carry the same value: eml's
//! fold collapses equal children to their shared value, so hasher
//! validation must follow that collapse rather than treating every merge as
//! a plain concatenation of its children's digests.
//!
//! Written from `docs/specs/storage-git.md` alone, against `storage-git`'s
//! public API (`GitStorage`, via the shared `new_log` fixture).

#[path = "acceptance_support/mod.rs"]
mod support;

use proptest::prelude::*;
use support::{FixtureHasher, bare_repo, new_log};

const ARITY: u64 = 2;
const WIDTH: usize = 20;

fn hasher() -> FixtureHasher {
    FixtureHasher::new(WIDTH)
}

/// Build a log over `leaves` (one byte each), recording the checkpoint tree
/// id at every size exactly as it is written -- straight off the staging
/// ref, never through `tree_at` itself, so the recorded oracle is
/// independent of the function under test. Checks `tree_at(n)` against that
/// oracle for every `n` from `0` to `leaves.len()`, both while those sizes
/// are still recent and again after four more (distinct) leaves have moved
/// the log past every one of them, so real merges have folded past
/// wherever `leaves` put equal children.
async fn check_tree_at_matches_written_history(leaves: &[u8], staging: &str) -> Result<(), String> {
    let dir = tempfile::tempdir().map_err(|e| format!("tempdir: {e}"))?;
    let repo = bare_repo(dir.path(), gix::hash::Kind::Sha256);
    let mut log = new_log(&repo, staging, ARITY, hasher()).await;
    let local = repo.to_thread_local();

    let mut written_at = vec![
        support::ref_target(&local, staging)
            .ok_or_else(|| "no checkpoint at size 0".to_string())?,
    ];
    for &b in leaves {
        log.append_leaf(&[b])
            .await
            .map_err(|e| format!("append {b}: {e:?}"))?;
        written_at.push(
            support::ref_target(&local, staging)
                .ok_or_else(|| "no checkpoint after append".to_string())?,
        );
    }

    for stage in ["before further appends", "after further appends"] {
        if stage == "after further appends" {
            for i in 0..4u32 {
                log.append_leaf(format!("tail-{i}").as_bytes())
                    .await
                    .map_err(|e| format!("append tail-{i}: {e:?}"))?;
            }
        }
        for n in 0..=leaves.len() as u64 {
            let got = log
                .storage()
                .tree_at(n)
                .map_err(|e| format!("{stage}: tree_at({n}) over leaves {leaves:?}: {e}"))?;
            if got != written_at[n as usize] {
                return Err(format!(
                    "{stage}: tree_at({n}) over leaves {leaves:?} does not equal the checkpoint \
                     actually written at size {n}"
                ));
            }
        }
    }
    Ok(())
}

/// [SG20] `tree_at`, with the correct hasher registered, MUST succeed and
/// MUST equal the tree genuinely written at that size, for logs whose
/// leaves repeat -- including where the repetition produces two equal
/// *subtrees*, not just two equal leaves.
#[test]
fn tree_at_succeeds_for_repeated_leaves() {
    smol::block_on(async {
        for (name, leaves) in [
            ("two-equal-leaves", vec![1u8, 1]),
            ("four-equal-leaves", vec![7u8, 7, 7, 7]),
            ("alternating-equal-subtrees", vec![1u8, 2, 1, 2]),
        ] {
            let staging = format!("refs/eml/storage/repeated-leaves-{name}/staging");
            if let Err(msg) = check_tree_at_matches_written_history(&leaves, &staging).await {
                panic!("{msg}");
            }
        }
    });
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    /// The same property, generalized: leaf sequences drawn from a tiny
    /// alphabet make repeated leaves -- and so equal subtrees -- frequent,
    /// not a hand-picked special case.
    #[test]
    fn tree_at_succeeds_for_leaf_sequences_from_a_small_alphabet(
        leaves in prop::collection::vec(0u8..3, 1..12)
    ) {
        let result = smol::block_on(check_tree_at_matches_written_history(
            &leaves,
            "refs/eml/storage/repeated-leaves-proptest/staging",
        ));
        if let Err(msg) = result {
            prop_assert!(false, "{msg}");
        }
    }
}
