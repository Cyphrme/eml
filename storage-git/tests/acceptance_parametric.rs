//! Acceptance tests for §6's algorithm and object-hash parametricity
//! (SG26, SG27), from `docs/specs/storage-git.md` alone.
//!
//! SG26's other half ("no function in this crate MUST name a specific hash
//! algorithm... checked by source audit at implementation time") was
//! performed manually against `storage-git/src/` as part of this suite's
//! own preparation (`grep -rniE 'sha-?1|sha-?256|sha-?3|blake[23]?|md5|
//! ripemd|keccak' storage-git/src/`): the only match is the module-level
//! doc comment on `lib.rs` noting that `Repository::object_hash()` is
//! queried "rather than assuming SHA-1 or SHA-256" -- a description of
//! *git's own* object-hash format (exactly what SG27 says this layer may
//! depend on generically), not of a digest algorithm this layer computes.
//! `storage-git/Cargo.toml` names no hashing library under
//! `[dependencies]` (only `gix`, whose `sha256` feature is git's own object
//! format support); `sha2` appears only under `[dev-dependencies]`. This is
//! a one-time, human/agent-performed audit, not something encoded as a
//! runtime test here (a naive automated grep would false-positive on that
//! same legitimate doc comment).

#[path = "acceptance_support/mod.rs"]
mod support;

use polydigest::Storage;
use support::{
    FixtureHasher, bare_repo, hasher_widths, new_log, new_memory_log, object_hash_formats,
};

/// [SG26]/[SG27] The full read/write behavior must be identical regardless
/// of which `Hasher` (of whatever digest width) the caller supplies, and
/// regardless of which git object-hash format the repository was created
/// under -- this layer must never branch on either. Parametrized over two
/// digest widths and both object-hash formats (per the spec's own §7 test
/// mapping for SG26/SG27), cross-checked against the same independent
/// `MemoryStorage` reference SG8 uses.
#[test]
fn sg26_sg27_parametric_over_hasher_width_and_object_hash_format() {
    smol::block_on(async {
        for object_hash in object_hash_formats() {
            for width in hasher_widths() {
                let dir = tempfile::tempdir().unwrap();
                let repo = bare_repo(dir.path(), object_hash);
                let staging = "refs/eml/storage/sg26-27/staging";
                let k = 3u64;
                let mut git_log = new_log(&repo, staging, k, FixtureHasher::new(width)).await;
                let mut mem_log = new_memory_log(k, FixtureHasher::new(width)).await;

                for n in 0..12u64 {
                    let leaf = format!("leaf-{n}-{object_hash:?}-{width}").into_bytes();
                    git_log.append_leaf(&leaf).await.unwrap_or_else(|e| {
                        panic!(
                            "object_hash={object_hash:?}, width={width}: append_leaf failed: {e}"
                        )
                    });
                    mem_log.append_leaf(&leaf).await.unwrap();

                    for i in 0..=n {
                        let git_leaf = git_log.storage().get_leaf(i).await.unwrap();
                        let mem_leaf = mem_log.storage().get_leaf(i).await.unwrap();
                        assert_eq!(
                            git_leaf, mem_leaf,
                            "object_hash={object_hash:?}, width={width}, n={n}, i={i}: get_leaf \
                             mismatch"
                        );
                    }
                    for height in 0..4u32 {
                        let cap = k.pow(height);
                        let mut left = 0u64;
                        while left <= n {
                            let git_node =
                                git_log.storage().get_node(0, left, height).await.unwrap();
                            let mem_node =
                                mem_log.storage().get_node(0, left, height).await.unwrap();
                            assert_eq!(
                                git_node, mem_node,
                                "object_hash={object_hash:?}, width={width}, n={n}, left={left}, \
                                 height={height}: get_node mismatch"
                            );
                            if let Some(bytes) = &git_node {
                                assert_eq!(
                                    bytes.len(),
                                    width,
                                    "a stored digest must be exactly this hasher's declared width"
                                );
                            }
                            left += cap;
                        }
                    }
                }

                // SG27: the repository's own object-hash format is
                // queried/re-detected correctly by reopening.
                let reopened = storage_git::GitStorage::open(dir.path(), staging, k)
                    .unwrap_or_else(|e| {
                        panic!(
                            "object_hash={object_hash:?}, width={width}: reopening an existing \
                             {object_hash:?} repository failed: {e}"
                        )
                    });
                assert_eq!(
                    Storage::len(&reopened).await.unwrap(),
                    12,
                    "object_hash={object_hash:?}: reopening must recover the same log length \
                     regardless of object-hash format"
                );
            }
        }
    });
}
