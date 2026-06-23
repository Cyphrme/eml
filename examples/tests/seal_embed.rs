//! Seal, embed, and snapshot example tests.
//!
//! Four self-contained demonstrations of the seal chain and the embedding
//! composition. Each reads in a few idiomatic lines and doubles as an
//! ergonomics witness for the surfaces it exercises.

// ---------------------------------------------------------------------------
// Shared test hasher — unprefixed SHA-256, fixed 32-byte output.
// ---------------------------------------------------------------------------

use sha2::{Digest, Sha256};

#[derive(Debug, Clone, Copy)]
struct H;

impl pmt::Hasher for H {
    fn leaf(&self, d: &[u8]) -> Vec<u8> {
        Sha256::digest(d).to_vec()
    }

    fn node(&self, cs: &[&[u8]]) -> Vec<u8> {
        let mut h = Sha256::new();
        for c in cs {
            h.update(c);
        }
        h.finalize().to_vec()
    }

    fn empty(&self) -> Vec<u8> {
        Sha256::digest(b"").to_vec()
    }

    fn hash(&self, d: &[u8]) -> Vec<u8> {
        Sha256::digest(d).to_vec()
    }

    fn clone_box(&self) -> Box<dyn pmt::Hasher> {
        Box::new(*self)
    }
}

// ---------------------------------------------------------------------------
// E1 — mutable-tree seal root byte-equals a natively-appended log root
//
// The mutable tree's `seal()` freezes the member roots at that size into
// `pmt::Sealed`. The append-only log accumulating the same payloads in order
// under the same hasher must carry an identical root: the two constructions
// share the kernel topology and the same hash, so the same data maps to the
// same digest.
// ---------------------------------------------------------------------------

#[test]
fn seal_root_equals_native_append_root() {
    let payloads: &[&[u8]] = &[b"alpha", b"beta", b"gamma"];

    // Build the mutable tree and seal it.
    let mut t = emt::Emt::new(emt::Config { arity: 2 }).unwrap();
    t.register_algorithm(0, Box::new(H)).unwrap();
    for (i, p) in payloads.iter().enumerate() {
        t.set(i as u64, p.to_vec(), Vec::new()).unwrap();
    }
    let sealed = t.seal().unwrap();

    // Build the append-only log over the same payloads in the same order.
    let log_root = smol::block_on(async {
        let mut log = cyphr_log::new(eml_log::MemoryStorage::new(), Box::new(H))
            .await
            .unwrap();
        for p in payloads {
            log.append_leaf(p).await.unwrap();
        }
        log.root_for(0).unwrap()
    });

    // The sealed member root for algorithm 0 must equal the native log root.
    let sealed_root = sealed
        .active_roots()
        .iter()
        .find(|(id, _)| *id == 0)
        .map(|(_, r)| r.as_slice())
        .expect("algorithm 0 present");

    assert_eq!(sealed_root, log_root.as_slice());
}

// ---------------------------------------------------------------------------
// E2 — cyphr-log root embeds in an EMT; composition is two independent
//       inclusion verifications, no new proof type
//
// An append-only log root is an opaque `pmt` leaf at position P in the outer
// EMT. Verifying that a log entry E is committed under the EMT root requires
// exactly two `pmt::verify_inclusion` calls:
//   1. the log's own inclusion proof (leaf E → log root),
//   2. the EMT's inclusion proof (log root as a leaf → EMT root).
// ---------------------------------------------------------------------------

#[test]
fn embedded_log_root_composes_as_two_inclusion_verifications() {
    let log_payloads: &[&[u8]] = &[b"tx0", b"tx1", b"tx2"];
    let embed_pos: u64 = 1; // position in the outer EMT

    smol::block_on(async {
        // Build the append-only log.
        let mut log = cyphr_log::new(eml_log::MemoryStorage::new(), Box::new(H))
            .await
            .unwrap();
        for p in log_payloads {
            log.append_leaf(p).await.unwrap();
        }
        let log_size = log.count();
        let log_root = log.root_for(0).unwrap();

        // Inclusion proof for entry 1 (b"tx1") within the log.
        let log_leaf_proof = log
            .leaf_proof(1, log_size)
            .await
            .unwrap()
            .expect("entry 1 is in range");

        // Embed the log root as an opaque leaf at `embed_pos` in the outer EMT.
        let mut outer = emt::Emt::new(emt::Config { arity: 2 }).unwrap();
        outer.register_algorithm(0, Box::new(H)).unwrap();
        outer.set(0, b"other-cell".to_vec(), Vec::new()).unwrap();
        // The log root is opaque: indistinguishable from any other leaf payload.
        outer.set(embed_pos, log_root.clone(), Vec::new()).unwrap();
        let outer_root = outer.root(0).unwrap();

        // Inclusion proof for the embedded log root in the outer EMT.
        let (outer_leaf_hash, outer_path) = outer
            .inclusion_proof(0, embed_pos)
            .expect("embed_pos is in range");

        // Verification step 1: log entry E → log root.
        assert!(log_leaf_proof.verify(&H, &log_root));

        // Verification step 2: log root (as a leaf) → outer EMT root.
        assert!(pmt::verify_inclusion(
            &H,
            &outer_leaf_hash,
            embed_pos,
            outer.len(),
            outer.arity(),
            &outer_path,
            &outer_root,
        ));

        // The two steps compose without a new proof type: log entry E is
        // committed under the outer EMT root via the log root as the bridge.
    });
}

// ---------------------------------------------------------------------------
// E3 — seal_snapshot yields a Snapshot carrying binding root + extents + meta
//
// `seal_snapshot_with_meta` consumes the log and produces a `Snapshot` that
// freezes the binding root, the committed canonicalization run-extents, and
// an opaque metadata payload. The seal is one-way: no path back to a log.
// ---------------------------------------------------------------------------

#[test]
fn seal_snapshot_carries_binding_root_extents_and_meta() {
    smol::block_on(async {
        let mut log = eml_log::NaryMerkleLog::new(
            eml_log::MemoryStorage::new(),
            Box::new(H),
            eml_log::TreeConfig { log_arity: 2 },
        )
        .await
        .unwrap();
        for p in [b"p0" as &[u8], b"p1", b"p2", b"p3", b"p4", b"p5", b"p6"] {
            log.append_leaf(p).await.unwrap();
        }

        let attestation = pmt::Meta::new(b"tree-head-sig".to_vec());
        let snap = log.seal_snapshot_with_meta(attestation).await.unwrap();

        // The snapshot carries the binding root for algorithm 0.
        assert!(snap.binding_root(0).is_some());
        // The committed run-extents are the non-promoted frontier nodes (height >= 1).
        assert!(!snap.run_extents().is_empty());
        // The opaque metadata channel carries the attestation verbatim.
        assert_eq!(
            snap.meta().map(pmt::Meta::as_bytes),
            Some(b"tree-head-sig".as_slice())
        );
        // The seal is one-way: no unsnapshot, no field mutator — enforced by the type.
    });
}

// ---------------------------------------------------------------------------
// E4 — snapshot proof verifies a leaf against the snapshot (base case = leaf
//       proof)
//
// `SnapshotProof::produce` packages the snapshot's frozen member roots with
// a sequence of `pmt::LeafProof` claims. `verify` checks the binding tier
// (member roots → trusted binding root) and the leaf tier (leaf proofs →
// member root) in two composed steps — the leaf proof is the base case.
// ---------------------------------------------------------------------------

#[test]
fn snapshot_proof_verifies_leaf_against_snapshot() {
    smol::block_on(async {
        let mut log = eml_log::NaryMerkleLog::new(
            eml_log::MemoryStorage::new(),
            Box::new(H),
            eml_log::TreeConfig { log_arity: 2 },
        )
        .await
        .unwrap();
        for p in [b"x0" as &[u8], b"x1", b"x2", b"x3"] {
            log.append_leaf(p).await.unwrap();
        }
        let n = log.count();

        // Produce the leaf proof before sealing (the log is consumed by the seal).
        let leaf_proof = log
            .leaf_proof(2, n)
            .await
            .unwrap()
            .expect("index 2 in range");
        let binding_root = log.combined_root_at(0, n).await.unwrap();

        let snap = log.seal_snapshot().await.unwrap();

        // Assemble the snapshot proof over the single claimed leaf.
        let proof =
            eml_log::SnapshotProof::produce(&snap, vec![eml_log::ClaimedLeaf::new(0, leaf_proof)]);

        let trusted = [pmt::TrustedBindingRoot {
            alg_id: 0,
            hasher: &H,
            root: &binding_root,
        }];
        let hashers: [(u64, &dyn pmt::Hasher); 1] = [(0, &H)];

        assert!(proof.verify(&trusted, &hashers));
    });
}
