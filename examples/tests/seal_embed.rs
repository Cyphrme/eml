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

impl spine::Hasher for H {
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

    fn clone_box(&self) -> Box<dyn spine::Hasher> {
        Box::new(*self)
    }
}

// ---------------------------------------------------------------------------
// E1 — mutable-tree seal root byte-equals a natively-appended log root
//
// The mutable tree's `seal()` computes the resumable frontier into the one
// kernel currency `polydigest::Sealed`; the member root is the fold of those frontier
// peaks. The append-only log accumulating the same payloads in order under the
// same hasher must carry an identical root: the two constructions share the
// kernel topology and the same hash, so the same data maps to the same digest.
// ---------------------------------------------------------------------------

// PRESERVED under MMR: an EMT seal's member root still byte-equals a
// separately-built EML log's root over the same payloads. The MMR peak-bag is the
// established rightmost-k grouping (root-preserving at every arity), the same
// fold the mutable tree uses, so the two constructions still map identical data
// to an identical digest — the migration changed the inclusion proof, not the
// root.
#[test]
fn seal_root_equals_native_append_root() {
    // Seven payloads → a frontier of three peaks (sizes 4, 2, 1) at k=2, i.e.
    // MORE than k peaks: the bag does real multi-level grouping, so this proves
    // the equality beyond the trivial ≤k-peak case where any fold coincides.
    let payloads: &[&[u8]] = &[
        b"alpha", b"beta", b"gamma", b"delta", b"eps", b"zeta", b"eta",
    ];

    // Build the mutable tree and seal it.
    let mut t = polydigest::EpochTree::new(polydigest::CmtConfig { arity: 2 }).unwrap();
    t.register_algorithm(0, Box::new(H)).unwrap();
    for (i, p) in payloads.iter().enumerate() {
        t.set(i as u64, p.to_vec(), Vec::new()).unwrap();
    }
    let sealed = t.seal().unwrap();

    // Build the append-only log over the same payloads in the same order.
    let log_root = smol::block_on(async {
        let mut log = eml::new(eml::MemoryStorage::new(), Box::new(H))
            .await
            .unwrap();
        for p in payloads {
            log.append_leaf(p).await.unwrap();
        }
        log.root_for(0).unwrap()
    });

    // The derived member root for algorithm 0 (the fold of the sealed frontier
    // peaks) must equal the native log root.
    let sealed_root = sealed
        .member_root(0, &H, polydigest::rebalanced_bag)
        .expect("algorithm 0 present");

    // The MMR peak-bag is the established rightmost-k grouping (root-preserving),
    // the same fold the mutable tree uses, so the member root byte-equals the
    // native log root.
    assert_eq!(sealed_root.as_slice(), log_root.as_slice());
}

// ---------------------------------------------------------------------------
// E2 — eml root embeds in an EMT; composition is two independent
//       inclusion verifications, no new proof type
//
// An append-only log root is an opaque `spine` leaf at position P in the outer
// EMT. Verifying that a log entry E is committed under the EMT root requires
// exactly two `spine::verify_inclusion` calls:
//   1. the log's own inclusion proof (leaf E → log root),
//   2. the EMT's inclusion proof (log root as a leaf → EMT root).
// ---------------------------------------------------------------------------

#[test]
fn embedded_log_root_composes_as_two_inclusion_verifications() {
    let log_payloads: &[&[u8]] = &[b"tx0", b"tx1", b"tx2"];
    let embed_pos: u64 = 1; // position in the outer EMT

    smol::block_on(async {
        // Build the append-only log.
        let mut log = eml::new(eml::MemoryStorage::new(), Box::new(H))
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
        let mut outer = polydigest::EpochTree::new(polydigest::CmtConfig { arity: 2 }).unwrap();
        outer.register_algorithm(0, Box::new(H)).unwrap();
        outer.set(0, b"other-cell".to_vec(), Vec::new()).unwrap();
        // The log root is opaque: indistinguishable from any other leaf payload.
        outer.set(embed_pos, log_root.clone(), Vec::new()).unwrap();
        let outer_root = outer.root(0).unwrap();

        // Inclusion proof for the embedded log root in the outer EMT.
        let (outer_leaf_hash, outer_path) = outer
            .inclusion_proof(0, embed_pos)
            .expect("embed_pos is in range");

        // Verification step 1: log entry E → log root (log-origin: mountain).
        let log_sk = polydigest::mountain_skeleton(
            log_leaf_proof.arity,
            log_leaf_proof.tree_size,
            log_leaf_proof.index,
        )
        .expect("valid log position");
        assert!(log_leaf_proof.verify(&H, &log_sk, &log_root));

        // Verification step 2: log root (as a leaf) → outer EMT root
        // (EMT-origin: rebalanced).
        let outer_sk = polydigest::rebalanced_skeleton(outer.len(), outer.arity(), embed_pos)
            .expect("valid position");
        assert!(spine::verify_inclusion(
            &H,
            &outer_leaf_hash,
            &outer_sk,
            &outer_path,
            &outer_root,
        ));

        // The two steps compose without a new proof type: log entry E is
        // committed under the outer EMT root via the log root as the bridge.
    });
}

// ---------------------------------------------------------------------------
// E3 — seal yields the one currency `Sealed`; binding root + extents are
//      derived views, and an opaque attestation rides the metadata channel
//
// `seal_with_meta` consumes the log and produces a `polydigest::Sealed` carrying the
// resumable frontier and an opaque metadata payload. The binding root and the
// committed run-extents are *derived views* of the `Sealed`, computed on demand
// (D12), never stored. The seal is one-way: no path back to a log.
// ---------------------------------------------------------------------------

#[test]
fn seal_yields_currency_with_derived_binding_root_and_extents() {
    smol::block_on(async {
        let mut log = eml::NaryMerkleLog::new(
            eml::MemoryStorage::new(),
            Box::new(H),
            eml::TreeConfig { arity: 2 },
        )
        .await
        .unwrap();
        for p in [b"p0" as &[u8], b"p1", b"p2", b"p3", b"p4", b"p5", b"p6"] {
            log.append_leaf(p).await.unwrap();
        }

        let attestation = spine::Meta::new(b"tree-head-sig".to_vec());
        let sealed = log.seal_with_meta(attestation).await.unwrap();

        // The binding root for algorithm 0 is derived from the frontier on demand.
        let hashers: [(u64, &dyn spine::Hasher); 1] = [(0, &H)];
        assert!(
            sealed
                .binding_root(0, &H, &hashers, polydigest::bag_peaks)
                .unwrap()
                .is_some()
        );
        // The committed run-extents are the non-promoted frontier nodes (height >= 1).
        assert!(!sealed.run_extents().is_empty());
        // The opaque metadata channel carries the attestation verbatim.
        assert_eq!(
            sealed.meta().map(spine::Meta::as_bytes),
            Some(b"tree-head-sig".as_slice())
        );
        // The seal is one-way: no unseal, no field mutator — enforced by the type.
    });
}

// ---------------------------------------------------------------------------
// E4 — snapshot proof verifies a leaf against the snapshot (base case = leaf
//       proof)
//
// `SnapshotProof::produce` packages the snapshot's frozen member roots with
// a sequence of `spine::LeafProof` claims. `verify` checks the binding tier
// (member roots → trusted binding root) and the leaf tier (leaf proofs →
// member root) in two composed steps — the leaf proof is the base case.
// ---------------------------------------------------------------------------

#[test]
fn snapshot_proof_verifies_leaf_against_snapshot() {
    smol::block_on(async {
        let mut log = eml::NaryMerkleLog::new(
            eml::MemoryStorage::new(),
            Box::new(H),
            eml::TreeConfig { arity: 2 },
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

        let sealed = log.seal().await.unwrap();
        let hashers: [(u64, &dyn spine::Hasher); 1] = [(0, &H)];

        // Assemble the snapshot proof over the single claimed leaf.
        let proof = eml::SnapshotProof::produce(
            &sealed,
            &hashers,
            polydigest::bag_peaks,
            vec![eml::ClaimedLeaf::new(0, leaf_proof)],
        );

        let trusted = [polydigest::TrustedBindingRoot {
            alg_id: 0,
            hasher: &H,
            root: &binding_root,
        }];

        // Log-origin seal: leaf proofs verify against the mountain topology.
        assert!(proof.verify(&trusted, &hashers, polydigest::mountain_skeleton));
    });
}

// ---------------------------------------------------------------------------
// E5 — seal an EMT, resume an EML onto its frontier, append forward
//
// `Emt::seal` computes the resumable frontier; `NaryMerkleLog::resume` reopens
// an append-only log onto exactly that frontier (frontier-anchored EML) and
// appends real leaves forward. The resumed log's root at the sealed size equals
// the sealed member root — the frontier carries forward losslessly.
// ---------------------------------------------------------------------------

// PRESERVED under MMR: resuming an EML onto an EMT's sealed frontier still
// reproduces the sealed member root. The MMR peak-bag is the established
// rightmost-k grouping (root-preserving at every arity) — the same fold the
// mutable tree uses — so the resumed log's root equals the EMT seal's member
// root, and the frontier carries forward losslessly. The migration restructured
// the inclusion proof (prove-to-peak), not the root.
#[test]
fn seal_emt_then_resume_eml_appends_forward() {
    smol::block_on(async {
        // Build and seal a mutable tree of SEVEN cells → a frontier of three
        // peaks (4, 2, 1) at k=2, i.e. MORE than k peaks: the resumed log must
        // reproduce a genuinely multi-level bagged root, not a trivial ≤k case.
        let mut t = polydigest::EpochTree::new(polydigest::CmtConfig { arity: 2 }).unwrap();
        t.register_algorithm(0, Box::new(H)).unwrap();
        for (i, p) in [b"a" as &[u8], b"b", b"c", b"d", b"e", b"f", b"g"]
            .iter()
            .enumerate()
        {
            t.set(i as u64, p.to_vec(), Vec::new()).unwrap();
        }
        let sealed = t.seal().unwrap();
        let sealed_member = sealed
            .member_root(0, &H, polydigest::rebalanced_bag)
            .unwrap();

        // Resume an append-only log onto the EMT-origin frontier.
        let mut log =
            eml::NaryMerkleLog::resume(&sealed, eml::MemoryStorage::new(), vec![(0, Box::new(H))])
                .await
                .unwrap();

        // The resumed log carries the sealed size and reproduces the member
        // root: the MMR peak-bag is the established rightmost-k grouping, the same
        // fold the EMT seal used, so the resumed root equals the sealed member root.
        assert_eq!(log.count(), 7);
        assert_eq!(log.root_for_at(0, 7).await.unwrap(), sealed_member);

        // Append real leaves forward; the log continues from the committed
        // frontier. A resumed log is subtree-kind, so a real leaf is a
        // single-leaf subtree (its digest is the leaf hash).
        log.append_subtree(&spine::Subtree::Leaf(b"h".to_vec()))
            .await
            .unwrap();
        log.append_subtree(&spine::Subtree::Leaf(b"i".to_vec()))
            .await
            .unwrap();
        assert_eq!(log.count(), 9);
        // A consistency proof bridges the resume boundary (7 -> 9).
        let proof = log.consistency_proof(7, 9).await.unwrap();
        assert!(proof.is_some());
    });
}

// ---------------------------------------------------------------------------
// E6 — seal an EML, fill an EMT from the data, verify against the binding root
//
// `fill` is the trustless verification path: holding the real leaf data and the
// committed `Sealed`, rebuild a readable tree of the chosen kind and verify the
// rebuilt binding root equals the committed one — no signature, no signer trust.
// ---------------------------------------------------------------------------

#[test]
fn seal_eml_then_fill_emt_verifies_against_binding_root() {
    smol::block_on(async {
        let data: Vec<Vec<u8>> = (0..6u64)
            .map(|i| format!("leaf-{i}").into_bytes())
            .collect();
        let mut log = eml::NaryMerkleLog::new(
            eml::MemoryStorage::new(),
            Box::new(H),
            eml::TreeConfig { arity: 2 },
        )
        .await
        .unwrap();
        for leaf in &data {
            log.append_leaf(leaf).await.unwrap();
        }
        let sealed = log.seal().await.unwrap();

        // Fill an EMT-kind tree from the real data; the rebuilt binding root is
        // verified against the committed one (rejection on mismatch is internal).
        let hashers: [(u64, &dyn spine::Hasher); 1] = [(0, &H)];
        let filled = eml::fill(&sealed, 0, &H, &data, eml::FillKind::Emt, &hashers).unwrap();
        assert_eq!(filled.tree_size(), 6);
        // The verified member root equals the sealed member root.
        assert_eq!(
            filled.root(),
            sealed
                .member_root(0, &H, polydigest::bag_peaks)
                .unwrap()
                .as_slice()
        );
    });
}

// ---------------------------------------------------------------------------
// E7 — fill-and-verify a commitment from data alone, without the signature
//
// The whole point of the trustless path: a party holding only the data and the
// committed binding root (vouched out of band) can confirm the commitment — and
// reject forged data — without trusting any signer. No attestation is consulted.
// ---------------------------------------------------------------------------

#[test]
fn trustless_fill_verify_without_a_signature() {
    smol::block_on(async {
        let data: Vec<Vec<u8>> = (0..7u64).map(|i| format!("e-{i}").into_bytes()).collect();
        let mut log = eml::NaryMerkleLog::new(
            eml::MemoryStorage::new(),
            Box::new(H),
            eml::TreeConfig { arity: 2 },
        )
        .await
        .unwrap();
        for leaf in &data {
            log.append_leaf(leaf).await.unwrap();
        }
        let sealed = log.seal().await.unwrap();
        let hashers: [(u64, &dyn spine::Hasher); 1] = [(0, &H)];

        // Genuine data verifies — the commitment is confirmed from data alone.
        assert!(eml::fill(&sealed, 0, &H, &data, eml::FillKind::Eml, &hashers).is_ok());

        // Forged data cannot reproduce the committed layout — rejected, no
        // signature needed to detect the tampering.
        let mut forged = data.clone();
        forged[2] = b"tampered".to_vec();
        assert_eq!(
            eml::fill(&sealed, 0, &H, &forged, eml::FillKind::Eml, &hashers),
            Err(eml::FillError::BindingRootMismatch { alg_id: 0 })
        );
    });
}
