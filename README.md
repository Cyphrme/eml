# Polymorphic Merkle Trees

A formally verified construction for cryptographic Merkle trees that share one
topology across many hash algorithms simultaneously. The repository is cut into
three layers — a kernel, two engineering libraries, and application
instantiations — described in full in [`docs/architecture.md`](docs/architecture.md).

## The three layers

```
┌──────────────────────────────────────────────────────────────────────┐
│ Layer 1 — PMT  (Polymorphic Merkle Tree kernel)        crate: pmt    │
│   proof spine · canonicalization (collapse + promotion) · Hasher seam│
│   inclusion · leaf proof · binding proof · binding root · coupling   │
│   seal lattice · opaque metadata channel                             │
│   depends on nothing                                                 │
└──────────────────────────┬───────────────────────────────────────────┘
                            │
           ┌────────────────┴──────────────────┐
┌──────────▼─────────────────┐    ┌────────────▼────────────────┐
│ Layer 2 — EML               │    │ Layer 2 — EMT               │
│  append-only log  crate: eml│    │  mutable tree    crate: emt │
│  frontier-stack carry        │    │  set / get; no consistency  │
│  consistency proofs          │    │  retroactive per-node alg   │
│  snapshot proof · filling    │    │  add at O(log n)            │
└──────────┬──────────────────┘    └────────────┬────────────────┘
           │                                    │
  ┌────────┴────────┐                  ┌────────┴───────┐
  │ cyphr-log (k=2)  │                  │ cyphr-tree(k=2)│
  └─────────────────┘                  └────────────────┘
    Layer 3 — application instantiations (consumers; may leave the repo)
```

**PMT** (`pmt/`) is the abstract core: proof spine, canonicalization,
multi-algorithm binding root, and the `Sealed` commitment currency. It depends
on nothing.

**EML** (`eml/`) is the append-only log built on PMT. It owns the frontier
carry, consistency proofs, snapshot proofs, and filling (data-required rebuild).

**EMT** (`emt/`) is the mutable peer. Interior cells can change (`set` / `get`),
so it has no frontier and no consistency proofs; instead it provides retroactive
per-node algorithm addition at O(log n).

The two engineering libraries never depend on each other. The one currency they
share is PMT's `Sealed` commitment.

## Key design points

**Multi-algorithm, one topology.** Every hash algorithm sees the same tree
shape; each computes its own digests independently. Adding or removing an
algorithm never touches another's roots or proofs.

**Canonicalization.** Two primitives — *promotion* (a lone child lifts without
hashing) and *collapse* (equal-valued siblings fold to one) — form a single
confluent reduction to a unique canonical form. This pins each layout to exactly
one root and closes proof malleability.

**Binding root.** One `nary_mr` fold over the per-algorithm member roots (plus
a timeline coverage child when the epoch schedule is non-trivial). A
single-algorithm tree with an open-from-genesis schedule folds to a plain root
with no overhead.

**Seal lattice.** There is exactly one commitment currency: `Sealed`
(`pmt/src/sealed.rs`). From a seal, three operations are possible:
*verify* (check proofs against the committed roots), *resume* (reopen an
append-only log without the historical data), and *fill* (rebuild a full tree
over the real leaf data — data-required, trustless, verifies against the
committed root).

**Epoch timeline.** Per algorithm, a committed vector of `(start, end)`
intervals records when it was active. Activity is read from the timeline, never
inferred from a digest. This is the basis for null-fill at inactive positions
and for temporal binding guarantees.

**Proof non-malleability.** A zero-sibling step would represent a promoted node;
honest provers omit it and verifiers reject it. A fixed `(leaf, index, size,
root)` tuple admits at most one accepting path modulo a hash collision.

## Formal guarantees

The core is verified in Lean 4 (`proofs/lean/`; see `proofs/lean/README.md`
for the reviewer's guide). The verification has two properties:

- **Sorry-free.** No `sorry` placeholder appears anywhere in the proof corpus.
- **At most four structural axioms.** The trusted computing base is declared in
  `proofs/lean/EMLProof/Foundations.lean`: an abstract digest type `Digest`,
  its non-emptiness, the abstract hash `H`, and the serializer `digestToBytes`,
  plus Lean's own built-ins. Collision resistance is **not** an axiom — it is
  discharged as an explicit hypothesis at each use site.

Named theorems:

| Theorem | File | Statement |
| :--- | :--- | :--- |
| `canonical_unique` | `Canonical.lean` | A structure reduces to a unique canonical normal form |
| `kary_inclusion_soundness` | `Kary.lean` | An accepting canonical proof commits the leaf at the claimed position |
| `inclusion_soundness` | `NEML.lean` | Same, lifted to the full NEML model |
| `inclusion_proof_unique` | `NEML.lean` | At most one accepting canonical path per statement (modulo collision) |
| `combinedRoot_binds_timeline` | `NEML.lean` | A fixed binding root pins the member-digest list and binds the timeline |
| `coupling_extract_sound` | `NEML.lean` | Coupling opens the binding root soundly |
| `binding_root_sound` | `BindingProof.lean` | Each algorithm's binding root folds under its own hash |
| `binding_proof_consistent` | `BindingProof.lean` | Mutually consistent trusted binding roots prove agreement on shared structure |
| `leaf_proof_sound` | `LeafProof.lean` | A leaf proof soundly binds a leaf hash to its trusted parameters |
| `snapshot_proof_sound` | `SnapshotProof.lean` | A snapshot proof soundly aggregates leaf proofs against a sealed commitment |
| `consistency_soundness` | `KaryConsistency.lean` | An accepting consistency proof forces the reconstructed old root to the genuine prefix root |
| `consistency_append_only` | `KaryConsistency.lean` | Lifts consistency soundness to the data-level append-only relation |

## Building and testing

Rust workspace:

```sh
cargo test --workspace                   # all unit, property, and fault-injection tests
cargo test --release --test complexity   # complexity regression (release profile)
```

Lean proofs (from `proofs/lean/`):

```sh
lake build
```

Fuzz targets (nightly Rust):

```sh
cargo +nightly fuzz run <target>
# targets: verify_inclusion, verify_consistency, rehydrate_proof,
#          proof_mutation, state_machine,
#          cyphr_malt_verify_inclusion, cyphr_malt_verify_consistency
```

## License

Copyright © 2026 [Cyphrme](https://github.com/Cyphrme). All rights reserved.

Distributed under an interim license that permits non-commercial, personal,
academic, or research use. Commercial use is prohibited. See
[LICENSE](./LICENSE) for the complete terms.

[rfc9162]: https://datatracker.ietf.org/doc/html/rfc9162
