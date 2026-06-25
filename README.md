# Merkle Spine

A formally verified library for canonical, multi-algorithm Merkle structures: one
tree topology shared across many hash algorithms at once, with a single canonical
form per layout. The repository is a **four-tier stack of library crates** — a
structural core, two single-algorithm engineering libraries, a combinator that
lifts them across algorithms, and the concrete instantiations. The full design is
in [`docs/architecture.md`](docs/architecture.md).

## The stack

The crates are layered, and the stack gets **more concrete going up**: the Spine
is the most abstract (a generic Merkle structure, infinitely reusable, with no
notion of epochs); each tier up is more concrete, ending in named, `k`-fixed
instantiations.

```
┌──────────────────────────────────────────────────────────────────────────────┐
│ L4 — EML / EMT — the instantiations (where "Epoch" lives)           eml/emt  │
│   EML = polydigest(CML) @ k=2, arbitrary subtrees — the general-purpose log    │
│   EMT = polydigest(CMT) @ k=2 — the mutable peer                               │
└───────────────────────────────┬────────────────────────────────────────────────┘
                                 │  instantiate at k=2
┌──────────────────────────────────────────────────────────────────────────────┐
│ L3 — the combinator                                             polydigest    │
│   lifts a CML or CMT across N algorithms over ONE shared data substrate:        │
│   activation timeline · null-run-extents · binding root · binding proof         │
└───────────────────────────────┬────────────────────────────────────────────────┘
              ┌──────────────────┴───────────────────┐
┌─────────────▼──────────────────┐      ┌─────────────▼──────────────────┐
│ L2 — CML (Canonical Merkle Log) │      │ L2 — CMT (Canonical Merkle Tree)│
│  append-only, single-algorithm  │      │  mutable, single-algorithm      │
│  frontier carry · consistency   │ cml  │  set / get; no consistency  cmt │
│  seal → Snapshot · filling base │      │  per-node multi-hash add        │
└─────────────┬──────────────────┘      └─────────────┬──────────────────┘
              └──────────────────┬───────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│ L1 — Merkle Spine — the structural core; the proof payoff            spine    │
│   canonicalization (collapse + promotion) · the proof spine · the Hasher seam  │
│   inclusion · leaf proof · the general structural Seal · opaque metadata       │
│   depends on nothing · epoch-free                                              │
└──────────────────────────────────────────────────────────────────────────────┘
```

**Merkle Spine** (`spine`) is the abstract structural core: canonicalization, the
proof spine, the `Hasher` seam, inclusion and leaf proofs, the general structural
`Seal`, and an opaque metadata channel. It is **epoch-free** and depends on
nothing. The structural uniqueness theorem is the central proof payoff.

**CML** (`cml`) and **CMT** (`cmt`) are the two single-algorithm engineering
libraries over the Spine. CML — Canonical Merkle Log — is append-only: it owns the
frontier carry, append-only-prefix consistency proofs, and the structural snapshot.
CMT — Canonical Merkle Tree — is the mutable peer: `set` / `get` and per-node
multi-hash, but no frontier and so no consistency proofs. Both are `k`-generic and
epoch-free; neither depends on the other. The one currency they exchange is the
spine's `Seal`.

**`polydigest`** is the combinator that lifts a CML or CMT across **N algorithms
over one shared data substrate**. It is *not* a composition of independent logs —
that would duplicate the data and raise per-algorithm cost. The leaf entries live
once; each algorithm is a frontier / hash-view over them, so its only per-algorithm
cost is its own hashing. The combinator adds the three concepts the structural core
deliberately omits: the **activation timeline** (which algorithm is live where),
the **null-run-extents** (the one logical count, for cross-tree alignment), and the
**binding root** (the atomic multi-tree commitment).

**EML / EMT** (`eml` / `emt`) are the concrete instantiations, fixed at arity
`k = 2`. **EML** — the Epoch Merkle Log, `polydigest(CML)` — is the general-purpose
append-only log. **EMT** — the Epoch Merkle Tree, `polydigest(CMT)` — is the mutable
peer. `k = 2` is a sane default, not an opinion: binary spine traversal is cheaply
logarithmic.

The library is **de-branded**. The deliverable is the crates; the instantiations
are thin. A consumer composes its own application structures over EML/EMT — for
example a mutable outer tree with an embedded append-only commit log, joined by the
spine's opaque subtree embedding; a CT-style build can wrap any `Hasher` with RFC
9162 prefix bytes — but no consumer-specific crate lives in the library namespace.

## Key design points

**One topology, many algorithms.** Every hash algorithm sees the same tree shape;
each computes its own digests independently. Adding or removing an algorithm never
touches another's roots or proofs.

**Canonicalization.** Two primitives — *promotion* (a lone child lifts in place of
its hashed node) and *collapse* (equal-valued siblings fold to one) — compose into a
single confluent reduction to a unique canonical form. Collapse is general, not
null-specific: null is just one value that collapses. This pins each layout to
exactly one root and closes proof malleability. Both primitives are structural —
they *reduce* the count, tracking nothing.

**The two-count model.** The structural tiers (Spine / CML / CMT) carry the bare
*reduced* count and commit nothing. The only thing ever counted is the
**null-run-extent**, retained solely for cross-tree alignment — and it lives only
at the `polydigest` combinator, because it is the one collapse instance that
diverges per algorithm. Everything follows from this boundary.

**The binding root.** Per algorithm, `BR_i` is the same canonicalization fold
applied one level up, over the per-algorithm member roots as opaque children (plus
the all-algorithms null-run-extents when activation is non-trivial). Others' roots
enter only as opaque digests — no security material is mixed across algorithms, so
no algorithm's break can weaken another. A single-algorithm, open-from-genesis
structure folds to a plain root with no overhead.

**Permanent / ephemeral hashes.** The spine decomposes a log into a frontier of
perfect `k`-ary subtrees. A complete subtree's hash is **permanent** — it appears
in every larger tree and never changes — while the frontier-fold is **ephemeral**,
recomputed per size. Only permanent hashes appear in proofs, so an append never
mutates a proven hash. This is the precise "maximally immutable" semantics, and it
lets the storage/serving layer stay fully untrusted (the CT / Trillian model).

**Stable-coordinate addressing.** A node is addressed by a coordinate invariant to
canonicalization and to the hash — the leaf sequence number, or a complete-subtree
`(level, index)` — and the structural path is *derived*, never stored. A from-root
child-index path is not used: it churns under promotion/collapse and diverges
across the per-algorithm trees.

**Proof non-malleability.** A zero-sibling step would represent a promoted node;
honest provers omit it and verifiers reject it. A fixed `(leaf, index, size, root)`
tuple admits at most one accepting path, modulo a hash collision.

## Formal guarantees

The structural core and the combinator are verified in Lean 4 (`proofs/lean/`; see
[`proofs/lean/README.md`](proofs/lean/README.md) for the reviewer's guide). The
verification has two properties:

- **Sorry-free.** No `sorry` placeholder appears anywhere in the proof corpus.
- **At most four structural axioms.** The trusted computing base is declared in
  `proofs/lean/EMLProof/Foundations.lean`: an abstract digest type `Digest`, its
  non-emptiness, the abstract hash `H`, and the serializer `digestToBytes`, plus
  Lean's own built-ins. Collision resistance is **not** an axiom — it is discharged
  as an explicit hypothesis at each use site.

The proof split mirrors the code split: the structural theorems carry no epoch
hypothesis and sit at the Spine / CML layer; the binding theorems consume roots as
opaque digests and sit at the `polydigest` layer.

| Theorem | Layer | Statement |
| :--- | :--- | :--- |
| `canonical_unique` | Spine | A structure reduces to a unique canonical normal form |
| `kary_inclusion_soundness` | Spine | An accepting canonical proof commits the leaf at the claimed position |
| `inclusion_proof_unique` | Spine | At most one accepting canonical path per statement (modulo collision) |
| `leaf_proof_sound` | Spine | A leaf proof soundly binds a leaf hash to its trusted parameters |
| `consistency_soundness` | CML | An accepting consistency proof forces the reconstructed old root to the genuine prefix root |
| `consistency_append_only` | CML | Lifts consistency soundness to the data-level append-only relation |
| `combinedRoot_binds_timeline` | polydigest | A fixed binding root pins the member-digest list and binds the timeline |
| `coupling_extract_sound` | polydigest | Coupling opens the binding root soundly |
| `binding_root_sound` | polydigest | Each algorithm's binding root folds under its own hash |
| `binding_proof_consistent` | polydigest | Mutually consistent trusted binding roots prove agreement on the shared structure |
| `snapshot_proof_sound` | polydigest | A snapshot proof soundly aggregates leaf proofs against a sealed commitment |

### Conformance

The log uses MMR **durable witnesses**: each leaf's inclusion path to its peak is
permanent and extends append-only. Inclusion and binding-root verification are
preserved from the prior design; the consistency proof is upgraded to the MMR
prefix-form. The conformance oracle is the Lean corpus and the durability property
tests (`eml/tests/proptests.rs`, `polydigest/tests/`), which assert witness
permanence across appends.

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
#          proof_mutation, state_machine
```

## License

Copyright © 2026 [Cyphrme](https://github.com/Cyphrme). All rights reserved.

Distributed under an interim license that permits non-commercial, personal,
academic, or research use. Commercial use is prohibited. See
[LICENSE](./LICENSE) for the complete terms.
