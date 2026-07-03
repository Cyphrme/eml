# Architecture

This document describes the architecture of the repository: a **four-tier stack**
of library crates — the structural **Merkle Spine** (`merkle-spine`), the two 
single-algorithm canonical libraries **canonical-ml** and **canonical-mt**, the 
**`polydigest`** combinator that lifts them across algorithms, and the concrete 
**EML / EMT** instantiations. It is the durable reference the crate documentation 
and the README point back to. Every architectural claim here is checkable against 
the source; the relevant paths are cited inline.

## The four tiers

The code is cut into four tiers. The stack gets **more concrete going up**: the
Spine is a generic Merkle structure with no notion of epochs, and each tier above
it is more concrete, ending in named `k`-fixed instantiations. Volatility runs the
same way — the abstract core changes least, the instantiations most.

```
┌──────────────────────────────────────────────────────────────────────────────┐
│ L4 — EML / EMT — the instantiations ("Epoch" lives here)            eml/emt  │
│   EML = polydigest(canonical-ml) @ k=2 · EMT = polydigest(canonical-mt) @ k=2 │
└───────────────────────────────┬────────────────────────────────────────────────┘
                                 │  instantiate at k=2
┌──────────────────────────────────────────────────────────────────────────────┐
│ L3 — `polydigest` — the combinator (multi-hash, epochs)        polydigest     │
│   lifts canonical-ml/canonical-mt across N algorithms over shared substrate    │
│   activation timeline · null-run-extents · binding root · binding proof         │
└───────────────────────────────┬────────────────────────────────────────────────┘
              ┌──────────────────┴───────────────────┐
┌─────────────▼──────────────────┐      ┌─────────────▼──────────────────┐
│ L2 — canonical-ml  (append-only)   │  │ L2 — canonical-mt  (mutable)    │
│  frontier carry · consistency       │  │  set / get; path-recompute      │
│  seal → Snapshot · filling base     │  │  per-node multi-hash add        │
└─────────────┬──────────────────┘      └─────────────┬──────────────────┘
              └──────────────────┬───────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│ L1 — Merkle Spine (merkle-spine) — the structural core             spine     │
│   canonicalization (collapse + promotion) · proof spine · Hasher seam         │
│   inclusion · leaf proof · general structural Seal · opaque metadata          │
│   depends on nothing · epoch-free                                              │
└──────────────────────────────────────────────────────────────────────────────┘

  seal stack (one-way):   canonical-mt ──► Seal ──► canonical-ml ──► Snapshot
  combinator:   polydigest(canonical-ml) / polydigest(canonical-mt)
  embedding:    any tree's root ──► an opaque leaf in any other tree
```

canonical-ml and canonical-mt depend only on the Merkle Spine, never on each other; 
the one currency they exchange is the spine's `Seal` (`merkle-spine/src/seal.rs`). 
`polydigest` depends on canonical-ml/canonical-mt. EML/EMT depend on `polydigest`. 
No tier carries an application concept.

## Layer 1 — the Merkle Spine, the structural core

The Spine (`spine/src/lib.rs`) is the abstract core every tree shares and whose
structural theorems are the central proof payoff. It is **epoch-free** — a plain
canonical Merkle structure. Its contents are the *non-arbitrary* structural choices.

### The Hasher seam

A construction reaches its hash through one trait, `Hasher`
(`spine/src/hasher.rs`). The **fixed-width contract** — every digest a single
hasher produces is the same constant byte length — is load-bearing: the unprefixed
node-hash concatenation is injective in its child boundaries only when all children
are the same width, and binding-root soundness rests on that injectivity. Prefix
domain separation is deliberately **not** a Spine axis — `leaf(d)` is `H(d)` with no
prefix byte, and an application that wants domain separation supplies a prefixing
`Hasher` wrapper. This keeps the libraries parameterized essentially by the arity
`k` alone.

One identity follows: because `leaf(d) = H(d)`, a leaf whose payload is the four
bytes `null` hashes to the same digest as the null constant `null() = H(b"null")`.
The structural core treats this as intentional and inert — activity is read from the
`polydigest` combinator's committed timeline, never inferred from a digest equaling the
null constant, so a correct verifier is never fooled by it.

### The proof spine

The proof spine (`spine/src/topology.rs`) is the kernel's topological strategy: a
**constant `k`-ary spine** whose shape is fixed entirely by `(tree_size, arity)`,
with **n-ary subtrees** hanging below it to recover full Merkle generality. For a
given size, a log decomposes into a *frontier* of perfect `k`-ary subtrees
(`frontier_for_size`), which fold into one root by repeatedly grouping the rightmost
`k` (`fold_frontier`). The shape of an inclusion proof is fully determined by
`(tree_size, arity, index)` and computed by a single function, `inclusion_skeleton`.

That single function is the load-bearing detail: the verifier reconstructs the
canonical topology and checks a proof's steps field-by-field against it
(`verify_inclusion_path_structure` in `spine/src/proof.rs`), and proof generation
emits the same skeleton (`within_subtree_path` in `spine/src/mr.rs`). Keeping one
derivation source is what prevents producer and verifier from drifting into
disagreeing topologies. The frontier decomposition is the same construction
certificate-transparency logs and Merkle-mountain-range accumulators use (their
"peaks"); the spine generalizes it to any arity `k` in `2..=256` (`ARITY_RANGE`).

Its payoff is bounding the most expensive part of proof traversal: the spine is the
worst case, and it is constant for a given size.

### Canonicalization: collapse and promotion

Canonicalization (`spine/src/mr.rs`) is one generic reduction over an arbitrary
Merkle structure. It is built from two operations that must be named **distinctly**:

- the **plain structural fold** is the perfect-`k`-ary fold into permanent/ephemeral
  hashes. It is *always-on and dense*, and it does **no reduction** — a dense log
  spine has no zero-sibling step.
- the **canonical reductions** are the two rewrite rules, which fire **only in the
  sparse/null dimension** (a dense log triggers neither):
  - **promotion** — a lone (single) child is lifted in place of the wrapping hashed
    node. It is *structurally deterministic*: a verifier re-derives it on
    reconstruction. This is the path compression a PATRICIA / radix trie performs.
  - **collapse** — children of the *same value* fold to that value
    (`spine/src/mr.rs`): any equal-sibling run collapses, **not only null runs**.
    This is the node-elimination rule of a reduced ordered binary decision diagram
    (ROBDD rule R2). Null is the dominant instance — it is the only
    per-algorithm-divergent collapse, because equal-value non-null runs are the same
    under every algorithm — but the fold is general same-value.

Treating these two reductions as a single confluent reduction to a unique canonical
form is the structural contribution. ROBDD canonicalization is the rigorous
template, but no published work casts generic *Merkle* canonicalization as one
reduction composing these two primitives; that framing is original to this work.
Orthogonal axes are kept separate and below the authentication boundary: subtree
deduplication / hash-consing is a *storage* concern (ROBDD rule R1, tree → DAG) and
entropy coding is a *serialization* concern, neither of which changes a root.

A strict-binary construction obtains its shape by *banning n-ary subtrees and fixing
`k = 2`* — not by disabling canonicalization, which always runs.

#### What canonicalization commits

At the structural layer the count is the *reduced* count, and **nothing is
tracked**:

- **Promotion** is structurally deterministic — a verifier re-derives a lone-child
  lift on reconstruction → commits **nothing**.
- **Collapse** (a same-value run, **including null**) is structural — a collapsed
  run is one node; the canonical form of N equal entries *is* the single canonical
  node. The count is the *reduced* count, never pre-collapse multiplicity.

The one collapse instance that *is* committed — the null-run-extent — is not a
structural-layer concern: nulls are the only value whose run geometry diverges
between algorithms, so their extents must be committed for cross-tree alignment, and
that commitment lives at the `polydigest` combinator (Layer 3). The active geometry that
is structurally derivable stays derived; only the null gaps are committed.

### The general structural Seal

The structural commitment currency is `Seal` (`spine/src/seal.rs`): the resumable
frontier — per algorithm, the digests of the perfect `k`-ary subtrees the frontier
names (the "peaks") — plus an optional opaque metadata channel. It is a **general
lattice** whose structural facet is invariant under algorithm churn, and it carries
**no epoch field**. The seal is **one-way**: there is no `unseal` and no field
mutator, so a value cannot be walked back to the construction it came from.

The `polydigest` combinator adds the epoch facet (activation timeline + binding root +
null-run-extents) as a **wrapper over** the general `Seal` — not as a field on it.
This keeps an illegal "canonical-layer Seal with an epoch field" state
unrepresentable and keeps the stable Seal decoupled from algorithm churn.

### The leaf proof

A `LeafProof` (`spine/src/leaf_proof.rs`) is the peer of the inclusion proof over
the *same* shared positional topology, packaged as a self-contained witness: a leaf
hash bound to its trusted positional parameters `(index, tree_size, arity)` plus the
path, so a consumer asks one question — `verify(hasher, root)`. It runs over a
**live** tree and is exposed by both CML and CMT; it is not consistency-coupled, and
it is the base case the snapshot proof composes.

### Inclusion and its trust contract

`verify_inclusion` (`spine/src/proof.rs`) binds a leaf hash to a log position by
reconstructing the exact topology from `(index, tree_size, arity)` and rejecting any
deviation; the proof supplies only sibling digests. Those parameters and the `root`
are **trusted** — they must come from an authenticated source (a signed tree head or
trusted checkpoint), never from the proof or caller-untrusted input.

#### Canonical proof encoding and non-malleability

Every accepted step must carry at least one sibling. A zero-sibling step would
represent a promoted (lone-child) node — an inert no-op whose parent equals its
child without hashing — so honest provers omit such steps and the verifier rejects
them (`reconstruct_inclusion_root`). Omitting a promoted step never changes the
computed root, so completeness is preserved; in exchange, a fixed
`(leaf_hash, index, tree_size, root)` admits at most one accepting path (modulo hash
collisions), which closes prepend/insert malleability. This concerns
zero-*sibling* steps only; null-*valued* siblings from a collapse are unaffected.

### Subtree opacity

Any tree's root can be carried as an **opaque leaf** in any other tree: a caller
places the root bytes directly into `Subtree::Leaf(root_bytes)`
(`spine/src/subtree.rs`), which is byte-identical to any other raw-payload leaf
carrying the same bytes. The Spine never branches on a leaf's origin — there is no
`is_embedded` tag. Composition is two independent inclusion verifications, with no
composite proof type. The opacity is a security property: an auditor cannot tell
whether a leaf is a raw payload or a child-tree root, so embedded subtrees cannot be
fingerprinted.

### The opaque metadata channel

`Meta` (`spine/src/metadata.rs`) is an arbitrary, opaque byte buffer attached to a
commitment. The Spine never reads, validates, signs, or branches on its contents —
round-trip fidelity is the only guarantee. The type names no signing scheme; the
fact that an out-of-band tree-head attestation *may* ride here is purely a consumer
convention. This is where the trust a binding or snapshot proof requires is
established, keeping the libraries signature-agnostic.

## Layer 2 — CML and CMT, the single-algorithm canonical libraries

CML and CMT move from the abstract core to a concrete mechanism. Each is a
**single-algorithm**, **epoch-free** canonical structure over the Spine. The
append-only-versus-mutable split is what decides which proofs are sound.

|                       | **CML — Canonical Merkle Log** (`cml`) | **CMT — Canonical Merkle Tree** (`cmt`) |
| :-------------------- | :------------------------------------- | :-------------------------------------- |
| Regime                | append-only                            | mutable (`set` / `get`)                 |
| Representation        | frontier stack (bounded carry)         | rebuild / path-recompute                |
| Consistency proofs    | **yes** (append-only prefix)           | **no** (unsound under mutation)         |
| Inherits from Spine   | spine, canonicalization, inclusion, leaf proof, metadata | same (no consistency)  |
| Adds                  | `seal → Snapshot`, snapshot proof base | per-node multi-hash add                 |
| Epochs / binding      | **none** (added by `polydigest`)       | **none** (added by `polydigest`)        |
| Config                | `k`                                    | `k`                                     |

A standalone CML/CMT is **simpler** than a multi-algorithm engine, because the
multi-algorithm machinery is gone.

### CML — the append-only log

CML (`cml/src/lib.rs`) owns the single-algorithm append-only mechanism: the frontier
carry (the base-`k` reduction schedule), the member-root fold, the append-only
`ConsistencyProof` (`cml/src/consistency.rs`), inclusion and leaf proof generation,
and the structural snapshot facet. It reads one algorithm's view (`AlgView`) over a
borrowed node-reader substrate and never owns the store, so the `polydigest`
combinator can drive **N** views over **one** shared data substrate without
duplicating leaf data.

### CMT — the mutable tree

CMT (`cmt/src/lib.rs`) is the mutable peer. It lets interior cells change
(`set` / `get`), so it keeps **no frontier and no consistency proofs**: the
frontier's "left subtrees are sealed" assumption is unsound under mutation. It is
positional and dense, shares the spine's proof-spine index space, and supports
inclusion proofs, non-membership (inclusion of the null constant via collapse), the
leaf proof, and **per-node multi-hash add** — a single cell gains a digest under a
new algorithm and the root is recomputed by path-recompute at `O(log n)`
(`Cmt::add_algorithm_at`, `cmt/src/tree.rs`). CMT exposes each algorithm's raw
member root and the structural seal; it never folds them into a binding root — that
is `polydigest`'s facet.

## Layer 3 — `polydigest`, the combinator

`polydigest` (`polydigest/src/lib.rs`) is the combinator that adds the polymorphic
dimension. It is **not a composition of independent CML/CMT instances** — that would
duplicate the data and raise per-algorithm cost. It is a **combinator over a single
shared data substrate**: the entries live once; each algorithm is a frontier /
hash-view over them (its only per-algorithm cost is its own hashing). The append-only
driver (`NaryMerkleLog`) holds the shared store plus, per algorithm, a
`{hasher, frontier}` view; its mutable peer is `EpochTree`
(`polydigest/src/mutable.rs`), the same combinator lifting a `Cmt`.

It adds the three concepts the structural core omits:

### The activation timeline

A **committed epoch timeline** per algorithm: a vector of disjoint, ordered
`(start, end)` intervals, with an open final interval for a live algorithm
(`polydigest/src/proof.rs`). It is the source for "is algorithm X active at position p?"
(`committed_active_at`) and "what is the active set?" (`committed_active_algs`);
`validate_committed_epochs` enforces strict sort by algorithm ID, ordered
non-overlapping intervals, and a single trailing open interval. A timeline is
**trivially covered** when every algorithm is active from genesis.

### The null-run-extents

What gets *committed* into each binding root is not the raw timeline but its
geometric consequence: the **null-run-extents** — the maximal aligned `k`-ary blocks
over which an algorithm has no active content. These are the only
per-algorithm-divergent collapse instances, and they are the minimal information
needed to reconstruct a verifier's view of the activation. `null_runs_for_alg`
derives them from the timeline; `serialize_null_runs` is the fixed-width, injective
serialization committed in every binding root.

### The binding root

The **binding root** is the live primary root: the head every per-algorithm root
authenticates against. It is *not* a bespoke hash — it is the same canonicalization
fold (`nary_mr`) applied one level up, over the per-algorithm **member roots as
children** (`combined_root`, `polydigest/src/root.rs`):

```
combined_root(H, member_roots, alg_epochs, tree_size, arity)
  = nary_mr(H,  [MR₀, MR₁, …]  ‖  [H(serialize_null_runs(...))]?)
```

A **member root** is one algorithm's own raw root. The member roots enter the fold
as **opaque digests** — `H` is only ever applied to those digests and to the
null-run serialization, never to another algorithm's security material — so each
algorithm's binding root rests solely on its own hash. This is why no algorithm's
break can weaken another's, even inside the shared head.

Two facts make this a fold rather than a special-cased commitment:

- **Singleton promotion is native.** A registry of one algorithm folds
  `nary_mr(H, [MR₀])`, whose one-child arm promotes to `MR₀`. The binding root *is*
  the member root — there is no promotion predicate, and so no branch to forget.
  This is what makes a single-algorithm tree's root identical to a plain (e.g.
  RFC 9162) root with no binding-root overhead.
- **Coverage is a sibling, present only when informative.** A non-trivial activation
  commits the null-run-extents as one extra coverage child, appended **iff** the
  null runs are non-trivial. A trivially covered structure omits the child; the
  absence of the child *is* the trivial encoding.

### Coupling and the binding proof

A `CouplingProof` (`polydigest/src/proof.rs`) is the primitive that opens *one* binding
root to its children: the per-algorithm raw roots together with the committed
timeline. Its `authenticate` method revalidates structure and recomputes the binding
root via the same `combined_root` fold; on success both the roots and the timeline
are authenticated by the head.

The **binding proof** (`polydigest/src/binding_proof.rs`) is the first-class,
cross-algorithm peer of the inclusion / consistency / leaf / snapshot proofs. It
proves that a set of per-algorithm binding roots (each computed under its own hash)
are mutually consistent — that every algorithm committed to the *same* member-root
tuple and the *same* activation geometry. The binding roots are supplied to `verify`
as **trusted inputs** (`TrustedBindingRoot`); the proof establishes consistency
*given* trusted roots, never their origin. A consumer roots that trust out of band,
via an optional attestation on the opaque metadata channel — the honest trust
contract, exactly as a forged `root` makes `verify_inclusion` vacuous.

### Non-regression invariant

The combinator must not make any one algorithm more expensive or more complex:
atomic multi-tree commit is preserved via the binding root, and one shared data
substrate with a per-algorithm frontier only means no data duplication and no
per-algorithm cost increase.

## The seal lattice, snapshots, and filling

The seal stack is **three monotonic, one-way levels: mutable (CMT) → append-only
(CML) → snapshot**. The Seal is the general structural lattice (Layer 1); the
`polydigest` combinator wraps it.

- **Seal (CMT → CML), one-way.** A CMT's current topology is materialized as a
  frontier and consumed by CML. One-way because the frontier's efficiency invariant
  holds only while semantics stay append-only.
- **`Sealed` — the combinator's snapshot.** `Sealed` (`polydigest/src/sealed.rs`) is the
  `polydigest` combinator's frozen multi-algorithm commitment: the structural `Seal`
  paired with the committed timeline, deriving the binding root. It is a thin wrapper
  over the general `Seal` (the `BoundSnapshot` epoch facet), not an epoch field baked
  into the structural type.
- **The member root, binding root, and run-extents are derived views.** Computed on
  demand from a `Sealed` and never stored, because they are provably derivable: the
  member root is the fold of an algorithm's frontier peaks, the binding root is the
  `combined_root` fold, and the run-extents are the `height >= 1` frontier nodes
  (pure `(tree_size, arity)` geometry).
- **resume** (`polydigest/src/tree.rs`) reopens an append-only log onto the committed
  frontier and appends forward. It is **data-free**: only the peaks are carried, so a
  resumed log cannot read the committed past — exactly the one-way guarantee.
- **fill** (`polydigest/src/filling.rs`) is the **trustless** path. It consumes the
  `Sealed` *and* the real historical leaf data, rebuilds a full readable tree, and
  **verifies the rebuilt binding root against the committed one**. Both inputs are
  mandatory: because a log abstracts its leaves by hash, only the data-holding
  operator can fill. With activation gaps it gains gap-aware semantics — re-deriving
  a gapped algorithm's gapless history by consuming the committed null-run-extents.
  Its purpose is to raise the certainty of the past, not to migrate.
- **No revival of a mutable tree from a seal.** A frontier is the *complete*
  continuation state of an append-only log but only *partial* state for a mutable
  tree (mutating an interior cell needs every cell's digest along its ancestor path,
  and the seal kept only the peaks). The way to a readable tree over committed data
  is `fill`.

### The snapshot proof

The **snapshot proof** (`polydigest/src/snapshot_proof.rs`) is the aggregate peer of the
other proofs, answering "are these leaves legitimately in the sealed commitment?" in
one self-contained witness. Its base case is the spine leaf proof: a sequence of
leaf proofs verifies against the sealed member roots, and the member roots bind to
the **trusted** binding roots (the same `TrustedBindingRoot` contract). One head
recomputation per algorithm binds all the member roots at once.

## Layer 4 — the Epoch instantiations

Concrete, `k`-fixed, named — this is where **"Epoch" lives**, and where the
deliverable is de-branded.

| Instantiation | Composed as | Choices | Role |
| :--- | :--- | :--- | :--- |
| **EML** — Epoch Merkle Log (`eml`) | `polydigest(CML)` | `k = 2`, no prefix, arbitrary subtrees | the general-purpose append-only log |
| **EMT** — Epoch Merkle Tree (`emt`) | `polydigest(CMT)` | `k = 2`, no prefix | the general-purpose mutable tree |

`k = 2` is a sane default, not an opinion: binary spine traversal is cheaply
logarithmic.

**EML** (`eml/src/lib.rs`) fixes `polydigest(CML)` at `k = 2` with no prefix and
re-exports the whole surface, so a consumer reaches the library through `eml::*`.
Root and inclusion proofs are preserved from the prior design; the consistency proof
is upgraded to the MMR prefix-form for durable witnesses.

**EMT** (`emt/src/lib.rs`) fixes `polydigest(CMT)` at `k = 2`, pairing the combinator with
a concrete unprefixed SHA-256 hasher so an application gets a ready mutable tree in a
few lines.

A consumer composes its own application structures over EML/EMT — for example a
single principal tree (a mutable outer tree with an embedded append-only commit log,
joined by the spine's opaque subtree embedding); a CT-style build can supply a
prefixing `Hasher` wrapper over EML. That composition lives at the consumer's layer;
no consumer-specific crate pollutes the library namespace.

The repository's contribution is the **Spine + CML/CMT + `polydigest`**; the
EML/EMT instantiations are thin.

## Dependency graph

```
                    Merkle Spine  (L1, zero deps)
                      ╱           ╲
              CML (L2)            CMT (L2)
                  ╲               ╱
                 polydigest  (L3 combinator over CML/CMT, shared substrate)
                  ╱                    ╲
            EML                        EMT        (L4 instantiations)
   =polydigest(CML)              =polydigest(CMT)
        @k2 plain                    @k2
```

## Formal guarantees

The structural core and the combinator are formally verified in Lean 4
(`proofs/lean/`; see [`../proofs/lean/README.md`](../proofs/lean/README.md) for the
reviewer's guide). Two properties bound what the verification rests on:

- **Sorry-free.** Every theorem in the corpus is complete — no `sorry` placeholder
  appears in any proof.
- **A small trust base — at most four structural axioms.** The entire trusted
  computing base is declared in `proofs/lean/EMLProof/Foundations.lean`: an abstract
  digest type `Digest`, its non-emptiness, the abstract hash `H`, and the serializer
  `digestToBytes`, together with Lean's own built-ins. Collision resistance is
  **not** an axiom — it is discharged as an explicit hypothesis at each use site.

The proof split mirrors the code split: the structural theorems carry no epoch
hypothesis and sit at the **Spine / CML** layer; every binding/epoch theorem
consumes roots as **opaque digests** and sits at the **`polydigest`** layer.

- **Canonicalization (Spine)** — `canonical_unique` (`Canonical.lean`): a structure
  reduces to a unique canonical normal form, the injectivity that pins a layout to
  its root.
- **Inclusion (Spine)** — `kary_inclusion_soundness` (`Kary.lean`) and
  `inclusion_proof_unique`: an accepting canonical proof commits the leaf at the
  claimed position, with at most one accepting path per statement (modulo collision).
- **Leaf proof (Spine)** — `leaf_proof_sound` (`LeafProof.lean`): a leaf proof
  soundly binds a leaf hash to its trusted positional parameters.
- **Consistency (CML)** — `consistency_soundness` and `consistency_append_only`
  (`KaryConsistency.lean`): an accepting consistency proof against the honest current
  root forces the reconstructed old root to the genuine prefix root, and lifts to the
  data-level append-only relation. CMT has no consistency theorem because it has no
  consistency proof.
- **Binding root and coupling (`polydigest`)** — `combinedRoot_binds_timeline`,
  `coupling_extract_sound`: the binding root is the `nary_mr` fold over the
  member-root child digests plus the coverage child, so a fixed root pins the
  member-digest list (modulo collision) and binds the timeline.
- **Binding proof (`polydigest`)** — `binding_root_sound`, `binding_proof_consistent`
  (`BindingProof.lean`): each algorithm's binding root folds under its own hash, and
  mutually consistent trusted binding roots prove agreement on the shared structure.
- **Snapshot proof (`polydigest`)** — `snapshot_proof_sound` (`SnapshotProof.lean`),
  composed from the leaf proof against a sealed commitment.

### Conformance and durability property tests

Beyond the proofs, the conformance oracle is the Lean corpus and the durability
property tests (`eml/tests/proptests.rs`, `polydigest/tests/`). The log uses MMR
**durable witnesses**: each leaf's inclusion path to its peak is permanent and extends
append-only, so a witness generated before an append remains valid after it. Root and
inclusion verification are preserved from the prior design; the consistency proof is
upgraded to the MMR prefix-form. The durability property tests assert witness
permanence across appends.
