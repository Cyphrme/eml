# spine — the Merkle Spine

**Tier L1 — the structural core.** `spine` is the abstract structural engine every
tree in the stack is built over, and the layer whose theorems are the central proof
payoff. It is **epoch-free** and depends on nothing.

## Role

The Spine is a plain canonical Merkle structure — a generic, infinitely reusable
core with no notion of algorithms, activation, or epochs. Everything concrete is
added above it: the single-algorithm libraries (`cml` / `cmt`) and then the `polydigest`
combinator that lifts them across N algorithms.

What the Spine provides:

- **Canonicalization** — `collapse` (same-value siblings fold to that value; null is
  just one value) + `promotion` (a lone child lifts in place of its hashed node).
  The two compose into one confluent reduction to a unique canonical form. Both are
  structural: the count *reduces*, and **nothing is tracked**.
- **The proof spine** — a constant `k`-ary spine whose shape is fixed by
  `(tree_size, arity)`, with n-ary subtrees hanging below it for full generality. A
  single function (`inclusion_skeleton`) derives every proof's shape, so producer
  and verifier never disagree on topology.
- **The `Hasher` seam** — the one hash interface. Prefix domain separation is **not**
  a spine axis; an application that wants it wraps the `Hasher` it passes in. The
  fixed-width contract (one constant digest length per hasher) is load-bearing for
  binding-root injectivity.
- **Inclusion proof** and the self-contained **leaf proof**, both over the shared
  positional topology, verified here (`verify_inclusion`).
- **The general structural `Seal`** — the resumable frontier (peaks) plus an opaque
  metadata channel. A one-way general lattice with **no epoch field**; the `polydigest`
  combinator wraps it to add the binding root.
- **An opaque metadata channel** (`Meta`) — round-trip fidelity only; never read,
  validated, or signed by the library.

## What it deliberately omits

Activation, the committed epoch timeline, the null-run-extents, the binding root,
and coupling are **not** here. They are the `polydigest` combinator's facet (Tier L3),
which lifts this structural engine across N algorithms over one shared data
substrate. The spine names no epoch concept.

## Place in the layered model

```
spine  ◄── the structural core (this crate)
  │
  ├── cml   (append-only, single-algorithm)
  └── cmt   (mutable, single-algorithm)
        │
      polydigest (the combinator: polydigest(cml) / polydigest(cmt))
        │
      EML / EMT / ETL  (k=2 instantiations)
```

## Further reading

- `cml` / `cmt` — the single-algorithm canonical libraries over this core.
- `polydigest` — the combinator that adds the multi-algorithm dimension.
- [`../docs/architecture.md`](../docs/architecture.md) — the full design.
- `proofs/lean/` — the machine-checked structural theorems.
