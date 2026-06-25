# cml — Canonical Merkle Log

**Tier L2 — a single-algorithm canonical library.** `cml` is the **append-only**
engine over the structural Merkle Spine (`spine`). It is the append-only peer of the
mutable `cmt` tree; both build on `spine` and neither depends on the other. The one
currency they exchange is the spine's general structural `spine::Seal`.

## Role

CML (Canonical Merkle Log) owns one algorithm's append-only mechanism:

- **Frontier carry** — the base-`k` reduction schedule (the bounded continuation
  state), itself an optimization of the spine's proof topology.
- **The member-root fold** — one algorithm's raw root, the fold of its frontier
  peaks.
- **Append-only consistency** — the `ConsistencyProof` (append-only prefix), sound
  here precisely because the log only ever grows. It is the proof a mutable tree
  cannot offer.
- **Inclusion and leaf proof generation**, verified in the spine.
- **The structural snapshot facet** — the frontier peaks a `spine::Seal` freezes,
  and the base case for filling.

## Epoch-free and substrate-borrowing

CML is **epoch-free and multi-algorithm-free**: it reads one algorithm's view over a
*borrowed* node-reader substrate and never owns the store. That is what lets the
`epoch` combinator drive **N** CML views over **one** shared data substrate without
duplicating leaf data. The activation timeline, the null-run-extents, the binding
root, and coupling are the combinator's facet, not CML's. The structural commitment
a CML seal produces is the general `spine::Seal`; the epoch facet over it is
`epoch::BoundSnapshot`.

## Place in the layered model

```
spine  ◄── the structural core
  │
  ├── cml  ◄── this crate (append-only)
  └── cmt      (mutable)
        │
      epoch (the combinator: epoch(cml) is the EML)
        │
      EML / EMT / ETL  (k=2 instantiations)
```

## Further reading

- `spine` — the structural core this library builds on.
- `cmt` — the mutable peer; both exchange `spine::Seal`.
- `epoch` — the combinator that lifts `cml` to `epoch(cml)` (the EML) with the
  activation timeline and binding root.
- [`../docs/architecture.md`](../docs/architecture.md) — the full design.
