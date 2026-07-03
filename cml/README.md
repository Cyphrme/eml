# canonical-ml — Canonical Merkle Log

**Tier L2 — a single-algorithm canonical library.** canonical-ml is the **append-only**
engine over the structural Merkle Spine (`merkle-spine`). It is the append-only peer of the
mutable canonical-mt tree; both build on `merkle-spine` and neither depends on the other. 
The one currency they exchange is the spine's general structural `Seal`.

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
`polydigest` combinator drive **N** CML views over **one** shared data substrate without
duplicating leaf data. The activation timeline, the null-run-extents, the binding
root, and coupling are the combinator's facet, not CML's. The structural commitment
a CML seal produces is the general `spine::Seal`; the epoch facet over it is
`polydigest::BoundSnapshot`.

## Place in the layered model

```
merkle-spine  ◄── the structural core
  │
  ├── canonical-ml  ◄── this crate (append-only)
  └── canonical-mt      (mutable)
        │
      polydigest (the combinator that lifts both; polydigest(canonical-ml) is EML)
        │
      EML / EMT / ETL  (k=2 instantiations)
```

## Further reading

- `merkle-spine` — the structural core this library builds on.
- `canonical-mt` — the mutable peer; both exchange `Seal`.
- `polydigest` — the combinator that lifts canonical-ml to EML with the
  activation timeline and binding root.
- [`../docs/architecture.md`](../docs/architecture.md) — the full design.
