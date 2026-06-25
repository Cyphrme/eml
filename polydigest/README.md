# polydigest — the combinator

**Tier L3 — the combinator over a shared data substrate.** `polydigest` lifts a
single-algorithm `cml` log or `cmt` tree across **N algorithms over one shared data
substrate**. It depends on `cml` and `cmt` (which depend on `spine`); the
instantiations `eml` / `emt` depend on it.

## Role

`polydigest` is **not** a composition of independent logs — that would duplicate the data
and raise per-algorithm cost. It is a combinator over **one** substrate: the leaf
entries live once, and each algorithm is a frontier / hash-view over them, so its
only per-algorithm cost is its own hashing. The append-only driver
(`NaryMerkleLog`) holds the shared store plus, per algorithm, a `{hasher, frontier}`
view; its mutable peer is `EpochTree` (`polydigest(cmt)`), the same combinator lifting a
`cmt::Cmt`.

It adds the three concepts the structural core (`spine`) deliberately omits:

- **The activation timeline** — the committed epochs that say which algorithm is
  live where (`validate_committed_epochs`, `committed_active_at`,
  `committed_active_algs`).
- **The null-run-extents** — the one logical count, the per-tree-divergent collapse
  (`NullRun`, `null_runs_for_alg`, `serialize_null_runs`). It is the only quantity
  ever counted in the whole stack, retained solely for cross-tree alignment.
- **The binding root** — the atomic multi-tree commitment (`combined_root`), the same
  canonicalization fold applied one level up over the per-algorithm member roots as
  opaque children. It is opened by a `CouplingProof` and proven mutually consistent
  by a `BindingProof`. Member roots enter as opaque digests, so no algorithm's break
  weakens another.

## Snapshots and filling

The combinator's frozen snapshot is `Sealed` — the `BoundSnapshot` epoch facet over
a structural `spine::Seal`; the structural `Seal` carries no epoch field. The `fill`
operation (trustless rebuild over the real leaf data, verified against the committed
binding root) and the aggregate `SnapshotProof` are the verification surfaces over a
`Sealed`.

## Non-regression invariant

The combinator must not make any one algorithm more expensive or more complex:
atomic multi-tree commit is preserved via the binding root, and one shared substrate
with a per-algorithm frontier only means no data duplication and no per-algorithm
cost increase.

## Place in the layered model

```
spine — the structural core
  │
  ├── cml (append-only)   cmt (mutable)
  │        ╲             ╱
  │      polydigest  ◄── this crate (the combinator)
  │         │
  │       EML / EMT  (k=2 instantiations)
```

## Further reading

- `cml` / `cmt` — the single-algorithm engines this combinator drives.
- `eml` / `emt` — the concrete instantiations at `k = 2`.
- [`../docs/architecture.md`](../docs/architecture.md) — the full design.
