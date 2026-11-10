# polydigest — the combinator

**Tier L3 — the combinator over a shared data substrate.** `polydigest` lifts a
single-algorithm canonical-ml log or canonical-mt tree across **N algorithms over 
one shared data substrate**. It depends on canonical-ml and canonical-mt (which 
depend on `merkle-spine`); the instantiations `eml` / `emt` depend on it.

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

## Staged appends

Every log mutation is computed in memory before anything is written.
`NaryMerkleLog::stage` returns an owned `Staged`: algorithm activations
(`add_algorithm`) and appends (`append_leaf`, `append_subtree`) apply to it
in call order, and its `root_for` and `size` report exactly what the log
will report once it is committed. `NaryMerkleLog::commit` writes all of its
ops in one atomic `Storage::apply` and then adopts the staged state, with
no `.await` between the two; a failed write leaves the log unchanged, and
dropping a `Staged` writes nothing. This lets a caller derive a value from
the post-append root, and refuse, before anything is durable.

A `Staged` is valid only for the generation of the log it was staged from:
committing it after the log has changed is a contract breach, caught by a
`debug_assert` and not reported as an error. `append_leaf`,
`append_subtree` and `add_algorithm` on the log are stage plus commit.

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
merkle-spine — the structural core
  │
  ├── canonical-ml (append-only)   canonical-mt (mutable)
  │        ╲             ╱
  │      polydigest  ◄── this crate (the combinator)
  │         │
  │       EML / EMT  (k=2 instantiations)
```

## Further reading

- `canonical-ml` / `canonical-mt` — the single-algorithm engines this combinator drives.
- `eml` / `emt` — the concrete instantiations at `k = 2`.
- [`../docs/architecture.md`](../docs/architecture.md) — the full design.
