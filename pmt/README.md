# pmt — compatibility facade (transitional)

The kernel formerly published as `pmt` has been split into two crates:

- **`spine`** — the structural Merkle Spine: canonicalization (collapse +
  promotion), the proof spine, the `Hasher` seam, inclusion and leaf proofs, and
  the general structural `Seal`. Epoch-free; depends on nothing.
- **`epoch`** — the epoch combinator: the activation timeline, the
  null-run-extents, the binding root, coupling, and the `BoundSnapshot` wrapper
  over the seal. Depends on `spine` alone.

This `pmt` crate is now a thin **facade** that re-exports the `spine` surface
verbatim and reconstructs the pre-split combined `Sealed` API (structural facet
plus epoch facet on one type) so existing consumers keep compiling while they
are re-pointed at `spine` / `epoch` directly.

It is **transitional** and carries no logic of its own beyond a delegating shim.
New code should depend on `spine` and/or `epoch` directly.
