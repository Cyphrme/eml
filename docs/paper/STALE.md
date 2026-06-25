# Stale: this whitepaper predates the four-tier architecture

> [!WARNING]
> The Quarto whitepaper in this directory (`*.qmd`) and its supporting documents
> describe an **earlier single-crate "EML" architecture** and are **stale** against
> the current code and design. They are kept for reference and a future paper
> revision; **do not treat them as the architecture of record.**

The architecture of record is [`../architecture.md`](../architecture.md), and the
crate-level documentation. The repository is now a **four-tier stack of library
crates**:

- **Merkle Spine** (`spine`) — the abstract structural core (canonicalization, the
  proof spine, inclusion/leaf proofs, the general `Seal`). Epoch-free.
- **CML / CMT** (`cml` / `cmt`) — the two single-algorithm canonical libraries over
  the Spine (append-only log and mutable tree). Epoch-free.
- **`epoch`** — the combinator that lifts a CML or CMT across N algorithms over one
  shared data substrate (activation timeline, null-run-extents, binding root).
- **EML / EMT** (`eml` / `emt`) — the concrete `k = 2` instantiations, where "Epoch"
  lives.

## What the whitepaper has wrong relative to the current model

- It describes a single `EML` crate with the structure, proofs, and multi-algorithm
  machinery merged together; that is now split across the four tiers above.
- Its framing of "projection equivalence" and the structural-to-cryptographic
  decoupling predates the `collapse` / `promotion` canonicalization model and the
  two-count boundary (structural count reduces and tracks nothing; only the
  null-run-extent is counted, only at `epoch`).
- It is branded around a specific consumer; the library is now de-branded, and that
  consumer is a downstream composer of EML/EMT, not a crate.

## Stale supporting documents (same cluster)

These feed the whitepaper and carry the same pre-four-tier model:

- [`../models/epoch-merkle-log.md`](../models/epoch-merkle-log.md) — the old
  single-crate EML domain model.
- [`../proofs/projection-equivalence.md`](../proofs/projection-equivalence.md) — a
  definitional mapping against the old `src/log.rs` layout.
- [`../plans/paper-revision.md`](../plans/paper-revision.md) — a completed revision
  plan for this whitepaper, also pre-four-tier.

A future paper revision should re-derive the narrative from
[`../architecture.md`](../architecture.md) and the proof corpus in `proofs/lean/`.
