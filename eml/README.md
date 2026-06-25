# eml — Epoch Merkle Log

**Tier L4 — an instantiation.** EML is the **general-purpose** append-only log: the
`epoch` combinator over the single-algorithm `cml` engine — `epoch(cml)` —
instantiated at arity **`k = 2`**, with no prefix and arbitrary subtrees allowed.
This is one of the three concrete crates where "Epoch" lives.

## Role

EML fixes the one opinion an instantiation makes — the arity — and re-exports the
whole `epoch` surface, so a consumer reaches the library through `eml::*`. `k = 2`
is a sane default, not an opinion: binary spine traversal is cheaply logarithmic.
The caller's `Hasher` is used directly, with no domain-separation wrapper (that is
ETL's job).

EML is the **behavioral successor of the historical reference log** and reproduces
its outputs **byte-for-byte on matching shapes** — distinct leaf payloads with no
same-value sibling run. That equality is the correctness marker for the whole
four-tier refactor, checked continuously by the differential oracle (`difftest/`).

The re-exported driver still accepts any arity for callers that need a different
`k`; the `eml::config()` preset and the `new` / `from_storage` constructors fix
`k = 2`.

## Place in the layered model

```
spine → cml → epoch → EML  (this crate: epoch(cml) @ k=2, no prefix, subtrees ok)
```

Compare the sibling instantiations:

- **EMT** (`emt`) — the mutable peer, `epoch(cmt)` @ `k = 2`.
- **ETL** (`etl`) — `epoch(cml)` @ `k = 2`, subtrees banned and prefixed (RFC 9162
  root equality + crypto-agility).

## Further reading

- `epoch` — the combinator EML instantiates.
- `cml` — the single-algorithm append-only engine underneath.
- [`../docs/architecture.md`](../docs/architecture.md) — the full design.
