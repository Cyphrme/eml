# eml — Epoch Merkle Log

**Tier L4 — an instantiation.** EML is the **general-purpose** append-only log: the
`polydigest` combinator over the single-algorithm `cml` engine — `polydigest(cml)` —
instantiated at arity **`k = 2`**, with no prefix and arbitrary subtrees allowed.
This is one of the three concrete crates where "Epoch" lives.

## Role

EML fixes the one opinion an instantiation makes — the arity — and re-exports the
whole `polydigest` surface, so a consumer reaches the library through `eml::*`. `k = 2`
is a sane default, not an opinion: binary spine traversal is cheaply logarithmic.
The caller's `Hasher` is used directly, with no domain-separation wrapper.

EML uses MMR **durable witnesses**: inclusion and binding-root verification are
preserved from the prior design; the consistency proof is upgraded to the MMR
prefix-form. Conformance is anchored by the Lean corpus and the durability property
tests, not a byte-equality oracle.

The re-exported driver still accepts any arity for callers that need a different
`k`; the `eml::config()` preset and the `new` / `from_storage` constructors fix
`k = 2`.

## Place in the layered model

```
spine → cml → polydigest → EML  (this crate: polydigest(cml) @ k=2, no prefix, subtrees ok)
```

Compare the sibling instantiation:

- **EMT** (`emt`) — the mutable peer, `polydigest(cmt)` @ `k = 2`.

## Further reading

- `polydigest` — the combinator EML instantiates.
- `cml` — the single-algorithm append-only engine underneath.
- [`../docs/architecture.md`](../docs/architecture.md) — the full design.
