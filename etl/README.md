# etl — Epoch Transparency Log

**Tier L4 — an instantiation.** ETL is a Certificate Transparency build: the `polydigest`
combinator over the single-algorithm `cml` engine — `polydigest(cml)` — instantiated at
arity **`k = 2`**, with **subtrees banned** (flat-leaf only) and a **prefixed
`Hasher`**. It gives RFC 9162 root equality while keeping crypto-agility.

## Role

ETL fixes two instantiation-local policies on top of the general-purpose EML shape:

- **A prefixed hasher**, domain-separating leaf hashes from inner-node hashes to
  match RFC 9162:
  - `0x00 ‖ data` for leaf hashes
  - `0x01 ‖ left ‖ right` for inner-node hashes
  - `0x02 ‖ b"null"` for the null constant (so null cannot alias a real leaf payload
    under the prefixed scheme)
- **No subtree appends.** A log created with `new` fixes a flat-leaf-only kind.

## RFC 9162 root equality

A single-algorithm-from-genesis ETL computes a root equal to the RFC 9162
`MTH(D[n])` for the same leaf sequence. The reduction at play is **promotion**: the
binding root has exactly one constituent (a lone child), so canonicalization lifts it
in place of the wrapping hashed node, reducing the binding root to the raw
single-algorithm root — the RFC 9162 root by construction.

The prefix is why ETL is a distinct instantiation rather than the default. RFC
9162's leaf/node prefix distinguishes inner from leaf hashes, which **contradicts
general promotion** (a promoted lone child must be indistinguishable from a plain
node). So the prefix is an instantiation-local `Hasher` policy; the unprefixed
general-purpose EML is where promotion applies uniformly.

## Crypto-agility

Epochs and the `add_algorithm` surface are fully active: a second algorithm can be
added and will produce a per-algorithm binding root.

## Place in the layered model

```
spine → cml → polydigest → ETL  (this crate: polydigest(cml) @ k=2, subtrees banned, prefixed)
```

Compare the sibling instantiations:

- **EML** (`eml`) — the general-purpose append-only log, `polydigest(cml)` @ `k = 2`, no
  prefix, subtrees allowed.
- **EMT** (`emt`) — the mutable peer, `polydigest(cmt)` @ `k = 2`.

## Further reading

- `polydigest` — the combinator ETL instantiates.
- `eml` — the general-purpose instantiation ETL specializes (the unprefixed shape).
- [`../docs/architecture.md`](../docs/architecture.md) — the full design.
- [RFC 9162](https://datatracker.ietf.org/doc/html/rfc9162) — Certificate
  Transparency 2.0.
