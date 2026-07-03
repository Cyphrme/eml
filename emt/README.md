# emt — Epoch Merkle Tree

**Tier L4 — an instantiation.** EMT is the general-purpose **mutable** tree: the
`polydigest` combinator over the single-algorithm canonical-mt engine — 
`polydigest(canonical-mt)` — instantiated at arity **`k = 2`**, with no prefix. 
It is the mutable peer of the append-only `eml` log.

## Role

EMT fixes the proof-spine arity to 2 and pairs the combinator with a concrete
unprefixed SHA-256 hasher, so an application gets a ready mutable tree in a few
lines:

```rust
use emt::Emt;

let mut tree = Emt::new();
tree.set(0, b"genesis".to_vec()).unwrap();
tree.set(1, b"second".to_vec()).unwrap();
let root = tree.root().expect("a non-empty tree has a root");
assert_eq!(tree.get(0), Some(b"genesis".as_slice()));
```

Because it is mutable (`set` / `get`), EMT keeps no frontier and offers no
consistency proofs — that is inherited from `cmt`. It does offer inclusion,
non-membership, and leaf proofs, and per-node multi-hash add.

A consumer can compose a single principal tree — a mutable EMT outer tree with an
embedded append-only `eml` commit log, joined by the spine's opaque subtree
embedding. That composition lives at the consumer's layer; this crate only supplies
the outer mutable tree.

## Place in the layered model

```
merkle-spine → canonical-mt → polydigest → EMT  (this: polydigest(canonical-mt) @ k=2)
```

Compare the sibling instantiation:

- **EML** (`eml`) — the append-only peer, `polydigest(canonical-ml)` @ `k = 2`.

## Further reading

- `polydigest` — the combinator EMT instantiates.
- `canonical-mt` — the single-algorithm mutable engine underneath.
- [`../docs/architecture.md`](../docs/architecture.md) — the full design.
