# pmt — Polymorphic Merkle Tree kernel

The `pmt` crate is the **Layer 1 kernel** of the three-layer architecture:
PMT (kernel) → EML/EMT (engineering libraries) → instantiations. It is the
abstract core shared by every tree built above it. The engineering libraries
(`eml`, `emt`) depend on it; it depends on nothing.

## What it is

PMT provides the non-arbitrary primitives that make multi-algorithm Merkle trees
work — the proof spine, canonicalization, the hasher seam, and the one-way
commitment currency — all without any application concept. No hash algorithm is
baked in. No domain-separation prefix is imposed. No application type appears.

## Place in the 3-layer model

```
┌──────────────────────────────────────────────────────────────────────┐
│ Layer 1 — PMT  (this crate)                                           │
│   proof spine · canonicalization · Hasher seam                        │
│   inclusion · leaf proof · binding proof · combined root · coupling   │
│   Sealed currency · opaque metadata channel                           │
│   depends on nothing                                                  │
└───────────────────────────┬──────────────────────────────────────────┘
                             │
              ┌──────────────┴──────────────────┐
              │ eml (append-only)                 │   emt (mutable)
              │ …                                 │   …
```

## Public surface

### The Hasher seam

[`Hasher`] is the single trait every tree implementation plugs a hash algorithm
into. Implement five required methods (`leaf`, `node`, `empty`, `hash`,
`clone_box`) and the kernel builds any tree shape over it. A sixth method,
`digest_len`, has a default derived from `empty()` and may be overridden for
efficiency. The fixed-width contract — every digest the hasher produces must be
the same constant byte length — is load-bearing for binding-root soundness (the
unprefixed node-hash concatenation is injective only over equal-width children).

### Proof spine (`topology`)

[`frontier_for_size`] decomposes a log of `n` leaves into its frontier of
perfect k-ary subtrees. [`inclusion_skeleton`] derives the exact shape of an
inclusion proof (position and sibling count at every step) from
`(tree_size, arity, index)` alone — the single authority shared by proof
generation and verification to prevent topology drift.

### Canonicalization (`mr`)

[`nary_mr`] applies two always-on primitives over any child sequence:
**promotion** (a lone child is lifted without hashing) and **collapse** (children
of the same value fold to that value; the current realization is the null-only
case where all-null children fold to the null constant). [`evaluate`] recursively
evaluates a [`Subtree`] to its root digest.

### Inclusion and proofs

[`verify_inclusion`] checks an [`InclusionProof`] against a trusted
`(index, tree_size, arity, root)`. [`LeafProof`] packages a leaf hash with its
trusted positional parameters into a self-contained witness; [`BindingProof`]
proves cross-algorithm binding-root consistency.

### The Sealed commitment currency

[`Sealed`] is the one kernel commitment type. Both the append-only log and the
mutable tree seal into it. It carries, per active algorithm, the frontier peaks
(the resumable continuation state), the committed epoch timeline, and an optional
opaque metadata channel ([`Meta`]). Member roots, binding roots, and
run-extents are derived views computed on demand.

### Combined root and coupling

[`combined_root`] is the canonicalization fold over the per-algorithm member
roots. [`CouplingProof`] maps a combined root to the active per-algorithm roots
and committed timeline; [`VerifierConfig`] bounds the fold for DoS mitigation.

### Subtree opacity

A caller carrying a child tree's root as a leaf places the root bytes directly
into `Subtree::Leaf(root_bytes)`. The resulting leaf is byte-identical to any
other raw-payload leaf carrying the same bytes — the kernel never branches on a
leaf's origin (no `is_embedded` tag exists). This opacity is the security
guarantee: an auditor cannot tell from an inclusion proof whether the leaf is a
raw payload or a child-tree root.

## Minimal usage example

```rust
use pmt::{Hasher, Subtree, evaluate, verify_inclusion, within_subtree_path};
use sha2::{Digest, Sha256};

#[derive(Debug)]
struct Sha256Hasher;

impl Hasher for Sha256Hasher {
    fn leaf(&self, data: &[u8]) -> Vec<u8> { Sha256::digest(data).to_vec() }
    fn node(&self, children: &[&[u8]]) -> Vec<u8> {
        let mut h = Sha256::new();
        for c in children { h.update(c); }
        h.finalize().to_vec()
    }
    fn empty(&self) -> Vec<u8> { Sha256::digest(b"").to_vec() }
    fn hash(&self, data: &[u8]) -> Vec<u8> { Sha256::digest(data).to_vec() }
    fn clone_box(&self) -> Box<dyn Hasher> { Box::new(Sha256Hasher) }
}

// Build a two-leaf subtree and verify inclusion of the first leaf.
let h = Sha256Hasher;
let tree = Subtree::Node(vec![
    Subtree::Leaf(b"hello".to_vec()),
    Subtree::Leaf(b"world".to_vec()),
]);
let root = evaluate(&h, &tree);
let leaf_hash = h.leaf(b"hello");

// Generate the inclusion path for leaf 0 inside the subtree.
let path = within_subtree_path(&h, &tree, 0).unwrap();

// Verify: index=0 in a size-2 tree at arity k=2.
assert!(verify_inclusion(&h, &leaf_hash, 0, 2, 2, &path, &root));
```

## Further reading

- `docs/architecture.md` — the full three-layer architecture document.
- `eml/README.md` — the append-only engineering library built over this kernel.
- `emt/README.md` — the mutable engineering library built over this kernel.
