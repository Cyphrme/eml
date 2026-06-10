# Formal Proof Walkthrough: Merkle Log Null Soundness & Unsoundness

This document provides a self-contained walkthrough of how the combination of **prefix-free hashing** and **null subtree reduction to a single constant** creates a structural vulnerability if the null digest is a known preimage, and why a **Nothing-Up-My-Sleeve (NUMS)** constant is mathematically required to prevent provers from lying about the log structure.

The corresponding machine-checked Lean 4 proof is located in [EMLProof/Unsoundness.lean](file:///var/home/nrd/git/github.com/Cyphrme/eml/proofs/lean/EMLProof/Unsoundness.lean).

---

## 1. The Core Threat: Structural Substitution Collisions

In a prefix-free Merkle tree (such as `neml`'s structure), there are no domain separation tags (e.g., prepended bytes) to distinguish a leaf node from an internal node or subtree. The hashing rules are simple:
* **Leaf Hash:** $\text{leafHash}(\text{data}) = H(\text{data})$
* **Internal Node Hash:** $\text{nodeHash}(\text{children}) = H(\text{child}_1 \mathbin{\Vert} \text{child}_2 \mathbin{\Vert} \dots)$

To represent empty or inactive slots efficiently in $k$-ary trees, `neml` utilizes **null subtree reduction**:
* Any subtree containing only inactive/empty leaves is reduced directly to a single constant digest: $\text{nullDigest}(L)$. 
* This reduction occurs regardless of the subtree's arity or height.

### The Vulnerability of a "Prefix-Null" (Known Preimage)
If we define the null digest by hashing a known constant or prefix (e.g. `0x00` or the string `"null"`):

$$
\text{nullDigest}(L) = H(\text{prefix\_data})
$$

This creates a severe structural collision:
1. A single active leaf containing the data `prefix_data` has a digest of:

$$
\text{leafHash}(\text{prefix\_data}) = H(\text{prefix\_data}) = \text{nullDigest}(L)
$$

2. Inactive subtrees of any height or depth also evaluate to the digest $\text{nullDigest}(L)$.

Because the hashing is prefix-free, **a single active leaf containing `prefix_data` is cryptographically and syntactically indistinguishable from an empty subtree of arbitrary height.**

---

## 2. How This Combination Allows Provers to Lie

If an attacker can exploit this collision, they can present a forged proof that lies about the existence of data, the active boundaries, and the physical shape of the tree:

### A. Substituting a Leaf for a Subtree
Suppose the log contains a single active leaf at index $i$ with the payload `prefix_data`. 
* Because $\text{leafHash}(\text{prefix\_data}) = \text{nullDigest}(L)$, the prover can swap this leaf for an empty subtree of height $H$.
* The verifier computes the parent hashes. Because both structures evaluate to the exact same digest, the computed root matches.
* The verifier accepts the proof, believing that a large inactive subtree exists at that position, when in reality there was a single active leaf containing data. The prover has successfully lied and deleted active data.

### B. Substituting a Subtree for a Leaf
Conversely, if an index range is completely inactive (empty), it evaluates to `nullDigest(L)`.
* The prover can swap this empty subtree with a single active leaf containing the data `prefix_data`.
* The verifier accepts the proof, believing that the user stored the data `prefix_data` at that position, when in fact the slot was empty. The prover has successfully fabricated history.

---

## 3. The Lean Formalization of the Contradiction

To mathematically guarantee soundness, the log must satisfy **Theorem 3 (Null Path Isolation / Inactivity Binding)**:

```lean
theorem contains_leaf_neq_null (L : Nat) (t : NaryTree (List UInt8)) (h : ContainsLeaf t) :
    eval L t ≠ nullDigest L
```
*In plain English: If a tree `t` recursively contains at least one active leaf node, the evaluation of the tree's hash can never equal the null digest.*

In [Unsoundness.lean](file:///var/home/nrd/git/github.com/Cyphrme/eml/proofs/lean/EMLProof/Unsoundness.lean), we prove that if the null digest is a known preimage, this theorem is refuted:

```lean
def PrefixNullModel (L : Nat) (prefix_data : List UInt8) : Prop :=
  nullDigest L = leafHash prefix_data

theorem soundness_violation (L : Nat) (prefix_data : List UInt8)
    (h_model : PrefixNullModel L prefix_data) :
    ∃ (t : NaryTree (List UInt8)), ContainsLeaf t ∧ eval L t = nullDigest L := by
  use NaryTree.leaf prefix_data
  constructor
  · exact ContainsLeaf.leaf prefix_data
  · rw [eval_leaf L prefix_data]
    exact h_model.symm
```

By constructing a single-leaf tree containing `prefix_data`, we show that `ContainsLeaf t` is true, yet it evaluates to `nullDigest L`, establishing a direct contradiction.

---

## 4. How the NUMS Constant Prevents the Attack

A **Nothing-Up-My-Sleeve (NUMS)** constant is derived from a mathematical sequence (the digits of $\pi$) rather than hashing a known preimage.

* **Preimage Resistance:** Finding any input $X$ such that $H(X) = \text{nullDigest}(L)$ requires solving a hard preimage challenge ($2^{8L}$ hash operations in general, or $2^{256}$ operations for SHA-256 where $L = 32$).
* **Perfect Separation:** Because it is computationally impossible to find a payload that hashes to the NUMS constant, no user can ever submit a leaf payload whose hash evaluates to the null digest.

By keeping the domain of active leaf hashes and inactive null digests strictly disjoint, the verifier is guaranteed that no structural substitution can occur, making it impossible for a prover to lie about the tree's data or topology.
