# Formal Proof Walkthrough: Merkle Log Null Soundness & Unsoundness

This document provides a self-contained, mathematically rigorous walkthrough of why a **Nothing-Up-My-Sleeve (NUMS)** constant is required to guarantee the soundness of a prefix-free Merkle log, and why defining a null digest via a known hash preimage (a "prefix null") is insecure.

The corresponding machine-checked Lean 4 proof is located in [`EMLProof/Unsoundness.lean`](file:///var/home/nrd/git/github.com/Cyphrme/eml/proofs/lean/EMLProof/Unsoundness.lean).

---

## 1. How the Merkle Log is Modeled

To understand the proof, we must look at how the Merkle tree structure, hashing, and evaluations are modeled in the Lean formalization ([`EMLProof/NEML.lean`](file:///var/home/nrd/git/github.com/Cyphrme/eml/proofs/lean/EMLProof/NEML.lean)).

### A. The N-ary Tree Model
A Merkle tree is defined as an inductive data type `NaryTree`, which can either be a leaf holding data, or a node containing a list of subtrees:

```lean
inductive NaryTree (α : Type) where
  | leaf (val : α)
  | node (children : List (NaryTree α))
```

To assert that a tree contains at least one leaf node containing actual user data, we define the inductive predicate `ContainsLeaf`:

```lean
inductive ContainsLeaf {α : Type} : NaryTree α → Prop where
  | leaf (val : α) : ContainsLeaf (NaryTree.leaf val)
  | node (children : List (NaryTree α)) (c : NaryTree α) (h_mem : c ∈ children)
      (h_cont : ContainsLeaf c) : ContainsLeaf (NaryTree.node children)
```

### B. Prefix-Free Hashing & Basic Types
In a standard Merkle tree (like Certificate Transparency), inputs are domain-separated by prepending `0x00` to leaves and `0x01` to internal nodes. 

`neml` uses **prefix-free hashing** to allow leaf digests to double as content addresses (so a leaf is just the hash of the raw data, without prepended tags). The hashing environment is defined using the following types and axioms:

```lean
-- Digest is the abstract type of cryptographic hashes
axiom Digest : Type

-- H is the underlying hash function mapping bytes to a Digest
axiom H : List UInt8 → Digest

-- digestToBytes represents the serialization of a Digest to bytes
axiom digestToBytes : Digest → List UInt8

-- numsSeed is the Nothing-Up-My-Sleeve master seed (based on fractional digits of pi)
axiom numsSeed : List UInt8

-- xof is an Extendable-Output Function expanding a seed to length L
axiom xof : List UInt8 → Nat → Digest
```

Using these primitives, the specific digests are defined as:
* **Leaf Hash:** $\text{leafHash}(\text{data}) = H(\text{data})$
* **Internal Node Hash:** $\text{nodeHash}(\text{children}) = H(\text{child}_1 \mathbin{\Vert} \text{child}_2 \mathbin{\Vert} \dots \mathbin{\Vert} \text{child}_m)$
* **Empty Hash:** The constant hash of an empty node ($H([])$).
* **Null Digest:** A constant digest representing inactivity/absence. The parameter `L` represents the target digest length of the active hash algorithm (e.g. 32 bytes for SHA-256):

```lean
noncomputable def leafHash (d : List UInt8) : Digest := H d

noncomputable def nodeHash (children : List Digest) : Digest :=
  H (children.flatMap digestToBytes)

noncomputable def emptyHash : Digest := H []

noncomputable def nullDigest (L : Nat) : Digest := xof numsSeed L
```

### C. Tree Evaluation (`eval`)
Evaluating a tree reduces the structure recursively to a single cryptographic digest:
1. A leaf evaluates to the leaf hash of its data.
2. An empty node evaluates to a constant empty hash.
3. A singleton node (one child) evaluates directly to the child's digest (singleton promotion).
4. A node of arity $\ge 2$ where all children evaluate to the `nullDigest` evaluates directly to the `nullDigest` (flat null promotion).
5. A node of arity $\ge 2$ with at least one active child (i.e. at least one child evaluates to a digest other than `nullDigest`) evaluates to the `nodeHash` of its children's digests.

```lean
axiom eval_leaf : ∀ (L : Nat) (data : List UInt8),
  eval L (NaryTree.leaf data) = leafHash data

axiom eval_flat_null_node : ∀ (L : Nat) (children : List (NaryTree (List UInt8))),
  children.length ≥ 2 →
  (∀ t ∈ children, eval L t = nullDigest L) →
  eval L (NaryTree.node children) = nullDigest L

axiom eval_node_hash : ∀ (L : Nat) (children : List (NaryTree (List UInt8))),
  children.length ≥ 2 →
  (∃ t ∈ children, eval L t ≠ nullDigest L) →
  eval L (NaryTree.node children) = nodeHash (children.map (eval L))
```

---

## 2. The Core Security Invariant: Soundness

In an append-only log, **soundness** means a verifier will never accept an invalid proof. For an epoch-based Merkle tree, a verifier must be guaranteed that:
* Storing actual active data can **never** be spoofed as an empty/inactive (null) node.
* An empty/inactive node can **never** be promoted or substituted for an active data leaf.

In the formal Lean specification, this is captured by **Theorem 3 (Null Path Isolation / Inactivity Binding)**:

```lean
theorem contains_leaf_neq_null (L : Nat) (t : NaryTree (List UInt8)) (h : ContainsLeaf t) :
    eval L t ≠ nullDigest L
```
In plain English: *If a tree `t` recursively contains at least one leaf node with payload data, the evaluation of the tree's hash can never equal the null digest for any algorithm digest length `L`.*

For this theorem to be true, it depends on **three preimage resistance axioms**:
1. `leaf_hash_neq_null`: A leaf hash cannot collide with the null digest ($\forall \text{data}, \text{leafHash}(\text{data}) \neq \text{nullDigest}(L)$).
2. `node_hash_neq_null`: An internal node hash cannot collide with the null digest.
3. `empty_hash_neq_null`: The empty hash cannot collide with the null digest.

---

## 3. Why Hashing a Known Value is Unsound (The Contradiction)

Suppose we define the null digest by hashing a known constant or prefix (e.g. `0x00` or the string `"null"`):
$$\text{nullDigest}(L) = H(\text{prefix})$$

Because the log uses prefix-free hashing, the hash of a leaf containing `prefix` is computed as:
$$\text{leafHash}(\text{prefix}) = H(\text{prefix})$$

This creates a collision where the hash of a real, physical leaf payload is identical to the null digest representation. 

We have formalized this as a theorem in [`Unsoundness.lean`](file:///var/home/nrd/git/github.com/Cyphrme/eml/proofs/lean/EMLProof/Unsoundness.lean):

```lean
def PrefixNullModel (L : Nat) (prefix_data : List UInt8) : Prop :=
  nullDigest L = leafHash prefix_data

theorem soundness_violation (L : Nat) (prefix_data : List UInt8)
    (h_model : PrefixNullModel L prefix_data) :
    ∃ (t : NaryTree (List UInt8)), ContainsLeaf t ∧ eval L t = nullDigest L := by
  -- Pass the leaf directly to avoid let-binding unfolding issues in Lean 4 rw tactics
  use NaryTree.leaf prefix_data
  constructor
  · -- Prove that this tree contains a leaf
    exact ContainsLeaf.leaf prefix_data
  · -- Prove that this tree evaluates to the null digest
    rw [eval_leaf L prefix_data]
    exact h_model.symm
```

### The Breakdown of the Proof:
1. **The Hypothesis:** Assume the null digest is defined as the hash of a known prefix (`PrefixNullModel`).
2. **The Counter-Example:** We construct a tree `t` that consists of a single leaf holding `prefix_data`.
3. **Contains Active Data:** Because `t` is a leaf, it satisfies the predicate `ContainsLeaf t` (proven via `ContainsLeaf.leaf`).
4. **Identical Digest:** The evaluation of `t` reduces to `leafHash prefix_data` (via the `eval_leaf` axiom). Under the hypothesis, this is exactly equal to `nullDigest L`.
5. **The Violation:** We have proven that $\exists t, \text{ContainsLeaf}(t) \wedge \text{eval}(L, t) = \text{nullDigest}(L)$, which directly contradicts Theorem 3. The proof system is now **unsound**.

### The Concrete Attack Scenario
* **Step 1:** A user appends a transaction or record to the Merkle log containing the bytes of `prefix_data`.
* **Step 2:** A malicious server (prover) wants to delete or hide this record from the client.
* **Step 3:** Because the leaf hash of `prefix_data` is exactly equal to the null digest, the prover substitutes the user's active leaf with an empty/inactive subtree in the inclusion proof.
* **Step 4:** The verifier calculates the root hash using the inactive subtree. Because the digests are identical, the computed root matches the signed head.
* **Step 5:** The verifier accepts the proof. The user's active data has been silently deleted/hidden, and the proof system is compromised.

---

## 4. Why the NUMS Constant is Sound

To prevent this collision, the null digest must be preimage-resistant:
* **NUMS Definition:** The null constant is derived from a mathematical constant (the digits of $\pi$) rather than hashing a known preimage.
* **No Known Preimage:** Finding an input $X$ such that $H(X) = \text{NUMS}$ requires solving a hard preimage challenge ($2^{256}$ operations for SHA-256).
* **Perfect Separation:** Because no one can find an input $X$ that evaluates to the NUMS constant, no user can ever submit a leaf payload whose hash equals the null digest.

This guarantees that the domain of active leaf hashes and the null digest remain completely disjoint, ensuring that the `leaf_hash_neq_null` axiom holds, and preventing a prover from ever substituting active data for a null node.
