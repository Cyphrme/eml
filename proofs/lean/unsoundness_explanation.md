# Explanation of NEML Null Soundness & Unsoundness Proof

This document walks through the mathematical and formal reasons why a **Nothing-Up-My-Sleeve (NUMS)** constant is required for the soundness of a prefix-free Merkle log, and why defining a null digest via a known hash preimage (a "prefix null") is insecure.

The corresponding formal Lean 4 proof is located in [`EMLProof/Unsoundness.lean`](file:///var/home/nrd/git/github.com/Cyphrme/eml/proofs/lean/EMLProof/Unsoundness.lean).

---

## 1. The Core Security Invariant: Soundness

In any append-only log, **soundness** means a verifier will never accept an invalid proof. Specifically, for an epoch-based Merkle tree, a verifier must be guaranteed that:
* Storing actual active data can **never** be spoofed as an empty/inactive (null) node.
* An empty/inactive node can **never** be promoted or substituted for an active data leaf.

In the formal Lean specification ([`EMLProof/NEML.lean`](file:///var/home/nrd/git/github.com/Cyphrme/eml/proofs/lean/EMLProof/NEML.lean)), this is captured by **Theorem 3 (Null Path Isolation / Inactivity Binding)**:

```lean
theorem contains_leaf_neq_null (L : Nat) (t : NaryTree (List UInt8)) (h : ContainsLeaf t) :
    eval L t ≠ nullDigest L
```

In plain English: *If a tree `t` recursively contains at least one leaf node with payload data, the evaluation of the tree's hash can never equal the null digest.*

---

## 2. Why Hashing a Known Value is Unsound

Suppose we define the null digest by hashing a known constant or prefix (e.g. `0x00` or the string `"null"`):
$$N_0 = H(\text{prefix})$$

Because the log uses **prefix-free hashing** (to allow leaf hashes to double as independent content addresses), the hash of a leaf containing `prefix` is computed as:
$$\text{leafHash}(\text{prefix}) = H(\text{prefix})$$

This creates a collision where the hash of a real, physical leaf payload is identical to the null digest representation. 

We have formalized this as a theorem in [`Unsoundness.lean`](file:///var/home/nrd/git/github.com/Cyphrme/eml/proofs/lean/EMLProof/Unsoundness.lean):

```lean
def PrefixNullModel (L : Nat) (prefix_data : List UInt8) : Prop :=
  nullDigest L = leafHash prefix_data

theorem soundness_violation (L : Nat) (prefix_data : List UInt8)
    (h_model : PrefixNullModel L prefix_data) :
    ∃ (t : NaryTree (List UInt8)), ContainsLeaf t ∧ eval L t = nullDigest L
```

### The Attack Scenario
1. A user appends a legitimate log entry containing the data `prefix_data`.
2. A malicious server (prover) wants to delete or hide this data from the client.
3. Because the leaf hash of `prefix_data` is exactly equal to the null digest, the prover replaces the user's active leaf with an empty/inactive subtree.
4. The verifier calculates the root hash using the inactive subtree. Because the digests are identical, the computed root matches the signed head.
5. The verifier accepts the proof, unaware that a real data leaf has been deleted.

---

## 3. Why the NUMS Constant is Sound

To prevent this collision, the null digest must be preimage-resistant:
* **NUMS Definition:** The null constant is derived from a mathematical constant (the digits of $\pi$) rather than hashing a known preimage.
* **No Known Preimage:** Finding an input $X$ such that $H(X) = \text{NUMS}$ requires solving a hard preimage challenge ($2^{256}$ operations for SHA-256).
* **Perfect Separation:** Because no one can find an input $X$ that evaluates to the NUMS constant, no user can ever submit a leaf payload whose hash equals the null digest.

This guarantees that the domain of active leaf hashes and the null digest remain completely disjoint, ensuring that a prover can never construct an inclusion proof that successfully substitutes active data for a null node.
