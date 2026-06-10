import EMLProof.NEML

namespace NEML

/--
A "prefix null" model assumes that the null digest is the hash of some known preimage.
We represent this by a definition stating that there exists a prefix
such that its leaf hash equals the null digest.
-/
def PrefixNullModel (L : Nat) (prefix_data : List UInt8) : Prop :=
  nullDigest L = leafHash prefix_data

/--
We prove that under the Prefix Null Model, the soundness theorem `contains_leaf_neq_null`
is violated. That is, we can construct a tree `t` that contains active data (a leaf)
but evaluates to the null digest, which is a contradiction.
-/
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

end NEML
