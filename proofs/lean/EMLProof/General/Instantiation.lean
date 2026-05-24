import EMLProof.General.Duality
import EMLProof.Bridge

/-!
# EML Generalization Instantiations

This module instantiates the generalized shift-reduce duality for a concrete
split policy and merge schedule to demonstrate the completeness of the general
framework without any unproven axioms.
-/

set_option linter.style.emptyLine false
set_option linter.unusedVariables false

/-- A simple linear split policy: splits a tree of size n into a left child of size 1
    and a right child of size n - 1. -/
def linear_split_policy (n : Nat) : Nat := 1

/-- The linear split policy is valid. -/
theorem linear_split_policy_valid : ValidSplitPolicy linear_split_policy := by
  intro n hn
  exact ⟨by simp [linear_split_policy], by simp [linear_split_policy]; omega⟩

instance : Fact (ValidSplitPolicy linear_split_policy) := ⟨linear_split_policy_valid⟩

/-- Auxiliary lemma: forestSizes under the linear split policy yields a list of 1s. -/
theorem forestSizes_linear (n : Nat) :
    forestSizes linear_split_policy n = List.replicate n 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · subst hn0
      simp [forestSizes]
    · by_cases hn1 : n = 1
      · subst hn1
        simp [forestSizes]
      · have hn : n > 1 := by omega
        conv_lhs => unfold forestSizes
        have h_ne : n ≠ 0 := by omega
        have h_ne2 : n ≠ 1 := by omega
        rw [if_neg h_ne, if_neg h_ne2]
        have h_guard : linear_split_policy n > 0 ∧ linear_split_policy n < n := by
          simp [linear_split_policy]; omega
        rw [dif_pos h_guard]
        simp only [linear_split_policy]
        have h_lt : n - 1 < n := by omega
        rw [ih (n - 1) h_lt]
        have h_eq : List.replicate (n - 1) 1 ++ [1] = List.replicate n 1 := by
          have h_eq_rec (k : Nat) : List.replicate k 1 ++ [1] = List.replicate (k + 1) 1 := by
            induction k with
            | zero => rfl
            | succ k ih_k =>
              simp only [List.replicate, List.cons_append, ih_k]
          have h_n_pos : n - 1 + 1 = n := by omega
          rw [← h_n_pos]
          exact h_eq_rec (n - 1)
        rw [h_eq]

/-- The merge schedule of 0 merges at each step is compatible with the linear policy. -/
theorem linear_schedule_compatible :
    AppendConsistent linear_split_policy (fun _ => 0) := by
  intro n
  refine ⟨?_, ?_⟩
  · simp only [List.take_zero, List.sum_nil, Nat.add_zero, List.drop_zero]
    rw [forestSizes_linear, forestSizes_linear]
    rw [List.replicate_succ]
  · intro i hi
    change i < 0 at hi
    omega

/-- The generalized bridge lemma instantiated for the linear split policy and schedule. -/
theorem linear_bridge_lemma {α : Type} (leaves : List (MerkleTree α)) :
    generalized_ctoRoot (fun _ => 0) leaves =
      generalized_mth linear_split_policy leaves := by
  exact generalized_bridge_lemma linear_split_policy (fun _ => 0)
    linear_schedule_compatible leaves
