import EMLProof.Tree

/-!
# EML Binary Carry Arithmetic and Binomial size Properties

This module contains the pure mathematical and arithmetic properties of binomial size structures 
required to establish the frontier stack invariants without assuming unsound associativity.

## Key Mathematical Invariants

1. **Parity and Carry Propagation**:
   - `cto(n)` represents the number of carries triggered when inserting the $n$-th leaf.
   - If the sum of segment sizes $n$ is odd, the smallest segment must have size $1$
     (least significant bit).
   - Halving the segment sizes corresponds to a right shift, reducing the carry count:
     $$\text{cto}(n / 2) = \text{cto}(n) - 1$$

2. **Geometric Doubling**:
   - Trailing set bits of $n$ correspond to segment sizes $2^0, 2^1, \dots, 2^k$.
   - This geometric sequence matches the merge cascade doubling sequence, proved in
     `cto_trailing_geo`.

3. **MTH Slicing**:
   - The batch MTH splits its inputs at the largest power-of-2 boundary. We prove in `mth_split`
     and `mth_merge` that concatenation splits match these boundaries structurally.
-/

set_option linter.style.emptyLine false

/-- If segment sizes are strictly descending powers of 2 summing to idx,
    and cto(idx) = 0, then no segment has size 1. -/
theorem no_size_one_when_cto_zero (sizes : List Nat)
    (h_desc : List.Pairwise (· > ·) sizes)
    (h_pow2 : ∀ s ∈ sizes, ∃ k, s = 2 ^ k)
    (h_cto : cto sizes.sum = 0) :
    ∀ s ∈ sizes, s ≥ 2 := by
  have h_even : sizes.sum % 2 = 0 := by
    by_contra h_ne
    have h_odd : sizes.sum % 2 = 1 := by omega
    have : cto sizes.sum ≥ 1 := by
      rw [cto]; simp [h_odd]
    omega
  intro s hs
  by_contra h_lt
  push Not at h_lt
  obtain ⟨k, hk⟩ := h_pow2 s hs
  have h_k_zero : k = 0 := by
    by_contra h_k_pos
    push Not at h_k_pos
    have : 2 ^ k ≥ 2 := by
      calc 2 ^ k ≥ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 2 := by rfl
    omega
  subst hk; subst h_k_zero
  suffices h_odd : ∀ (l : List Nat),
      List.Pairwise (· > ·) l → (∀ s ∈ l, ∃ k, s = 2 ^ k) → 1 ∈ l →
      l.sum % 2 = 1 by
    have := h_odd sizes h_desc h_pow2 hs
    omega
  intro l
  induction l with
  | nil => intro _ _ h_mem; nomatch h_mem
  | cons hd tl ih =>
    intro h_d h_p h_mem
    simp only [List.sum_cons]
    rcases List.mem_cons.mp h_mem with h_eq | h_in_tl
    · subst h_eq
      have h_tl_empty : tl = [] := by
        by_contra h_ne
        obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil tl h_ne
        have h_gt := (List.pairwise_cons.mp h_d).1 x hx
        obtain ⟨j, hj⟩ := h_p x (List.Mem.tail _ hx)
        have := Nat.one_le_two_pow (n := j); omega
      subst h_tl_empty; simp
    · have h_hd_gt : hd > 1 :=
        (List.pairwise_cons.mp h_d).1 1 h_in_tl
      obtain ⟨j, hj⟩ := h_p hd (List.Mem.head _)
      subst hj
      have h_j_pos : j ≥ 1 := by
        by_contra h
        push Not at h
        interval_cases j
        simp at h_hd_gt
      have h_tl_odd : tl.sum % 2 = 1 :=
        ih (List.Pairwise.of_cons h_d)
          (fun s hs => h_p s (List.Mem.tail _ hs)) h_in_tl
      have h_hd_even : 2 ^ j % 2 = 0 := by
        have : j = j - 1 + 1 := by omega
        rw [this, pow_succ]
        omega
      omega

/-- Sum of strictly descending powers of 2 is strictly less than the first. -/
theorem sum_rest_lt_first (first : Nat) (rest : List Nat)
    (h_first_pow2 : ∃ k, first = 2 ^ k)
    (h_rest_pow2 : ∀ s ∈ rest, ∃ k, s = 2 ^ k)
    (h_desc : List.Pairwise (· > ·) (first :: rest)) :
    rest.sum < first := by
  induction rest generalizing first with
  | nil =>
    obtain ⟨k, hk⟩ := h_first_pow2; subst hk; simp
  | cons hd tl ih =>
    simp only [List.sum_cons]
    have h_hd_lt : hd < first := by
      have := List.pairwise_cons.mp h_desc
      exact this.1 hd (List.Mem.head _)
    have h_hd_pow2 : ∃ j, hd = 2 ^ j :=
      h_rest_pow2 hd (List.Mem.head _)
    have h_tl_pow2 : ∀ s ∈ tl, ∃ k, s = 2 ^ k := by
      intro s hs; exact h_rest_pow2 s (List.Mem.tail _ hs)
    have h_desc_tl : List.Pairwise (· > ·) (hd :: tl) := by
      exact List.Pairwise.sublist
        (List.sublist_cons_self first (hd :: tl)) h_desc
    have h_tl_lt : tl.sum < hd := ih hd h_hd_pow2 h_tl_pow2 h_desc_tl
    obtain ⟨j, hj⟩ := h_hd_pow2
    obtain ⟨k, hk⟩ := h_first_pow2
    subst hj; subst hk
    have h_j_lt_k : j < k := by
      by_contra h_ge
      push Not at h_ge
      have := Nat.pow_le_pow_right (by omega : 1 ≤ 2) h_ge
      omega
    have h_two_j_le : 2 * 2 ^ j ≤ 2 ^ k := by
      calc 2 * 2 ^ j = 2 ^ (j + 1) := by ring
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

/-- largestPow2Lt of a power-of-2 plus a strictly smaller sum is equal to the power of 2 itself. -/
theorem largestPow2Lt_of_desc_segments (first_len rest_total : Nat)
    (h_first_pos : first_len > 0)
    (h_rest_pos : rest_total > 0)
    (h_first_pow2 : ∃ k, first_len = 2 ^ k)
    (h_lt : rest_total < first_len) :
    largestPow2Lt (first_len + rest_total) = first_len := by
  obtain ⟨k, hk⟩ := h_first_pow2
  subst hk
  have h_total_gt_1 : 2 ^ k + rest_total > 1 := by
    have := Nat.one_le_two_pow (n := k)
    omega
  rw [largestPow2Lt_def h_total_gt_1]
  have h_lo : 2 ^ k ≤ 2 ^ k + rest_total - 1 := by omega
  have h_hi : 2 ^ k + rest_total - 1 < 2 ^ (k + 1) := by
    have : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    omega
  have h_log : Nat.log 2 (2 ^ k + rest_total - 1) = k := by
    apply Nat.log_eq_of_pow_le_of_lt_pow
    · exact h_lo
    · exact h_hi
  rw [h_log]

/-- Unfolds mth definition when list length > 1. -/
theorem mth_unfold {α : Type} (leaves : List (MerkleTree α)) (h : leaves.length > 1) :
    mth leaves = MerkleTree.node (mth (leaves.take (largestPow2Lt leaves.length)))
                          (mth (leaves.drop (largestPow2Lt leaves.length))) := by
  match leaves with
  | [] => simp at h
  | [_] => simp at h
  | a :: b :: rest => simp [mth]

/-- Splits MTH over concatenation when the split point matches largestPow2Lt. -/
theorem mth_split {α : Type} (L₁ L₂ : List (MerkleTree α))
    (hL₁ : L₁ ≠ []) (hL₂ : L₂ ≠ [])
    (h_split : largestPow2Lt (L₁.length + L₂.length) = L₁.length) :
    mth (L₁ ++ L₂) = MerkleTree.node (mth L₁) (mth L₂) := by
  have h_len : (L₁ ++ L₂).length > 1 := by
    simp only [List.length_append]
    have h1 : L₁.length > 0 := by
      match L₁ with | [] => contradiction | _ :: _ => simp
    have h2 : L₂.length > 0 := by
      match L₂ with | [] => contradiction | _ :: _ => simp
    omega
  rw [mth_unfold _ h_len]
  simp only [List.length_append, h_split]
  rw [List.take_append_length, List.drop_append_length]

/-- Merging two equal power-of-2 size segments' mth's yields the concatenated mth. -/
theorem mth_merge {α : Type} (L R : List (MerkleTree α)) (k : Nat)
    (hL : L.length = 2 ^ k) (hR : R.length = 2 ^ k) :
    MerkleTree.node (mth L) (mth R) = mth (L ++ R) := by
  symm
  apply mth_split L R
  · intro h; simp [h] at hL; have := Nat.one_le_two_pow (n := k); omega
  · intro h; simp [h] at hR; have := Nat.one_le_two_pow (n := k); omega
  · have h_gt : 2 ^ (k + 1) > 1 := by
      have := Nat.one_le_two_pow (n := k + 1); omega
    simp only [hL, hR]
    have h_sum : 2 ^ k + 2 ^ k = 2 ^ (k + 1) := by ring
    rw [h_sum]
    simp only [largestPow2Lt, Nat.not_le.mpr h_gt, if_false]
    have h_bound_lo : 2 ^ k ≤ 2 ^ (k + 1) - 1 := by omega
    have h_bound_hi : 2 ^ (k + 1) - 1 < 2 ^ (k + 1) := by omega
    rw [Nat.log_eq_of_pow_le_of_lt_pow h_bound_lo h_bound_hi]

/-- Sum of strictly descending powers of 2 strictly bounded by 2^a is strictly less than 2^a. -/
theorem sum_desc_pow2_lt (a : Nat) (tl : List Nat)
    (h_desc : ∀ s ∈ tl, s < 2 ^ a)
    (h_pow2 : ∀ s ∈ tl, ∃ j, s = 2 ^ j)
    (h_pair : List.Pairwise (· > ·) tl) :
    tl.sum < 2 ^ a := by
  induction tl generalizing a with
  | nil => simp
  | cons hd rest ih =>
    simp only [List.sum_cons]
    have h_hd_lt := h_desc hd (by simp)
    have h_rest_pair : rest.Pairwise (· > ·) := by
      exact List.Pairwise.of_cons h_pair
    have h_rest_lt_hd : ∀ s ∈ rest, s < hd := by
      intro s hs
      have := List.pairwise_cons.mp h_pair
      exact this.1 s hs
    obtain ⟨j, hj⟩ := h_pow2 hd (by simp)
    subst hj
    have h_j_lt_a : j < a := by
      by_contra h; push Not at h
      have := Nat.pow_le_pow_right (by omega : 1 ≤ 2) h
      omega
    have h_rest_sum : rest.sum < 2 ^ j := ih j
      h_rest_lt_hd
      (fun s hs => h_pow2 s (by simp [hs]))
      h_rest_pair
    have h1 : 2 ^ j + rest.sum < 2 ^ j + 2 ^ j := by omega
    have h2 : 2 ^ j + 2 ^ j = 2 ^ (j + 1) := by rw [Nat.pow_succ]; ring
    have h3 : 2 ^ (j + 1) ≤ 2 ^ a := by
      apply Nat.pow_le_pow_right (by decide); omega
    omega

/-- In a strictly descending list of powers of 2 with odd sum, the last element is 1. -/
theorem last_is_one_of_odd_sum (sizes : List Nat)
    (h_ne : sizes ≠ [])
    (h_desc : List.Pairwise (· > ·) sizes)
    (h_pow2 : ∀ s ∈ sizes, ∃ j, s = 2 ^ j)
    (h_odd : sizes.sum % 2 = 1) :
    sizes.getLast h_ne = 1 := by
  obtain ⟨j, hj⟩ := h_pow2 _ (List.getLast_mem h_ne)
  by_contra h_ne_1
  rw [hj] at h_ne_1
  have h_j_pos : j ≥ 1 := by
    by_contra h; push Not at h; interval_cases j; simp at h_ne_1
  have h_all_even : ∀ s ∈ sizes, s % 2 = 0 := by
    intro s hs
    obtain ⟨m, hm⟩ := h_pow2 s hs
    subst hm
    have h_m_ge_j : m ≥ j := by
      by_contra h_lt; push Not at h_lt
      have h_pow_lt : 2 ^ m < 2 ^ j := Nat.pow_lt_pow_right (by omega) h_lt
      rw [← List.dropLast_append_getLast h_ne] at hs
      simp only [List.mem_append, List.mem_singleton] at hs
      rcases hs with h_drop | h_eq
      · have := h_desc.rel_dropLast_getLast h_drop; rw [hj] at this; omega
      · rw [h_eq] at h_pow_lt; rw [hj] at h_pow_lt; omega
    exact (Nat.two_pow_mod_two_eq_zero).mpr (by omega)
  have h_sum_even : sizes.sum % 2 = 0 := by
    suffices h : ∀ (l : List Nat), (∀ s ∈ l, s % 2 = 0) → l.sum % 2 = 0 from
      h sizes h_all_even
    intro l
    induction l with
    | nil => simp
    | cons hd tl ih_l =>
      intro h_even
      simp [List.sum_cons]
      have := h_even hd (by simp)
      have := ih_l (fun s hs => h_even s (by simp [hs]))
      omega
  omega

/-- Halving decreases CTO by 1 for odd sums. -/
theorem cto_half_of_odd (n : Nat) (h_odd : n % 2 = 1) :
    cto (n / 2) = cto n - 1 := by
  have : cto n = 1 + cto (n / 2) := by
    conv_lhs => unfold cto
    simp [h_odd]
  omega

/-- Proves that if n mod 2^m = 2^m - 1, then cto n ≥ m. -/
theorem cto_ge_of_mod : ∀ (n m : Nat),
    n % 2 ^ m = 2 ^ m - 1 → cto n ≥ m := by
  intro n m; induction m generalizing n with
  | zero => intro _; omega
  | succ k ih =>
    intro h_mod
    have h_pk_pos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have h_pk1_pos : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
    have h_odd : n % 2 = 1 := by
      have : n % 2 = n % 2 ^ (k + 1) % 2 := by
        rw [Nat.mod_mod_of_dvd]
        exact ⟨2 ^ k, by ring⟩
      rw [this, h_mod]
      have : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      omega
    rw [cto, if_pos h_odd]
    suffices cto (n / 2) ≥ k from by omega
    apply ih
    set q := n / 2 ^ (k + 1) with hq_def
    have h_decomp := Nat.div_add_mod n (2 ^ (k + 1))
    have h_n_succ : n + 1 = 2 ^ (k + 1) * (q + 1) := by
      have : n % 2 ^ (k + 1) + 1 = 2 ^ (k + 1) := by omega
      nlinarith
    have h2k : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    have h_ndiv_succ : n / 2 + 1 = 2 ^ k * (q + 1) := by
      have : n + 1 = 2 * (n / 2 + 1) := by omega
      rw [h2k] at h_n_succ; nlinarith
    have h_ndiv_rearr : n / 2 + 1 = 2 ^ k + q * 2 ^ k := by nlinarith
    have h_n2_eq : n / 2 = 2 ^ k - 1 + q * 2 ^ k := by omega
    rw [h_n2_eq, show 2 ^ k - 1 + q * 2 ^ k = 2 ^ k - 1 + 2 ^ k * q from by ring,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

/-- Halving segments preserves invariants and decreases cto by 1. -/
theorem halved_dropLast_props (sizes : List Nat) (k' : Nat)
    (h_desc : List.Pairwise (· > ·) sizes)
    (h_pow2 : ∀ s ∈ sizes, ∃ j, s = 2 ^ j)
    (h_cto : cto sizes.sum = k' + 2)
    (h_ne : sizes ≠ [])
    (h_odd : sizes.sum % 2 = 1)
    (h_last : sizes.getLast h_ne = 1) :
    let dl := sizes.dropLast
    let dl2 := dl.map (· / 2)
    List.Pairwise (· > ·) dl2 ∧
    (∀ s ∈ dl2, ∃ j, s = 2 ^ j) ∧
    cto dl2.sum = k' + 1 ∧
    dl2.length = sizes.length - 1 ∧
    (∀ s ∈ dl, ∃ j, j ≥ 1 ∧ s = 2 ^ j) := by
  intro dl dl2
  have h_dl_gt1 : ∀ s ∈ dl, s > 1 := by
    intro s hs
    have : s > sizes.getLast h_ne := h_desc.rel_dropLast_getLast hs
    rw [h_last] at this; exact this
  have h_dl_pow2 : ∀ s ∈ dl, ∃ j, j ≥ 1 ∧ s = 2 ^ j := by
    intro s hs
    obtain ⟨j, hj⟩ := h_pow2 s (List.dropLast_subset sizes hs)
    refine ⟨j, ?_, hj⟩
    by_contra hlt; push Not at hlt
    interval_cases j; simp at hj
    have := h_dl_gt1 s hs; omega
  have h_dl2_desc : List.Pairwise (· > ·) dl2 := by
    change List.Pairwise (· > ·) (dl.map (· / 2))
    rw [List.pairwise_iff_getElem]
    intro i j hil hjl hij
    simp only [List.getElem_map]
    have h_dl_desc : dl.Pairwise (· > ·) := by
      rw [List.pairwise_iff_getElem]
      intro i' j' hi'l hj'l hi'j'
      rw [List.pairwise_iff_getElem] at h_desc
      have h_dl_len : dl.length = sizes.length - 1 := by simp [dl, List.length_dropLast]
      have hi_eq : dl[i'] = sizes[i']'(by omega) := by simp [dl, List.getElem_dropLast]
      have hj_eq : dl[j'] = sizes[j']'(by omega) := by simp [dl, List.getElem_dropLast]
      rw [hi_eq, hj_eq]; exact h_desc i' j' (by omega) (by omega) hi'j'
    rw [List.pairwise_iff_getElem] at h_dl_desc
    have h_dl_len : dl.length = (dl.map (· / 2)).length := by simp
    have h_ij : dl[i] > dl[j] := h_dl_desc i j (by omega) (by omega) hij
    obtain ⟨ei, hei, h_ei⟩ := h_dl_pow2 dl[i] (List.getElem_mem ..)
    obtain ⟨ej, hej, h_ej⟩ := h_dl_pow2 dl[j] (List.getElem_mem ..)
    rw [h_ei, h_ej]
    rw [show 2 ^ ei / 2 = 2 ^ (ei - 1) from by
      conv_lhs => rw [show ei = (ei - 1) + 1 from by omega, pow_succ]
      exact Nat.mul_div_cancel _ (by omega)]
    rw [show 2 ^ ej / 2 = 2 ^ (ej - 1) from by
      conv_lhs => rw [show ej = (ej - 1) + 1 from by omega, pow_succ]
      exact Nat.mul_div_cancel _ (by omega)]
    apply Nat.pow_lt_pow_right (by omega)
    rw [h_ei, h_ej] at h_ij
    by_contra h_le; push Not at h_le
    have h_ei_le_ej : ei ≤ ej := by omega
    have := Nat.pow_le_pow_right (by omega : 1 ≤ 2) h_ei_le_ej
    omega
  have h_dl2_pow2 : ∀ s ∈ dl2, ∃ j, s = 2 ^ j := by
    intro s hs
    simp only [dl2, List.mem_map] at hs
    obtain ⟨x, hx_mem, rfl⟩ := hs
    obtain ⟨j, hj_ge, rfl⟩ := h_dl_pow2 x hx_mem
    exact ⟨j - 1, by rw [Nat.pow_div hj_ge (by omega)]⟩
  have h_dl2_sum : dl2.sum = (sizes.sum - 1) / 2 := by
    have h_dl_sum : dl.sum = sizes.sum - 1 := by
      have h_split := List.dropLast_append_getLast h_ne
      have h_eq : sizes.sum = dl.sum + sizes.getLast h_ne := by
        conv_lhs => rw [← h_split]; simp [List.sum_append, List.sum_cons]
      rw [h_last] at h_eq; omega
    suffices h_half : dl2.sum * 2 = dl.sum from by
      rw [h_dl_sum] at h_half; omega
    suffices h_gen : ∀ (l : List Nat),
        (∀ s ∈ l, ∃ j, j ≥ 1 ∧ s = 2 ^ j) → (l.map (· / 2)).sum * 2 = l.sum from
      h_gen dl h_dl_pow2
    intro l; induction l with
    | nil => simp
    | cons hd tl ih =>
      intro h_pw2
      simp only [List.map, List.sum_cons]
      obtain ⟨j, hj_ge, rfl⟩ := h_pw2 hd (List.mem_cons_self ..)
      have h_div : 2 ^ j / 2 = 2 ^ (j - 1) := by
        conv_lhs => rw [show j = (j - 1) + 1 from by omega, pow_succ]
        exact Nat.mul_div_cancel _ (by omega)
      rw [h_div]
      have ih_res := ih (fun s hs => h_pw2 s (List.mem_cons_of_mem _ hs))
      have h_pow : 2 ^ (j - 1) * 2 = 2 ^ j := by
        conv_rhs => rw [show j = (j - 1) + 1 from by omega, pow_succ]
      linarith
  have h_dl2_cto : cto dl2.sum = k' + 1 := by
    rw [h_dl2_sum]
    have h_half := cto_half_of_odd sizes.sum h_odd
    have h_sum_pos : sizes.sum ≥ 1 := by
      by_contra h
      have h_sum_zero : sizes.sum = 0 := by omega
      rw [h_sum_zero] at h_cto
      simp only [cto_zero] at h_cto
      omega
    have h_div_eq : sizes.sum / 2 = (sizes.sum - 1) / 2 := by
      have := Nat.div_add_mod sizes.sum 2
      have := h_odd; omega
    rw [← h_div_eq]; omega
  have h_dl2_len : dl2.length = sizes.length - 1 := by
    have : dl2.length = dl.length := List.length_map ..
    have : dl.length = sizes.length - 1 := List.length_dropLast ..
    omega
  exact ⟨h_dl2_desc, h_dl2_pow2, h_dl2_cto, h_dl2_len, h_dl_pow2⟩

/-- Descending pow2s with cto(sum) = k+1 have length at least k+1. -/
theorem cto_trailing_geo_len (sizes : List Nat) (k : Nat)
    (h_desc : List.Pairwise (· > ·) sizes)
    (h_pow2 : ∀ s ∈ sizes, ∃ j, s = 2 ^ j)
    (h_cto : cto sizes.sum = k + 1) :
    k + 1 ≤ sizes.length := by
  induction k generalizing sizes with
  | zero =>
    by_contra h
    rcases sizes with _ | ⟨hd, tl⟩
    · simp only [List.sum_nil, cto_zero] at h_cto; omega
    · simp only [List.length_cons] at h; omega
  | succ k' ih =>
    have h_ne : sizes ≠ [] := by intro h; subst h; simp at h_cto
    have h_odd : sizes.sum % 2 = 1 := by
      by_contra h_even
      have h_even_zero : sizes.sum % 2 = 0 := by omega
      have h_cto_zero := cto_even h_even_zero
      omega
    have h_last := last_is_one_of_odd_sum sizes h_ne h_desc h_pow2 h_odd
    obtain ⟨h_dl2_desc, h_dl2_pow2, h_dl2_cto, h_dl2_len, _⟩ :=
      halved_dropLast_props sizes k' h_desc h_pow2 h_cto h_ne h_odd h_last
    have h_len' := ih _ h_dl2_desc h_dl2_pow2 h_dl2_cto
    omega

/-- Geometric trailing set bits run: trailing k+1 segments are 2^0, 2^1, ..., 2^k. -/
theorem cto_trailing_geo (sizes : List Nat) (k : Nat)
    (h_desc : List.Pairwise (· > ·) sizes)
    (h_pow2 : ∀ s ∈ sizes, ∃ j, s = 2 ^ j)
    (h_cto : cto sizes.sum = k + 1)
    (h_len : k + 1 ≤ sizes.length) :
    ∀ (i : Nat) (hi : i < k + 1),
      sizes.get ⟨sizes.length - 1 - i, by omega⟩ = 2 ^ i := by
  induction k generalizing sizes with
  | zero =>
    intro i hi; interval_cases i
    have h_ne : sizes ≠ [] := by intro h; subst h; simp at h_cto
    have h_odd : sizes.sum % 2 = 1 := by
      by_contra h_even
      have h_even_zero : sizes.sum % 2 = 0 := by omega
      have h_cto_zero := cto_even h_even_zero
      omega
    have h_last := last_is_one_of_odd_sum sizes h_ne h_desc h_pow2 h_odd
    simp only [List.get_eq_getElem, Nat.sub_zero]
    rw [← List.getLast_eq_getElem h_ne]
    exact h_last
  | succ k' ih =>
    have h_ne : sizes ≠ [] := by intro h; subst h; simp at h_cto
    have h_odd : sizes.sum % 2 = 1 := by
      by_contra h_even
      have h_even_zero : sizes.sum % 2 = 0 := by omega
      have h_cto_zero := cto_even h_even_zero
      omega
    have h_last := last_is_one_of_odd_sum sizes h_ne h_desc h_pow2 h_odd
    intro i hi
    by_cases h_i0 : i = 0
    · subst h_i0; simp only [List.get_eq_getElem, Nat.sub_zero]
      rw [← List.getLast_eq_getElem h_ne]
      exact h_last
    · obtain ⟨h_dl2_desc, h_dl2_pow2, h_dl2_cto, h_dl2_len, h_dl_pow2⟩ :=
        halved_dropLast_props sizes k' h_desc h_pow2 h_cto h_ne h_odd h_last
      have h_ih_len := cto_trailing_geo_len _ k' h_dl2_desc h_dl2_pow2 h_dl2_cto
      have h_ih := ih _ h_dl2_desc h_dl2_pow2 h_dl2_cto (by omega)
      have h_i_pos : i ≥ 1 := by omega
      have h_idx : sizes.length - 1 - i < sizes.length - 1 := by omega
      have h_dl_len : (sizes.dropLast).length = sizes.length - 1 := List.length_dropLast ..
      have h_sizes_eq_dl : sizes[sizes.length - 1 - i] =
          (sizes.dropLast)[sizes.length - 1 - i]'(by omega) := by
        simp [List.getElem_dropLast]
      have h_dl2_eq : (sizes.dropLast.map (· / 2))[sizes.length - 1 - i]'(by simp; omega) =
          (sizes.dropLast)[sizes.length - 1 - i]'(by omega) / 2 := by
        simp [List.getElem_map]
      have h_idx_eq : (sizes.dropLast.map (· / 2)).length - 1 - (i - 1) =
          sizes.length - 1 - i := by
        simp; omega
      have h_ih_val := h_ih (i - 1) (by omega)
      simp only [List.get_eq_getElem] at h_ih_val
      simp only [List.get_eq_getElem]
      rw [h_sizes_eq_dl]
      obtain ⟨ej, hej, h_ej⟩ := h_dl_pow2 ((sizes.dropLast)[sizes.length - 1 - i]'(by omega))
        (List.getElem_mem ..)
      rw [h_ej]
      have h_dl2_val : (sizes.dropLast.map (· / 2))[sizes.length - 1 - i]'(by simp; omega) =
          2 ^ ej / 2 := by
        simp only [List.getElem_map]; rw [h_ej]
      have h_ej_div : 2 ^ ej / 2 = 2 ^ (ej - 1) := by
        conv_lhs => rw [show ej = (ej - 1) + 1 from by omega, pow_succ]
        exact Nat.mul_div_cancel _ (by omega)
      rw [h_ej_div] at h_dl2_val
      have h_same_idx : (sizes.dropLast.map (· / 2)).length - 1 - (i - 1) =
          sizes.length - 1 - i := by
        simp; omega
      have h_eq_pow : 2 ^ (ej - 1) = 2 ^ (i - 1) := by
        rw [← h_dl2_val, ← h_ih_val]
        congr 1; omega
      have h_ej_eq : ej = i := by
        have := Nat.pow_right_injective (by omega : 2 ≥ 2) h_eq_pow
        omega
      rw [h_ej_eq]
