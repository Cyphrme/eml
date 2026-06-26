import EMLProof.Kary

/-!
# Durability — peak permanence and the leaf-path-prefix property

The MMR durable-witness guarantee, proven over the shared spine topology
(`EMLProof.Kary`). An inclusion proof for a leaf decomposes leaf → root as
`peakPath ++ bagPath`: the `peakPath` lifts the leaf to its **perfect mountain
peak** (entirely inside a permanent perfect subtree), and the `bagPath` lifts
that peak through the peak bag to the root. This module proves the two facts
that make the `peakPath` *durable* across an append — the property RFC-6962's
rebalancing tree structurally cannot have:

* **Peak permanence** (`peak_permanent`): a leaf's perfect-mountain peak digest
  is byte-identical before and after appending more cells. A formed peak is
  never rewritten — it is `perfectRoot_stable` read at the peak granularity.
* **Leaf-path prefix** (`peakPath_prefix`): the `peakPath` a leaf has at size
  `n` is a **prefix** of its `peakPath` at any later size `n' ≥ n`. As the log
  grows, the leaf's mountain only ever *merges upward* — `frontier_for_size`
  re-decomposes the same leaf into a taller mountain whose low base-`k` digits
  (the original path) are unchanged and a few high digits are appended. The
  witness is extend-only; the durable prefix is never mutated.

Both rest on the structural geometry of the greedy frontier decomposition:
perfect mountains are aligned to their height (`k ^ h ∣ left`), so a merge that
takes a leaf from mountain `(l, h)` to a taller `(l', h')` keeps `index - l` as
the low `h` base-`k` digits of `index - l'`. The `peakPath` is exactly the
base-`k` digit expansion (`digitSteps`), so a prefix at the digit level is a
prefix at the path level.

## Trust base

This module declares **no new axiom**: it reuses `EMLProof.Kary` (hence
`EMLProof.Foundations`) and Mathlib, and its theorems' `#print axioms` is a
subset of the four Foundations axioms (`Digest`, `Digest.nonempty`, `H`,
`digestToBytes`) plus the Lean built-ins.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace NEML

open Nat

/-! ## The peak path

The `peakPath` of a leaf is the base-`k` digit expansion of its offset within
its perfect mountain — `digitSteps k (index - left) height`. It is the leading
(within-mountain) segment of `inclusionSkeleton`; `Kary.lean` already proves it
folds the leaf up to the mountain's `perfectRoot` (`digitFold`). -/

/-- The structural peak path for leaf `index` in the mountain `(left, height)`:
    the base-`k` digit steps that lift the leaf to its perfect-mountain peak. -/
def peakPath (k index left height : Nat) : List (Nat × Nat) :=
  digitSteps k (index - left) height

/-! ## Digit-path prefix arithmetic (pure)

The leaf-path-prefix property is, at heart, a fact about base-`k` digit
expansions: agreeing on the low `h` digits makes the height-`h` digit list a
prefix of any taller one. These lemmas are pure `Nat` arithmetic, independent of
hashing or the frontier. -/

/-- The low `h` base-`k` digits of `off` depend only on `off % k ^ h`: for
    `j < h`, the `j`-th digit `off / k ^ j % k` is unchanged by reducing `off`
    mod `k ^ h`. -/
theorem digit_mod_pow (k off j h : Nat) (hj : j < h) :
    off % k ^ h / k ^ j % k = off / k ^ j % k := by
  have hdvd : k ^ (j + 1) ∣ k ^ h := pow_dvd_pow k (by omega)
  have bridge : ∀ x : Nat, x / k ^ j % k = x % k ^ (j + 1) / k ^ j := by
    intro x; rw [pow_succ, Nat.mod_mul_right_div_self]
  rw [bridge, bridge, Nat.mod_mod_of_dvd off hdvd]

/-- `digitSteps` at height `h` is a prefix of `digitSteps` at any height
    `h' ≥ h` for the **same** offset: the extra `h' - h` high digits are
    appended, the low `h` are shared. -/
theorem digitSteps_take_prefix (k off h h' : Nat) (hle : h ≤ h') :
    digitSteps k off h <+: digitSteps k off h' := by
  rw [digitSteps_eq_map, digitSteps_eq_map]
  have : List.range h <+: List.range h' := by
    rw [show h' = h + (h' - h) from by omega, List.range_add]
    exact List.prefix_append _ _
  exact this.map _

/-- **Digit-path prefix.** If two offsets agree on their low `h` base-`k` digits
    (`a' % k ^ h = a`) and `h ≤ h'`, then `digitSteps k a h` is a prefix of
    `digitSteps k a' h'`. The structural core of leaf-path durability. -/
theorem digitSteps_prefix (k a a' h h' : Nat)
    (hle : h ≤ h') (hagree : a' % k ^ h = a) :
    digitSteps k a h <+: digitSteps k a' h' := by
  have heq : digitSteps k a h = digitSteps k a' h := by
    rw [digitSteps_eq_map, digitSteps_eq_map]
    apply List.map_congr_left
    intro j hj
    rw [List.mem_range] at hj
    subst hagree
    rw [digit_mod_pow k a' j h hj]
  rw [heq]
  exact digitSteps_take_prefix k a' h h' hle

/-! ## Frontier alignment

The greedy perfect-subtree decomposition strips the largest power-of-`k` block
first, so every mountain `(left, height)` is aligned: `k ^ height ∣ left`. This
is what forces a leaf's offset within its mountain to be the low base-`k` digits
of its offset within any *coarser* (taller) mountain it later merges into. -/

/-- **Mountains are height-aligned.** Generalized over `frontierGo`'s offset so
    the induction closes; `frontierForSizeT` is the `off = 0` case below. -/
theorem frontierGo_aligned (k : Nat) (hk : 2 ≤ k) :
    ∀ (n off : Nat), k ^ Nat.log k n ∣ off →
      ∀ lh ∈ frontierGo k off n, k ^ lh.2 ∣ lh.1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro off hdvd lh hmem
    rw [frontierGo] at hmem
    split at hmem
    · simp only [List.not_mem_nil] at hmem
    · next h =>
        push Not at h
        obtain ⟨hn0, _⟩ := h
        rw [List.mem_cons] at hmem
        have hcap : k ^ Nat.log k n ≤ n := Nat.pow_log_le_self k hn0
        have hcappos : 0 < k ^ Nat.log k n := pow_pos (by omega) _
        rcases hmem with rfl | hmem'
        · exact hdvd
        · have hHle : Nat.log k (n - k ^ Nat.log k n) ≤ Nat.log k n :=
            Nat.log_mono_right (by omega)
          have hdvd' : k ^ Nat.log k (n - k ^ Nat.log k n) ∣ (off + k ^ Nat.log k n) :=
            Nat.dvd_add (dvd_trans (pow_dvd_pow k hHle) hdvd) (pow_dvd_pow k hHle)
          exact ih (n - k ^ Nat.log k n) (by omega) (off + k ^ Nat.log k n) hdvd' lh hmem'

/-- Every mountain `(l, h)` in the size-`n` frontier is height-aligned:
    `k ^ h ∣ l`. -/
theorem frontier_aligned (k n l h : Nat) (hk : 2 ≤ k)
    (hmem : (l, h) ∈ frontierForSizeT k n) : k ^ h ∣ l :=
  frontierGo_aligned k hk n 0 (by simp) (l, h) hmem

/-- **Aligned blocks nest by their floor.** If `x` and `y` are both multiples of
    `m > 0`, and `y` lands strictly below the top of the block at `x`
    (`y ≤ p < x + m` for some `p`), then `y ≤ x` — there is no multiple of `m`
    strictly between `x` and `x + m`. The arithmetic backbone of mountain
    nesting, reused for both the `l' ≤ l` direction and its converse. -/
theorem aligned_le_of_lt_top (m x y p : Nat) (hm : 0 < m)
    (hx : m ∣ x) (hy : m ∣ y) (hyp : y ≤ p) (hpt : p < x + m) : y ≤ x := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  by_contra hlt
  push Not at hlt  -- x < y
  have hab : a < b := by
    rw [ha, hb] at hlt
    exact lt_of_mul_lt_mul_left hlt (Nat.zero_le _)
  have : x + m ≤ y := by
    rw [ha, hb]
    calc m * a + m = m * (a + 1) := by ring
      _ ≤ m * b := Nat.mul_le_mul_left _ (by omega)
  omega

/-! ## Mountain growth is append-only on the digit path

The leaf-path-prefix theorem: locating leaf `index` in the size-`n` frontier
gives mountain `(l, h)`; locating it in a larger size-`n'` frontier
(`n ≤ n'`, `index < n`) gives `(l', h')` with `l' ≤ l`, `h ≤ h'`, and the offsets
agreeing on the low `h` digits — so the size-`n` peak path is a prefix of the
size-`n'` peak path. -/

/-- **Mountain merge keeps the low digits.** Given the mountain `(l, h)` of leaf
    `index` at size `n` and its mountain `(l', h')` at the larger size `n'`, the
    merge only widened the block: with `h ≤ h'` and `l' ≤ l` (the geometric
    nesting — both derived from `n ≤ n'`, see `peakPath_prefix`), the offset within
    the larger mountain reduces mod `k ^ h` to the offset within the smaller —
    `(index - l') % k ^ h = index - l`. This is what makes the size-`n` digit
    path the low digits of the size-`n'` digit path. -/
theorem mountain_digit_agree (k index l h l' h' : Nat) (hk : 2 ≤ k)
    (halL : k ^ h ∣ l) (halL' : k ^ h' ∣ l')
    (hsl : l ≤ index) (hslt : index < l + k ^ h)
    (hsl' : l' ≤ index) (hhh : h ≤ h') (hl'le : l' ≤ l) :
    (index - l') % k ^ h = index - l := by
  have hk0 : 0 < k ^ h := pow_pos (by omega) h
  have hl'h : k ^ h ∣ l' := dvd_trans (pow_dvd_pow k hhh) halL'
  -- index - l' = (l - l') + (index - l); (l - l') a multiple of k^h, (index - l) < k^h.
  have hdvd_diff : k ^ h ∣ (l - l') := Nat.dvd_sub halL hl'h
  obtain ⟨q, hq⟩ := hdvd_diff
  have hrw : index - l' = k ^ h * q + (index - l) := by omega
  rw [hrw, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]

/-- **Frontier nesting characterizes mountain growth.** Once the leaf's mountain
    has grown from `(l, h)` to a taller `(l', h')` with `h ≤ h'`, the merge was
    leftward: `l' ≤ l`. Aligned blocks containing a common point nest — a
    `k ^ h`-multiple `l'` (which `l'` is, since `k ^ h ∣ k ^ h'`) below
    `index < l + k ^ h` cannot exceed `l`.

    The companion fact `h ≤ h'` — that growth raises the height — is the greedy
    monotonicity of `frontier_for_size` under append (`frontier_height_mono`,
    proven from `n ≤ n'`); it is threaded in as `hhh` here so this lemma is the
    pure leftward-merge alignment step. `peakPath_prefix` supplies it from
    `n ≤ n'`, making durability unconditional. -/
theorem frontier_nest (k n n' index l h l' h' : Nat) (hk : 2 ≤ k)
    (hmemsmall : (l, h) ∈ frontierForSizeT k n) (hsl : l ≤ index) (hslt : index < l + k ^ h)
    (hmembig : (l', h') ∈ frontierForSizeT k n') (hsl' : l' ≤ index) (hslt' : index < l' + k ^ h')
    (hhh : h ≤ h') :
    l' ≤ l := by
  have hall : k ^ h ∣ l := frontier_aligned k n l h hk hmemsmall
  have halr : k ^ h' ∣ l' := frontier_aligned k n' l' h' hk hmembig
  have hk0 : 0 < k ^ h := pow_pos (by omega) h
  have hl'h : k ^ h ∣ l' := dvd_trans (pow_dvd_pow k hhh) halr
  exact aligned_le_of_lt_top (k ^ h) l l' index hk0 hall hl'h hsl' (by omega)

/-! ## The durability theorems -/

/-- **Leaf-path prefix (durability).** A leaf's peak path at size `n` is a prefix
    of its peak path at any later size `n' ≥ n`. The witness inside the perfect
    mountain extends append-only as the mountain merges upward; the original path
    is never mutated.

    The hypotheses are the leaf's located mountain at each size — the
    `findFrontier`/`frontier_for_size` covering blocks, here as membership + span
    facts — plus `n ≤ n'`. The mountain growth is now **unconditional**: both
    `h ≤ h'` (height monotonicity, `frontier_height_mono`) and the leftward merge
    `l' ≤ l` (`frontier_nest`) are *derived* from `n ≤ n'`, not assumed. -/
theorem peakPath_prefix (k n n' index l h l' h' : Nat) (hk : 2 ≤ k) (hnn' : n ≤ n')
    (hidx : index < n)
    (hmemsmall : (l, h) ∈ frontierForSizeT k n) (hsl : l ≤ index) (hslt : index < l + k ^ h)
    (hmembig : (l', h') ∈ frontierForSizeT k n') (hsl' : l' ≤ index) (hslt' : index < l' + k ^ h') :
    peakPath k index l h <+: peakPath k index l' h' := by
  -- height monotonicity (the greedy append-only invariant), now PROVEN
  have hhh : h ≤ h' :=
    frontier_height_mono k index n h n' h' hk ⟨l, hmemsmall, hsl, hslt⟩ hidx hnn'
      ⟨l', hmembig, hsl', hslt'⟩
  have hl'le : l' ≤ l :=
    frontier_nest k n n' index l h l' h' hk hmemsmall hsl hslt hmembig hsl' hslt' hhh
  have hall : k ^ h ∣ l := frontier_aligned k n l h hk hmemsmall
  have halr : k ^ h' ∣ l' := frontier_aligned k n' l' h' hk hmembig
  have hagree : (index - l') % k ^ h = index - l :=
    mountain_digit_agree k index l h l' h' hk hall halr hsl hslt hsl' hhh hl'le
  unfold peakPath
  exact digitSteps_prefix k (index - l) (index - l') h h' hhh hagree

/-- **Peak permanence (durability).** A leaf's perfect-mountain peak digest is
    unchanged by appending more cells: the peak hash a witness terminates at is
    permanent. The `perfectRoot` of a mountain `(left, height)` reads only the
    cells inside its span, so cells appended beyond it leave the peak identical —
    this is `perfectRoot_stable` read at the peak (the durable prefix endpoint).
    Combined with `peakPath_prefix`, the whole within-mountain witness is durable:
    the path is extended append-only and folds to the same permanent peak. -/
theorem peak_permanent (k : Nat) (cells extra : List Digest) (left height : Nat)
    (hspan : left + k ^ height ≤ cells.length) :
    perfectRoot k cells left height = perfectRoot k (cells ++ extra) left height :=
  perfectRoot_stable k cells extra height left hspan

/-- **The peak path folds the leaf to its permanent peak.** Reusing `digitFold`:
    folding a leaf through its honest within-mountain digit path reaches the
    mountain's `perfectRoot`. Stated at the peak path's endpoint to make the
    prove-to-peak half explicit alongside `peak_permanent` (the peak is durable)
    and `peakPath_prefix` (the path is extend-only). -/
theorem peakPath_folds_to_peak (k : Nat) (hk : 2 ≤ k) (cells : List Digest)
    (left offset height : Nat) (hoff : offset < k ^ height) :
    foldNary (cells.getD (left + offset) emptyHash)
      (honestDigitPath k cells left offset height)
      = perfectRoot k cells left height := by
  have := digitFold k hk cells left height offset
  rwa [Nat.div_eq_of_lt hoff, Nat.zero_mul, Nat.add_zero] at this

end NEML

/-!
## Trust base (axiom inventory)

This module adds **no axiom**. Every theorem reuses `EMLProof.Kary`
(`digitSteps`, `frontierForSizeT`/`frontierGo`, `perfectRoot`, `foldNary`,
`digitFold`, `perfectRoot_stable`) over the four `Foundations` axioms
(`Digest`, `Digest.nonempty`, `H`, `digestToBytes`) plus the Lean built-ins
(`propext`, `Classical.choice`, `Quot.sound`). `#print axioms` on
`peakPath_prefix`, `peak_permanent`, and `peakPath_folds_to_peak` reports a
subset of those — the durability guarantee rests on nothing new.
-/
