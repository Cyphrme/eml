import EMLProof.Foundations
import Mathlib.Tactic
import Mathlib.Logic.Encodable.Basic
import Mathlib.Logic.Equiv.List

/-!
# NEML Formal Soundness and Promotion Properties

This module formalizes the N-ary Epoch Merkle Log (NEML) tree structure,
its singleton and flat null promotion rules, and proves their cryptographic soundness
under prefix-free hashing.
-/

namespace NEML

/-- Prefix-free leaf hash: H(data). -/
noncomputable def leafHash (d : List UInt8) : Digest := H d

/-- Prefix-free internal node hash: H(c₁ ‖ c₂ ‖ ... ‖ cₘ). -/
noncomputable def nodeHash (children : List Digest) : Digest :=
  H (children.flatMap digestToBytes)

/-- A collision on the internal node hash: distinct child lists, equal digest.
    A `nodeHash` collision is in particular an `H` collision. (Defined here, by
    `nodeHash`, so both the combined-root fold and the inclusion layer share it.) -/
def NodeHashCollision : Prop := ∃ a b : List Digest, a ≠ b ∧ nodeHash a = nodeHash b

/-- Canonical preimage of the null constant: the literal bytes of `b"null"`.
    Mirrors `neml/src/hasher.rs` (`null() = hash(b"null")`). -/
def nullPreimage : List UInt8 := [0x6e, 0x75, 0x6c, 0x6c]

/-- The null digest `N₀`, defined faithfully as `H` of the null preimage —
    exactly `hash(b"null")` in the Rust hasher.

    The digest-length parameter `L` is retained for compatibility with the
    dynamic-arity evaluator but is vestigial: the shipped `null()` does not
    depend on it, matching the implementation where the null constant is
    length-independent.

    Because `leafHash d = H d` (prefix-free) and `nullDigest _ = H nullPreimage`,
    the identity `leafHash nullPreimage = nullDigest L` holds *by construction*
    (`null_collision` below). This is the leaf/null collision, now expressible
    in the model. It is **correct under Design A+**: A+ does not assume the
    collision away — it renders it inert by reading activity from the
    authenticated epoch timeline rather than from digest null-ness (see the
    "Design A+" section). -/
noncomputable def nullDigest (_L : Nat) : Digest := H nullPreimage

/-- **The leaf/null collision, made expressible — and provable.**
    A genuine leaf whose payload is the 4-byte string `null` hashes to the null
    constant. Under prefix-free hashing this is not a negligible-probability
    event — the preimage is public and trivial. Inactivity therefore cannot be
    soundly inferred from `cell = N₀`; it must be read from the committed epoch
    timeline (Design A+, below). -/
theorem null_collision (L : Nat) : leafHash nullPreimage = nullDigest L := rfl

/-- Inductive N-ary Merkle Tree structure. -/
inductive NaryTree (α : Type) where
  | leaf (val : α)
  | node (children : List (NaryTree α))
  deriving Inhabited

/-- Inductive predicate representing that an NaryTree contains at least one leaf node. -/
inductive ContainsLeaf {α : Type} : NaryTree α → Prop where
  | leaf (val : α) : ContainsLeaf (NaryTree.leaf val)
  | node (children : List (NaryTree α)) (c : NaryTree α) (h_mem : c ∈ children)
      (h_cont : ContainsLeaf c) : ContainsLeaf (NaryTree.node children)


/-- Predicate enforcing that a tree has a fixed arity k.
    This is used to model the log-level fixed-arity tree topology. -/
def HasArity {α : Type} (k : Nat) : NaryTree α → Prop
  | NaryTree.leaf _ => True
  | NaryTree.node children => children.length = k ∧ ∀ c ∈ children, HasArity k c

/-- The "tree of trees" model of NEML:
    The outer log tree is a fixed-arity k tree whose leaves are dynamic-arity subtrees. -/
def IsNEMLTree {α : Type} (k : Nat) (t : NaryTree (NaryTree α)) : Prop :=
  HasArity k t

/-! ## Constructive evaluation under NEML promotion rules

`eval` was previously an `axiom` together with five `eval_*` equation axioms
(six axioms in total). It is now a real `def`; the five equations are derived
lemmas, removing those axioms from the trust base. The case split mirrors
`nary_mr` in `neml/src/mr.rs` and `Compression.lean`'s `evalConstructive`. -/

/-! Structural size metric for termination of the evaluator (`nsize`/`nlsize`).
    Local to NEML; `Compression.lean` carries its own `treeSize`/`listSize` for
    the `Option`-payload variant. -/
mutual
  def nsize {α : Type} : NaryTree α → Nat
    | NaryTree.leaf _ => 1
    | NaryTree.node children => 1 + nlsize children
  def nlsize {α : Type} : List (NaryTree α) → Nat
    | [] => 0
    | c :: cs => 1 + nsize c + nlsize cs
end

mutual
  /-- Recursive evaluation of an N-ary tree under NEML canonicalization rules.
      `L` is the digest length of the active hash algorithm (vestigial; see
      `nullDigest`). Arms: leaf hashing; empty node → `emptyHash`; singleton
      promotion; **general same-value collapse** (all children evaluate to one
      value, arity ≥ 2 → that value); standard node hashing. The all-null
      collapse is the dominant instance of the same-value collapse, not a
      separate rule — `evalAllNull` is its `value = nullDigest` specialization,
      retained because activity is read against `nullDigest`. -/
  noncomputable def eval (L : Nat) : NaryTree (List UInt8) → Digest
    | NaryTree.leaf data => leafHash data
    | NaryTree.node [] => emptyHash
    | NaryTree.node [c] => eval L c
    | NaryTree.node (a :: b :: rest) =>
        let ds := evalMap L (a :: b :: rest)
        if ds.all (· == eval L a) then eval L a
        else nodeHash ds
  termination_by t => nsize t
  decreasing_by
    all_goals simp [nsize, nlsize]
    all_goals omega

  /-- Whether every child of a node evaluates to the null digest — the
      `value = nullDigest` instance of same-value collapse, kept because
      activity is read against the null constant. -/
  noncomputable def evalAllNull (L : Nat) : List (NaryTree (List UInt8)) → Bool
    | [] => true
    | c :: cs => (eval L c == nullDigest L) && evalAllNull L cs
  termination_by cs => nlsize cs
  decreasing_by
    all_goals simp [nlsize]

  /-- Map `eval` over a child list (structural; equals `List.map (eval L)`). -/
  noncomputable def evalMap (L : Nat) : List (NaryTree (List UInt8)) → List Digest
    | [] => []
    | c :: cs => eval L c :: evalMap L cs
  termination_by cs => nlsize cs
  decreasing_by
    all_goals simp [nlsize]
    all_goals omega
end

/-- `evalAllNull` is the decidable reflection of "every child evaluates null". -/
theorem evalAllNull_eq_true_iff (L : Nat) (children : List (NaryTree (List UInt8))) :
    evalAllNull L children = true ↔ ∀ t ∈ children, eval L t = nullDigest L := by
  induction children with
  | nil => simp [evalAllNull]
  | cons c cs ih =>
    simp only [evalAllNull, Bool.and_eq_true, beq_iff_eq, ih, List.mem_cons]
    constructor
    · rintro ⟨hc, hcs⟩ x (rfl | hx)
      · exact hc
      · exact hcs x hx
    · intro h
      exact ⟨h c (Or.inl rfl), fun x hx => h x (Or.inr hx)⟩

/-- `evalMap` agrees with `List.map (eval L)`. -/
theorem evalMap_eq_map (L : Nat) (children : List (NaryTree (List UInt8))) :
    evalMap L children = children.map (eval L) := by
  induction children with
  | nil => simp [evalMap]
  | cons c cs ih => simp [evalMap, ih]

/-- Leaf evaluation equation (was `axiom eval_leaf`). -/
theorem eval_leaf (L : Nat) (data : List UInt8) :
    eval L (NaryTree.leaf data) = leafHash data := by
  simp [eval]

/-- Empty node evaluation equation (was `axiom eval_empty`). -/
theorem eval_empty (L : Nat) :
    eval L (NaryTree.node []) = emptyHash := by
  simp [eval]

/-- Singleton promotion equation (was `axiom eval_singleton_node`). -/
theorem eval_singleton_node (L : Nat) (t : NaryTree (List UInt8)) :
    eval L (NaryTree.node [t]) = eval L t := by
  simp [eval]

/-- The same-value collapse guard, reflected: every child of a node (arity ≥ 2)
    evaluates to the head child's digest. The boolean the `eval` collapse arm
    branches on. -/
theorem evalAllEq_iff (L : Nat) (a b : NaryTree (List UInt8))
    (rest : List (NaryTree (List UInt8))) :
    ((evalMap L (a :: b :: rest)).all (· == eval L a) = true)
      ↔ ∀ t ∈ (a :: b :: rest), eval L t = eval L a := by
  rw [evalMap_eq_map]
  constructor
  · intro h t ht
    have := (List.all_eq_true.mp h) (eval L t) (by
      rw [List.mem_map]; exact ⟨t, ht, rfl⟩)
    simpa using this
  · intro h
    rw [List.all_eq_true]
    intro d hd
    rw [List.mem_map] at hd
    obtain ⟨t, ht, rfl⟩ := hd
    simpa using h t ht

/-- **General same-value collapse equation, arity ≥ 2.** A node all of whose
    children evaluate to one value `v` evaluates to `v`. The all-null collapse
    (`v = nullDigest`) is the dominant instance. -/
theorem eval_collapse_node (L : Nat) (children : List (NaryTree (List UInt8)))
    (h_length : children.length ≥ 2) {v : Digest}
    (h_all_eq : ∀ t ∈ children, eval L t = v) :
    eval L (NaryTree.node children) = v := by
  obtain ⟨a, b, rest, rfl⟩ : ∃ a b rest, children = a :: b :: rest := by
    match children, h_length with
    | a :: b :: rest, _ => exact ⟨a, b, rest, rfl⟩
  have ha : eval L a = v := h_all_eq a (by simp)
  have hall : ∀ t ∈ (a :: b :: rest), eval L t = eval L a := by
    intro t ht; rw [h_all_eq t ht, ha]
  have hguard : (evalMap L (a :: b :: rest)).all (· == eval L a) = true :=
    (evalAllEq_iff L a b rest).mpr hall
  simp only [eval]
  rw [if_pos hguard, ha]

/-- Flat null promotion equation, arity ≥ 2 (was `axiom eval_flat_null_node`).
    The `value = nullDigest` instance of the general collapse. -/
theorem eval_flat_null_node (L : Nat) (children : List (NaryTree (List UInt8)))
    (h_length : children.length ≥ 2)
    (h_all_null : ∀ t ∈ children, eval L t = nullDigest L) :
    eval L (NaryTree.node children) = nullDigest L :=
  eval_collapse_node L children h_length h_all_null

/-- Standard node hashing equation, arity ≥ 2 with two children of different
    value (was `axiom eval_node_hash`, generalized: hashing fires whenever the
    children are *not* all equal, of which "a non-null child amid nulls" is one
    instance). -/
theorem eval_node_hash (L : Nat) (children : List (NaryTree (List UInt8)))
    (h_length : children.length ≥ 2)
    (h_some : ∃ t ∈ children, ∃ u ∈ children, eval L t ≠ eval L u) :
    eval L (NaryTree.node children) = nodeHash (children.map (eval L)) := by
  obtain ⟨a, b, rest, rfl⟩ : ∃ a b rest, children = a :: b :: rest := by
    match children, h_length with
    | a :: b :: rest, _ => exact ⟨a, b, rest, rfl⟩
  have hNot : ¬ ((evalMap L (a :: b :: rest)).all (· == eval L a) = true) := by
    rw [evalAllEq_iff]
    intro hall
    obtain ⟨t, ht, u, hu, hne⟩ := h_some
    exact hne ((hall t ht).trans (hall u hu).symm)
  simp only [eval]
  rw [if_neg hNot, evalMap_eq_map]

/-- **Theorem 1 (Singleton Promotion Soundness).**
    A node with exactly one child evaluates directly to the child's evaluation,
    preserving the digest without hashing. Now a real theorem (no longer an
    `exact <axiom>` restatement). -/
theorem eval_singleton (L : Nat) (t : NaryTree (List UInt8)) :
    eval L (NaryTree.node [t]) = eval L t :=
  eval_singleton_node L t

/-- **Theorem 2 (Flat Null Promotion Soundness).**
    A node with two or more children, all of which evaluate to the null digest,
    evaluates directly to the null digest. This is the null-*valued* collapse
    (N₀); it is unrelated to the rejection of zero-*sibling* proof steps under
    canonical proof encoding (see the inclusion-verifier section). -/
theorem eval_flat_null_promotion (L : Nat) (children : List (NaryTree (List UInt8)))
    (h_length : children.length ≥ 2)
    (h_all_null : ∀ t ∈ children, eval L t = nullDigest L) :
    eval L (NaryTree.node children) = nullDigest L :=
  eval_flat_null_node L children h_length h_all_null

set_option linter.style.longLine false

/-! ## Design A+ — the committed null-run-extents authenticate activity

This section formalizes the Design A+ soundness content. The combined root is a
structural **metaroot**: a tree layer whose preimage commits every algorithm's
root **and** the **null-run-extents** (the activation — they decide which cells
are null projections, and cover exactly the inactive positions). Two consequences
are modeled:

* **Activity is read from the authenticated null-run-extents, never from digest
  null-ness.** This is what renders the `leaf(b"null") = N₀` collision
  (`null_collision`) inert: the inference "cell = N₀ ⇒ inactive" is unsound
  (`inferredActiveFromNull_unsound`), so activity must come from the committed
  runs.
* **The metaroot binds the activation** (`combinedRoot_binds_timeline`): the two
  histories the collision would conflate — identical member roots but null
  structures disagreeing on activity at some `(X, p)` — cannot share a combined
  root unless `H` collides. Inactivity is therefore not forgeable by metadata
  substitution.

The `Timeline` here is the activation the null-run-extents encode; an activity-
equivalent re-encoding of the same active set is the *same* activation (the
commitment is canonical over activity, per
`pmt::null_runs_cover_exactly_the_inactive_positions`). Plus the verification-time
consistency check `inactive ⇒ N₀` (`InactiveImpliesNull`) and its anti-repudiation
consequence (`real_cell_forces_committed_active`).

Mirrors `pmt/src/proof.rs` (`committed_active_at`, `serialize_null_runs`,
`null_runs_for_alg`, `validate_committed_epochs`) and `eml/src/tree.rs`
(`combined_root_at`, `verify_audit_payload`). The metaroot is never
signature-dependent; signing is an orthogonal, snapshot-level act performed after
a snapshot's leaves are verified. -/

/-- An algorithm identifier. -/
abbrev AlgId := Nat

/-- A committed epoch interval `[start, stop)`. `stop = none` encodes an open
    (still-active) interval — the model analogue of the `u64::MAX` end marker in
    the Rust `(u64, u64)` encoding. -/
abbrev CEpoch := Nat × Option Nat

/-- The committed epoch timeline at a snapshot: `(alg_id, intervals)` for every
    registered algorithm, mirroring `alg_epochs : Vec<(u64, Vec<(u64,u64)>)>`. -/
abbrev Timeline := List (AlgId × List CEpoch)

/-- Whether position `i` lies in the committed interval `[start, stop)`. -/
def epochCovers (e : CEpoch) (i : Nat) : Bool :=
  decide (e.1 ≤ i) && (match e.2 with | none => true | some s => decide (i < s))

/-- Whether any of an algorithm's intervals covers position `i`. -/
def inAnyEpoch (eps : List CEpoch) (i : Nat) : Bool :=
  eps.any (fun e => epochCovers e i)

/-- Look up an algorithm's committed intervals. -/
def lookupTimeline (tl : Timeline) (alg : AlgId) : Option (List CEpoch) :=
  (tl.find? (fun p => decide (p.1 = alg))).map Prod.snd

/-- Authenticated activity of `alg` at position `i`, read from the committed
    timeline. `none` iff `alg` has no committed timeline. Mirrors
    `committed_active_at` (`proof.rs`). -/
def committedActiveAt (tl : Timeline) (alg i : Nat) : Option Bool :=
  (lookupTimeline tl alg).map (fun eps => inAnyEpoch eps i)

/-- The *unsound* legacy inference: read activity from digest null-ness
    (cell ≠ N₀ ⇒ active). Modeled only to prove it unsound. -/
noncomputable def inferredActiveFromNull (L : Nat)
    (cells : AlgId → Nat → Digest) (alg i : Nat) : Bool :=
  !(cells alg i == nullDigest L)

/-- **Null-inference is unsound.** A genuine active leaf can hash to the null
    constant (`null_collision`), so reading activity from null-ness misclassifies
    it as inactive: an honest leaf with payload `b"null"` is reported inactive.
    This is exactly why A+ reads activity from the authenticated timeline. -/
theorem inferredActiveFromNull_unsound (L : Nat) :
    ∃ (cells : AlgId → Nat → Digest) (alg i : Nat),
      cells alg i = leafHash nullPreimage ∧
      inferredActiveFromNull L cells alg i = false := by
  refine ⟨(fun _ _ => leafHash nullPreimage), 0, 0, rfl, ?_⟩
  simp only [inferredActiveFromNull, Bool.not_eq_eq_eq_not, Bool.not_false, beq_iff_eq]
  exact null_collision L

/-- The verification-time consistency check enforced by `verify_audit_payload`:
    every position the committed timeline marks *inactive* for an algorithm must
    hold the null constant in that algorithm's tree. One-directional — it never
    constrains active cells, so an active cell whose payload is literally
    `b"null"` (hashing to `N₀`) is permitted; no payload is ever forbidden. -/
def InactiveImpliesNull (L : Nat) (tl : Timeline) (cells : AlgId → Nat → Digest) : Prop :=
  ∀ alg i, committedActiveAt tl alg i = some false → cells alg i = nullDigest L

/-- **A+ anti-repudiation.** Under the committed consistency check, a cell that
    holds a genuine non-null value forces the committed timeline to mark that
    position active: a logger cannot commit a real leaf and later disown it via
    the epochs. (The repudiation defense — `inactive ⇒ N₀` read contrapositively.) -/
theorem real_cell_forces_committed_active
    (L : Nat) (tl : Timeline) (cells : AlgId → Nat → Digest)
    (hcheck : InactiveImpliesNull L tl cells) (alg i : Nat)
    (hreal : cells alg i ≠ nullDigest L) :
    committedActiveAt tl alg i ≠ some false := by
  intro hfalse
  exact hreal (hcheck alg i hfalse)

/-- **A+ revocation side.** Under the consistency check, a committed-inactive
    position genuinely holds `N₀` — no real leaf hides behind a "retired" claim. -/
theorem committed_inactive_is_null
    (L : Nat) (tl : Timeline) (cells : AlgId → Nat → Digest)
    (hcheck : InactiveImpliesNull L tl cells) (alg i : Nat)
    (hinactive : committedActiveAt tl alg i = some false) :
    cells alg i = nullDigest L :=
  hcheck alg i hinactive

/-- A collision on the hash `H`: distinct preimages with equal digest. -/
def HashCollision : Prop := ∃ a b : List UInt8, a ≠ b ∧ H a = H b

/-- Self-delimiting byte encoding of a `Nat`: `n` copies of `0x01` terminated by
    `0x00`. Injective (recoverable from its length). -/
def uNat (n : Nat) : List UInt8 := List.replicate n 1 ++ [0]

theorem uNat_injective : Function.Injective uNat := by
  intro m n h
  have hlen := congrArg List.length h
  simp only [uNat, List.length_append, List.length_replicate, List.length_cons,
    List.length_nil] at hlen
  omega

/-- `uNat 0` is the lone terminator byte. -/
theorem uNat_zero : uNat 0 = [0] := rfl

/-- `uNat (n+1)` prepends one `0x01` mark — definitionally, since `uNat` is a
    `replicate` of marks terminated by `0x00`. -/
theorem uNat_succ (n : Nat) : uNat (n + 1) = 1 :: uNat n := rfl

/-- **`uNat` is self-delimiting (prefix-free).** Because each `uNat n` is a run
    of `0x01` marks closed by a single `0x00`, the boundary is recoverable from
    the byte stream: a concatenation `uNat a ++ s` determines both `a` (the
    leading mark run) and the suffix `s`. This is the parsing primitive behind
    `encTimeline`'s injectivity. -/
theorem uNat_append_injective : ∀ {a b : Nat} {s t : List UInt8},
    uNat a ++ s = uNat b ++ t → a = b ∧ s = t := by
  intro a
  induction a with
  | zero =>
    intro b s t h
    cases b with
    | zero =>
      rw [uNat_zero] at h
      simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and] at h
      exact ⟨rfl, h⟩
    | succ b' =>
      rw [uNat_zero, uNat_succ] at h
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
      exact absurd h.1 (by decide)
  | succ a' ih =>
    intro b s t h
    cases b with
    | zero =>
      rw [uNat_succ, uNat_zero] at h
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
      exact absurd h.1 (by decide)
    | succ b' =>
      rw [uNat_succ, uNat_succ] at h
      simp only [List.cons_append, List.cons.injEq, true_and] at h
      obtain ⟨ha, hst⟩ := ih h
      exact ⟨by omega, hst⟩

/-- Injective byte serialization of the committed **activation** — modeled as the
    `Timeline`, the activity the null-run-extents encode. The combined-root
    preimage commits this; the shipped `pmt::serialize_null_runs` is one concrete
    injective realization (fixed-width big-endian over `(arity, tree_size,
    per-alg null runs)`). The activation and its null-run-extents are two
    encodings of one truth — the null runs cover exactly the inactive positions
    (`pmt::null_runs_cover_exactly_the_inactive_positions`) — so an injective
    encoding of either is an injective encoding of the activity. Built as
    `uNat ∘ encode`, so injectivity is immediate. -/
def encTimeline (tl : Timeline) : List UInt8 := uNat (Encodable.encode tl)

theorem encTimeline_injective : Function.Injective encTimeline :=
  uNat_injective.comp Encodable.encode_injective

/-! ## Fixed-width splitting (the raw-concat parsing primitive)

`nary_mr` concatenates its child digests **with no length prefix**, so the child
*boundaries* of the byte stream are recoverable only if the children share a
width — the `Hasher` fixed-width contract (N32). `flatten_inj_of_eqWidth` is the
proof that, under that hypothesis, the unprefixed concatenation splits uniquely:
two equal-width child lists with the same total bytes and the same count are the
same list. This is the code-side analogue of the digit-width hypothesis N32 added
to the Hasher; a *hypothesis*, not an axiom. It replaces the old model's
`digestToBytes`-injective per-member re-hash as the lever that makes the concat
injective. -/

/-- All elements of a byte-string list share a common width `w`. The
    `Hasher`-contract predicate: combined-root siblings are equal-width digests. -/
def EqWidth (w : Nat) (cs : List (List UInt8)) : Prop := ∀ c ∈ cs, c.length = w

/-- **Fixed-width concat-splitting.** Two lists of equal-width (`w`) byte strings
    with the same flattened concatenation and the same length are equal — the raw
    `nary_mr` concatenation parses uniquely under the fixed-width contract. Proved
    by simultaneous induction, peeling one width-`w` block per step
    (`List.append_inj` on the shared head width). No axiom; a structural fact about
    equal-width chunked concatenation. -/
theorem flatten_inj_of_eqWidth {w : Nat} :
    ∀ {a b : List (List UInt8)}, EqWidth w a → EqWidth w b →
      a.length = b.length → a.flatten = b.flatten → a = b := by
  intro a
  induction a with
  | nil =>
    intro b _ _ hlen _
    exact (List.length_eq_zero_iff.mp hlen.symm).symm
  | cons x xs ih =>
    intro b hwa hwb hlen hflat
    match b with
    | [] => simp at hlen
    | y :: ys =>
      have hxw : x.length = w := hwa x (List.mem_cons_self ..)
      have hyw : y.length = w := hwb y (List.mem_cons_self ..)
      simp only [List.flatten_cons] at hflat
      have hxy : x.length = y.length := by rw [hxw, hyw]
      obtain ⟨hx, hrest⟩ := List.append_inj hflat hxy
      have hwa' : EqWidth w xs := fun c hc => hwa c (List.mem_cons_of_mem _ hc)
      have hwb' : EqWidth w ys := fun c hc => hwb c (List.mem_cons_of_mem _ hc)
      have hlen' : xs.length = ys.length := by simpa using hlen
      rw [hx, ih hwa' hwb' hlen' hrest]

/-! ## The combined root as the raw-concat canonicalization fold (post-N29, D9)

The combined root is no longer a bespoke `H(metaPreimage)` byte-concat. It is the
**canonicalization fold** ([`naryMr`] — collapse + promotion) over the
per-algorithm member roots as children, one level up, with the committed
timeline entering as a single **coverage child** iff it is non-trivial — exactly
`pmt::combined_root`:

```text
combined_root(H, ar, tl) = nary_mr ( (member roots of ar)  ++  [coverage tl]? )
```

The children are fed **raw** to `nary_mr`: the member roots are opaque digest
*bytes* (`Vec<u8>`) and `nary_mr` concatenates them with **no length prefix**
before hashing (`pmt/src/proof.rs::combined_root` → `pmt/src/mr.rs::nary_mr`).
Earlier the Lean model **re-hashed** each member root (`memberDigest e := H e.2`),
making the concatenation trivially injective — but that proved a *different*
construction than the code. This model is faithful: children are the raw member
bytes, the node hash concatenates them raw, and the unprefixed concatenation is
parseable **only under the fixed-width contract** (`Hasher`, N32): siblings of a
combined-root node share a digest width, so the concatenation splits uniquely
(`flatten_inj_of_eqWidth`). A width mismatch is exactly the case `nary_mr`'s
`debug_assert!(children.windows(2).all(|w| w[0].len() == w[1].len()))` rejects.

* **Raw bytes, not re-hashed digests.** A member child is `e.2` verbatim; the
  binding root is `List UInt8`, matching Rust's `Vec<u8>` (no embedding axiom).
* **Genesis promotion is native.** One child (single algorithm, trivial timeline)
  ⇒ `nary_mr [c] = c`: the binding root *is* the raw member root, no node hash.
* **Coverage is a sibling, present only when informative.** A trivial activation
  contributes no coverage child; a non-trivial one appends
  `digestToBytes (H (encTimeline tl))` — the bytes of the coverage hash over the
  committed **null-run-extents** (all algorithms', in every binding root: the
  redundancy physically binds the trees, D12 REVISED).

The structural unit a fixed combined root pins is the **raw child-byte list**, by
a `NodeHashCollisionFor`/`NodeHashCollision` escape — *under the fixed-width
hypothesis* that makes the split unique. Recovering the abstract `ar` *identities*
is not the fold's job: the coupling verifier trusts `expected_active_algs` for IDs
and order, and the fold authenticates the *member-root bytes* under them. -/

/-- A member root as a raw child of the combined-root node: the algorithm's root
    **bytes** `e.2` verbatim, fed raw to `nary_mr` (no per-member re-hash). The
    Rust member roots are already digests (`Vec<u8>`); they enter the
    concatenation unchanged (D9, opaque digests). -/
def memberDigest (e : AlgId × List UInt8) : List UInt8 := e.2

/-- Whether the committed activation is **trivial**: every algorithm is
    open-from-genesis (`[(0, none)]`, the model image of `[(0, u64::MAX)]`) — the
    activity with no null run. Mirrors `pmt::null_runs_are_trivial`; the trivial
    case omits the coverage child (informativeness, not registry cardinality). -/
def timelineTrivial (tl : Timeline) : Bool :=
  tl.all (fun p => p.2 == [(0, none)])

/-- The byte-hash the combined-root level actually computes: `hasher.hash`
    returns *bytes* (`Vec<u8>`), so the deployed node hash is `digestToBytes ∘ H`
    over the raw concatenation. Modeling it as its own function keeps the collision
    lever on exactly the function the verifier compares. -/
noncomputable def hashBytes (x : List UInt8) : List UInt8 := digestToBytes (H x)

/-- A collision in the byte-hash: distinct preimages with equal hashed *bytes*.
    The combined-root level compares `hasher.hash(...)` outputs, so this — not the
    abstract-`Digest` `HashCollision` — is the binding-relevant collision lever.
    It is *implied by* `HashCollision` (equal digests ⇒ equal bytes,
    `hashCollision_imp_hashBytesCollision`), so discharging it is a weaker (hence
    sound) requirement than discharging `HashCollision`. -/
def HashBytesCollision : Prop :=
  ∃ a b : List UInt8, a ≠ b ∧ hashBytes a = hashBytes b

/-- An `H` collision (equal abstract digests) is in particular a byte-hash
    collision (equal serialized bytes). -/
theorem hashCollision_imp_hashBytesCollision (h : HashCollision) : HashBytesCollision := by
  obtain ⟨a, b, hne, heq⟩ := h
  exact ⟨a, b, hne, by simp only [hashBytes, heq]⟩

/-- The **raw** children of the combined-root fold: each member root's bytes
    (`e.2` verbatim), followed by the coverage child — the *bytes* of
    `H(encTimeline tl)` (the committed null-run-extents) — iff the activation is
    non-trivial. Every child is a raw `List UInt8`, fed unprefixed to `nary_mr`. -/
noncomputable def combinedChildren (ar : List (AlgId × List UInt8)) (tl : Timeline) :
    List (List UInt8) :=
  ar.map memberDigest ++ (if timelineTrivial tl then [] else [hashBytes (encTimeline tl)])

/-- The combined-root node hash over **raw** children: `nary_mr`'s genuine-node
    arm — concatenate the child bytes (no length prefix) and byte-hash. The bytes
    of `H(c₀ ‖ … ‖ cₘ)`, matching `pmt::nary_mr`'s `hasher.hash(&concat)`. -/
noncomputable def combNodeHash (children : List (List UInt8)) : List UInt8 :=
  hashBytes children.flatten

/-- The combined-root fold (fixed-`H`), **raw-concat**: empty ⇒ `H []` bytes; one
    child ⇒ that **raw** child (native promotion — `nary_mr [c] = c`, the binding
    root *is* the member bytes); many ⇒ `combNodeHash`. The root is `List UInt8`,
    matching Rust's `Vec<u8>` (no embedding axiom). -/
noncomputable def combFold (children : List (List UInt8)) : List UInt8 :=
  match children with
  | [] => digestToBytes emptyHash
  | [c] => c
  | _ => combNodeHash children

/-- The combined root: the raw-concat canonicalization fold over the member-root
    children (plus a coverage child iff the timeline is non-trivial). Mirrors
    `pmt::combined_root`. -/
noncomputable def combinedRoot (ar : List (AlgId × List UInt8)) (tl : Timeline) : List UInt8 :=
  combFold (combinedChildren ar tl)

/-- `combFold` of a list of length ≥ 2 is `combNodeHash` of that list. -/
theorem combFold_multi {children : List (List UInt8)} (h : children.length ≥ 2) :
    combFold children = combNodeHash children := by
  match children, h with
  | _ :: _ :: _, _ => rfl

/-- The member-root bytes are a length-`ar.length` prefix of the combined-root
    children; in the multi-member regime they make the child list length ≥ 2. -/
theorem combinedChildren_len_ge {ar : List (AlgId × List UInt8)} {tl : Timeline}
    (hmulti : ar.length ≥ 2) : (combinedChildren ar tl).length ≥ 2 := by
  simp only [combinedChildren, List.length_append, List.length_map]
  omega

/-- **The raw-concat fold binds its children — modulo a node-hash collision —
    under the fixed-width hypothesis.** Equal combined roots over equal-width
    child lists of equal length (both ≥ 2) force *equal child lists*, unless the
    node hash collides. The fixed-width hypothesis (`EqWidth w`) is the
    `Hasher`-contract analogue (N32): without it a *different* split of the same
    concatenated bytes would be an equally valid child list and the root would
    fail to bind. With it, equal node-hash bytes split two ways: either the
    concatenations differ (a `combNodeHash`/`H` collision) or they agree and
    `flatten_inj_of_eqWidth` recovers the child list. No re-hash per member; the
    lever is the raw-concat node hash alone. -/
theorem combinedChildren_bound {w : Nat} {ar₁ ar₂ : List (AlgId × List UInt8)}
    {tl₁ tl₂ : Timeline}
    (hw₁ : EqWidth w (combinedChildren ar₁ tl₁)) (hw₂ : EqWidth w (combinedChildren ar₂ tl₂))
    (hlen : (combinedChildren ar₁ tl₁).length = (combinedChildren ar₂ tl₂).length)
    (h₁ : (combinedChildren ar₁ tl₁).length ≥ 2)
    (h₂ : (combinedChildren ar₂ tl₂).length ≥ 2)
    (heq : combinedRoot ar₁ tl₁ = combinedRoot ar₂ tl₂) :
    combinedChildren ar₁ tl₁ = combinedChildren ar₂ tl₂ ∨ HashBytesCollision := by
  simp only [combinedRoot, combFold_multi h₁, combFold_multi h₂] at heq
  by_cases hch : combinedChildren ar₁ tl₁ = combinedChildren ar₂ tl₂
  · exact Or.inl hch
  · -- distinct child lists with equal node hash; under fixed width the
    -- concatenations must differ (else `flatten_inj_of_eqWidth` equates the
    -- lists), so the equal byte-hashes are a genuine `HashBytesCollision`.
    right
    by_cases hflat : (combinedChildren ar₁ tl₁).flatten = (combinedChildren ar₂ tl₂).flatten
    · exact absurd (flatten_inj_of_eqWidth hw₁ hw₂ hlen hflat) hch
    · exact ⟨_, _, hflat, heq⟩

/-- **A+ non-equivocation: a non-trivial combined root binds the committed
    null-run-extents.** Two histories the leaf/null collision would conflate —
    identical member roots `ar` (≥ 2), but distinct *non-trivial* activations
    (distinct null structures) — cannot share a combined root unless the byte-hash
    collides. Under the fixed-width contract the coverage children
    `hashBytes (encTimeline ·)` differ only via a byte-hash collision on the
    distinct timeline encodings; equal combined roots therefore force a collision.
    A trivial activation contributes no coverage child by design. Because the null
    runs cover exactly the inactive positions, binding them binds the activity:
    the verifier reads activity from the *committed* runs, not a separately-trusted
    timeline. -/
theorem combinedRoot_binds_timeline {w : Nat}
    (ar : List (AlgId × List UInt8)) (tl₁ tl₂ : Timeline)
    (hmulti : ar.length ≥ 2)
    (hw₁ : EqWidth w (combinedChildren ar tl₁)) (hw₂ : EqWidth w (combinedChildren ar tl₂))
    (hlen : (combinedChildren ar tl₁).length = (combinedChildren ar tl₂).length)
    (hnt₁ : timelineTrivial tl₁ = false) (hnt₂ : timelineTrivial tl₂ = false)
    (hne : tl₁ ≠ tl₂) (heq : combinedRoot ar tl₁ = combinedRoot ar tl₂) :
    HashBytesCollision := by
  rcases combinedChildren_bound hw₁ hw₂ hlen (combinedChildren_len_ge hmulti)
      (combinedChildren_len_ge hmulti) heq with hch | hcol
  · -- Equal child lists; the member-root prefixes are equal (same `ar`), so the
    -- trailing one-element coverage byte-lists coincide — a byte-hash collision on
    -- the distinct timeline encodings.
    simp only [combinedChildren, hnt₁, hnt₂, Bool.false_eq_true, if_false] at hch
    have hcov : [hashBytes (encTimeline tl₁)] = [hashBytes (encTimeline tl₂)] := by
      have := List.append_cancel_left hch
      simpa only [hashBytes] using this
    have hdb : hashBytes (encTimeline tl₁) = hashBytes (encTimeline tl₂) := by
      simpa using hcov
    exact ⟨encTimeline tl₁, encTimeline tl₂,
      fun he => hne (encTimeline_injective he), hdb⟩
  · exact hcol

/-! ## Coupling-verifier soundness

The abstract binding theorem (`combinedChildren_bound`) upgrades into a soundness
theorem for the *coupling verifier* that clients actually run
(`CouplingProof::authenticate` / `::verify` in `proof.rs`).

The verifier recomputes `combined_root(Hᵢ, active_roots, alg_epochs)` — the
canonicalization fold over the member-root children (plus a coverage child iff
the timeline is non-trivial) — and compares against the trusted combined root; on
success it extracts the target algorithm's root by membership in `active_roots`.

Because the fold consumes the member roots as **raw** child bytes (no length
prefix), an accepting proof pins the *child-byte list* — under the fixed-width
contract that makes the unprefixed concat parseable — not the abstract `ar`
identities. So soundness is: a committed algorithm carries the *same member-root
bytes* as the extracted one, unless the byte-hash collides. The IDs and ordering
are the verifier's trusted `expected_active_algs` inputs, not something the root
must re-establish. The multi-child regime (≥ 2 member roots) is the genuine-node
case; the singleton branch (one member root, where the combined root *is* that
raw root) is trivially sound (the lone extracted root equals the compared root
with no hashing). -/

/-- The coupling verifier's recompute-and-authenticate relation: the presented
    roots `ar` and timeline `tl` fold to the trusted combined root `cr` (the raw
    `Vec<u8>`). Mirrors `CouplingProof::authenticate` (recompute, compare). -/
def CouplingAuthenticates (ar : List (AlgId × List UInt8)) (tl : Timeline) (cr : List UInt8) :
    Prop := combinedRoot ar tl = cr

/-- The full recompute-and-extract accept: authenticate, then return the target
    algorithm's root by membership in the presented active roots. Mirrors
    `CouplingProof::verify` returning `Some(root)` for `(target, root) ∈ ar`. -/
def CouplingExtracts (ar : List (AlgId × List UInt8)) (tl : Timeline) (cr : List UInt8)
    (target : AlgId) (root : List UInt8) : Prop :=
  CouplingAuthenticates ar tl cr ∧ (target, root) ∈ ar

/-- A presented member root is one of the combined-root children. -/
theorem memberDigest_mem_combinedChildren
    {ar : List (AlgId × List UInt8)} {tl : Timeline} {e : AlgId × List UInt8}
    (h : e ∈ ar) : memberDigest e ∈ combinedChildren ar tl := by
  simp only [combinedChildren, List.mem_append, List.mem_map]
  exact Or.inl ⟨e, h, rfl⟩

/-- **Coupling-verifier soundness (raw-concat fold model).** Let `(ar_true,
    tl_true)` be the genuinely committed roots and timeline under combined root
    `cr`, both sides in the multi-child regime (≥ 2 member roots), over the same
    active-set length (`hlen`, the verifier's `active_roots.len() ==
    expected_active_algs.len()` check), and with both child lists equal-width
    (`hw_true`, `hw'` — the `Hasher` fixed-width contract). If a presented coupling
    proof authenticates against `cr` and extracts `(target, root)`, then some
    genuinely committed algorithm carries a member root with the **same bytes** as
    `root` — `∃ e' ∈ ar_true, memberDigest e' = memberDigest (target, root)` —
    unless the byte-hash collides. An accepting coupling proof cannot extract a
    member root no committed algorithm bound, modulo collision. -/
theorem coupling_extract_sound {w : Nat}
    (ar_true ar' : List (AlgId × List UInt8)) (tl_true tl' : Timeline) (cr : List UInt8)
    (target : AlgId) (root : List UInt8)
    (hmulti_true : ar_true.length ≥ 2) (hmulti' : ar'.length ≥ 2)
    (hlen : ar'.length = ar_true.length)
    (hw_true : EqWidth w (combinedChildren ar_true tl_true))
    (hw' : EqWidth w (combinedChildren ar' tl'))
    (hclen : (combinedChildren ar' tl').length = (combinedChildren ar_true tl_true).length)
    (htrue : combinedRoot ar_true tl_true = cr)
    (haccept : CouplingExtracts ar' tl' cr target root) :
    (∃ e' ∈ ar_true, memberDigest e' = memberDigest (target, root)) ∨ HashBytesCollision := by
  obtain ⟨hauth, hmem⟩ := haccept
  have hcr : combinedRoot ar' tl' = combinedRoot ar_true tl_true := hauth.trans htrue.symm
  rcases combinedChildren_bound hw' hw_true hclen (combinedChildren_len_ge hmulti')
      (combinedChildren_len_ge hmulti_true) hcr with hch | hcol
  · -- Equal child lists. The member-root prefixes have equal length (`hlen` via
    -- `length_map`), so append-injectivity splits the shared child list at the
    -- common boundary: the presented member bytes equal the committed ones.
    left
    have hmem' : memberDigest (target, root) ∈ ar'.map memberDigest :=
      List.mem_map.mpr ⟨(target, root), hmem, rfl⟩
    have hplen : (ar'.map memberDigest).length = (ar_true.map memberDigest).length := by
      simp only [List.length_map]; exact hlen
    have hmap : ar'.map memberDigest = ar_true.map memberDigest := by
      simp only [combinedChildren] at hch
      exact List.append_inj_left hch hplen
    have hd : memberDigest (target, root) ∈ ar_true.map memberDigest := hmap ▸ hmem'
    obtain ⟨e', he', hde'⟩ := List.mem_map.mp hd
    exact ⟨e', he', hde'⟩
  · exact Or.inr hcol

/-! ## Per-algorithm combined root (binding root, no security mixing)

The binding proof needs the *same* **raw-concat** fold under each algorithm's
**own** hash `Hᵢ` (D9 — no security mixing). These definitions parameterize the
fold by the hash, so `combinedRootWith Hᵢ` is algorithm `i`'s binding root and
the soundness lever is `NodeHashCollisionFor Hᵢ` — a byte-hash collision in `i`'s
hash alone, never another algorithm's: `Hᵢ` is applied **only** to the raw
concatenation of the member-root bytes (and the coverage child), so no other
algorithm's security material ever enters `Hᵢ`. The fixed-`H` `combinedRoot`
above is the special case `combinedRootWith H`. -/

/-- The per-algorithm byte-hash: `digestToBytes ∘ Hᵢ`, the deployed
    `hasher.hash` for algorithm `i`. Applied only to raw child concatenations. -/
noncomputable def hashBytesWith (Hi : List UInt8 → Digest) (x : List UInt8) : List UInt8 :=
  digestToBytes (Hi x)

/-- Node hash under an arbitrary algorithm hash `Hᵢ`, **raw-concat**:
    `digestToBytes (Hᵢ (c₁ ‖ … ‖ cₘ))` over the raw child bytes — `nary_mr`'s
    genuine-node arm at `Hᵢ` (`pmt::nary_mr`'s `hasher.hash(&concat)`). -/
noncomputable def nodeHashWith (Hi : List UInt8 → Digest) (children : List (List UInt8)) :
    List UInt8 := hashBytesWith Hi children.flatten

/-- A collision in a *specific* algorithm's byte-hash: distinct preimages, equal
    `Hᵢ`-hashed bytes. The per-algorithm analogue of `HashBytesCollision`;
    binding-root security rests on `Hᵢ` alone (D9 — `Hᵢ` never touches another
    algorithm's material). -/
def NodeHashCollisionFor (Hi : List UInt8 → Digest) : Prop :=
  ∃ a b : List UInt8, a ≠ b ∧ hashBytesWith Hi a = hashBytesWith Hi b

/-- A member root as a **raw** child under algorithm `i`'s fold: the root bytes
    `e.2` verbatim (the `Hᵢ` parameter is *not* applied per member — the old
    `Hᵢ e.2` re-hash was the SEV-2b fidelity bug). `Hᵢ` enters only at the node
    hash over the concatenation. Kept hash-parameterized for call-site symmetry
    with the fixed-`H` `memberDigest`. -/
def memberDigestWith (_Hi : List UInt8 → Digest) (e : AlgId × List UInt8) : List UInt8 := e.2

/-- The combined-root **raw** children under `Hᵢ`: the member-root bytes, then the
    coverage child `hashBytesWith Hᵢ (encTimeline tl)` (iff the timeline is
    non-trivial). Every child is raw bytes; `Hᵢ` is applied only inside the
    coverage child's own hash and at the node level. -/
noncomputable def combinedChildrenWith (Hi : List UInt8 → Digest)
    (ar : List (AlgId × List UInt8)) (tl : Timeline) : List (List UInt8) :=
  ar.map (memberDigestWith Hi)
    ++ (if timelineTrivial tl then [] else [hashBytesWith Hi (encTimeline tl)])

/-- `nary_mr` under `Hᵢ`, raw-concat: empty ⇒ `digestToBytes (Hᵢ [])`; one child ⇒
    that **raw** child (promotion — `nary_mr [c] = c`); many ⇒ `nodeHashWith Hᵢ`.
    The binding root is `List UInt8`, matching Rust's `Vec<u8>`. -/
noncomputable def naryMrWith (Hi : List UInt8 → Digest) (children : List (List UInt8)) :
    List UInt8 :=
  match children with
  | [] => digestToBytes (Hi [])
  | [c] => c
  | _ => nodeHashWith Hi children

/-- Algorithm `i`'s binding root: the raw-concat canonicalization fold over the
    member-root children under its own hash `Hᵢ` (coverage child iff non-trivial).
    Mirrors `pmt::combined_root` instantiated at `Hᵢ`. -/
noncomputable def combinedRootWith (Hi : List UInt8 → Digest)
    (ar : List (AlgId × List UInt8)) (tl : Timeline) : List UInt8 :=
  naryMrWith Hi (combinedChildrenWith Hi ar tl)

/-- `naryMrWith` of a length-≥2 list is `nodeHashWith`. -/
theorem naryMrWith_multi (Hi : List UInt8 → Digest) {children : List (List UInt8)}
    (h : children.length ≥ 2) : naryMrWith Hi children = nodeHashWith Hi children := by
  match children, h with
  | _ :: _ :: _, _ => rfl

/-- The per-algorithm child list has length ≥ 2 in the multi-member regime. -/
theorem combinedChildrenWith_len_ge (Hi : List UInt8 → Digest)
    {ar : List (AlgId × List UInt8)} {tl : Timeline} (hmulti : ar.length ≥ 2) :
    (combinedChildrenWith Hi ar tl).length ≥ 2 := by
  simp only [combinedChildrenWith, List.length_append, List.length_map]
  omega

/-- **The per-algorithm raw-concat fold binds its children — under fixed width —
    modulo `Hᵢ`'s byte-hash collision.** Equal binding roots over equal-width
    child lists of equal length (both ≥ 2) force equal child lists, unless `Hᵢ`'s
    byte-hash collides — `i`'s security alone, no mixing. The fixed-width
    hypothesis (`EqWidth w`, the `Hasher` contract) is what makes the unprefixed
    concat parseable; with it, equal node hashes split into either a genuine
    `Hᵢ`-collision (distinct concatenations) or, via `flatten_inj_of_eqWidth`,
    equal child lists. -/
theorem combinedChildrenWith_bound (Hi : List UInt8 → Digest) {w : Nat}
    {ar₁ ar₂ : List (AlgId × List UInt8)} {tl₁ tl₂ : Timeline}
    (hw₁ : EqWidth w (combinedChildrenWith Hi ar₁ tl₁))
    (hw₂ : EqWidth w (combinedChildrenWith Hi ar₂ tl₂))
    (hlen : (combinedChildrenWith Hi ar₁ tl₁).length = (combinedChildrenWith Hi ar₂ tl₂).length)
    (h₁ : (combinedChildrenWith Hi ar₁ tl₁).length ≥ 2)
    (h₂ : (combinedChildrenWith Hi ar₂ tl₂).length ≥ 2)
    (heq : combinedRootWith Hi ar₁ tl₁ = combinedRootWith Hi ar₂ tl₂) :
    combinedChildrenWith Hi ar₁ tl₁ = combinedChildrenWith Hi ar₂ tl₂
      ∨ NodeHashCollisionFor Hi := by
  simp only [combinedRootWith, naryMrWith_multi Hi h₁, naryMrWith_multi Hi h₂,
    nodeHashWith] at heq
  by_cases hch : combinedChildrenWith Hi ar₁ tl₁ = combinedChildrenWith Hi ar₂ tl₂
  · exact Or.inl hch
  · right
    by_cases hflat :
        (combinedChildrenWith Hi ar₁ tl₁).flatten = (combinedChildrenWith Hi ar₂ tl₂).flatten
    · exact absurd (flatten_inj_of_eqWidth hw₁ hw₂ hlen hflat) hch
    · exact ⟨_, _, hflat, heq⟩

/-- **The singleton (promoted) binding root is the raw member root itself.** One
    member root under a trivial activation contributes exactly one fold child (no
    coverage child), so `naryMrWith` promotes — the binding root *is* that member
    root's **raw bytes**, with no hashing. Genesis promotion at the binding-root
    level (`pmt::combined_root`, `nary_mr` `len == 1`): a one-algorithm `BRᵢ`
    equals the raw member root, needing no node hash and hence no collision
    lever. -/
theorem combinedRootWith_singleton (Hi : List UInt8 → Digest)
    (e : AlgId × List UInt8) (tl : Timeline) (htriv : timelineTrivial tl = true) :
    combinedRootWith Hi [e] tl = memberDigestWith Hi e := by
  simp only [combinedRootWith, combinedChildrenWith, List.map_cons, List.map_nil,
    htriv, if_true, List.append_nil, naryMrWith]

/-- Inserts an element at a given position in a list. -/
def insertAt {α : Type} (n : Nat) (x : α) : List α → List α
  | [] => [x]
  | y :: ys =>
    match n with
    | 0 => x :: y :: ys
    | n + 1 => y :: insertAt n x ys

structure ProofStep where
  siblings : List Digest
  position : Nat
  deriving Inhabited

structure InclusionProof where
  index : Nat
  treeSize : Nat
  logArity : Nat
  path : List ProofStep
  deriving Inhabited

/-- Helper to safely get an element from a list, returning default if out of bounds. -/
def getL {α : Type} [Inhabited α] : List α → Nat → α
  | [], _ => default
  | x :: _, 0 => x
  | _ :: xs, n + 1 => getL xs n

/-- Reconstructs the root hash from a leaf and a proof path.

    This is the legacy transcription of the Rust verifier's fold. Under
    **canonical proof encoding** the `step.siblings.isEmpty` (promoted/zero-
    sibling) branch is dead: such steps are rejected, not passed through. The
    canonical model with its proved properties is `foldCanonical` /
    `CanonicalPath` in the "Canonical inclusion proofs" section below. -/
noncomputable def reconstructPathRoot (leafHash : Digest) (path : List ProofStep) : Digest :=
  path.foldl (fun current step =>
    if step.siblings.isEmpty then
      current
    else
      nodeHash (insertAt step.position current step.siblings)
  ) leafHash

/-- Reconstruct the coordinates (left_index, height) of the frontier for a given tree size. -/
partial def frontierForSize (n : Nat) (k : Nat) : List (Nat × Nat) :=
  if k < 2 then []
  else
    let rec loop (temp_n : Nat) (curr_left : Nat) (acc : List (Nat × Nat)) : List (Nat × Nat) :=
      if temp_n = 0 then acc.reverse
      else
        let rec find_height (cap : Nat) (height : Nat) : Nat × Nat :=
          let next_cap := cap * k
          if next_cap ≤ temp_n then
            find_height next_cap (height + 1)
          else
            (cap, height)
        let (cap, height) := find_height 1 0
        loop (temp_n - cap) (curr_left + cap) ((curr_left, height) :: acc)
    loop n 0 []

structure TreeBuildResult where
  childrenMap : List (Nat × List Nat)
  spans : List (Nat × (Nat × Nat))
  root : Nat
  deriving Inhabited

def lookupSpan (spans : List (Nat × (Nat × Nat))) (key : Nat) : Nat × Nat :=
  match spans with
  | [] => (0, 0)
  | (k, v) :: xs => if k = key then v else lookupSpan xs key

def lookupChildren (childrenMap : List (Nat × List Nat)) (key : Nat) : Option (List Nat) :=
  match childrenMap with
  | [] => none
  | (k, v) :: xs => if k = key then some v else lookupChildren xs key

partial def buildTree (k : Nat) (coords_len : Nat) : TreeBuildResult :=
  let initial_spans := List.range coords_len |>.map (fun i => (i, (i, i)))
  let initial_frontier := List.range coords_len
  let rec loop (frontier : List Nat) (next_id : Nat) (cmap : List (Nat × List Nat)) (spans : List (Nat × (Nat × Nat))) : TreeBuildResult :=
    if frontier.length > k then
      let split_idx := frontier.length - k
      let children := frontier.drop split_idx
      let parent_id := next_id
      let first_child := children.headD 0
      let last_child := children.getLastD 0
      let (min_val, _) := lookupSpan spans first_child
      let (_, max_val) := lookupSpan spans last_child
      let next_frontier := (frontier.take split_idx) ++ [parent_id]
      loop next_frontier (parent_id + 1) ((parent_id, children) :: cmap) ((parent_id, (min_val, max_val)) :: spans)
    else if frontier.length > 1 then
      let parent_id := next_id
      let first_child := frontier.headD 0
      let last_child := frontier.getLastD 0
      let (min_val, _) := lookupSpan spans first_child
      let (_, max_val) := lookupSpan spans last_child
      let cmap_final := (parent_id, frontier) :: cmap
      let spans_final := (parent_id, (min_val, max_val)) :: spans
      TreeBuildResult.mk cmap_final spans_final parent_id
    else
      TreeBuildResult.mk cmap spans (frontier.headD 0)
  loop initial_frontier coords_len [] initial_spans

partial def pathLengthToFrontierNode (k : Nat) (coords_len : Nat) (target_f_idx : Nat) : Option Nat :=
  if target_f_idx ≥ coords_len then none
  else
    let res : TreeBuildResult := buildTree k coords_len
    let rec trace (curr : Nat) (depth : Nat) : Option Nat :=
      match lookupChildren res.childrenMap curr with
      | none => some depth
      | some children =>
        let rec find_child (lst : List Nat) : Option Nat :=
          match lst with
          | [] => none
          | c :: cs =>
            let (min_val, max_val) := lookupSpan res.spans c
            if target_f_idx ≥ min_val ∧ target_f_idx ≤ max_val then
              trace c (depth + 1)
            else
              find_child cs
        find_child children
    trace res.root 0

partial def reconstructIndexFromPath (k : Nat) (treeSize : Nat) (path : List ProofStep) : Option Nat :=
  if k < 2 then none
  else
    let coords := frontierForSize treeSize k
    if coords.isEmpty then none
    else
      let res : TreeBuildResult := buildTree k coords.length
      let rec loop (curr : Nat) (path_idx : Nat) : Option (Nat × Nat) :=
        match lookupChildren res.childrenMap curr with
        | some children =>
          if path_idx = 0 then none
          else
            let step : ProofStep := getL path (path_idx - 1)
            if step.siblings.length ≠ children.length - 1 then none
            else if step.position ≥ children.length then none
            else
              let next_node := getL children step.position
              loop next_node (path_idx - 1)
        | none => some (curr, path_idx)
      
      match loop res.root path.length with
      | none => none
      | some (curr, path_idx) =>
        if curr ≥ coords.length then none
        else
          let (left, height) := getL coords curr
          if path_idx ≠ height then none
          else
            let rec loop_offset (i : Nat) (offset : Nat) (power : Nat) : Option Nat :=
              if i = path_idx then some (left + offset)
              else
                let step : ProofStep := getL path i
                if step.siblings.length ≠ k - 1 then none
                else if step.position ≥ k then none
                else
                  loop_offset (i + 1) (offset + step.position * power) (power * k)
            loop_offset 0 0 1

def verifyInclusionPathStructure (k : Nat) (index : Nat) (treeSize : Nat) (path : List ProofStep) : Bool :=
  match reconstructIndexFromPath k treeSize path with
  | some idx => idx = index
  | none => false

noncomputable def verifyInclusion (leafHash : Digest) (proof : InclusionProof) (root : Digest) : Bool :=
  let k := proof.logArity
  let T := proof.treeSize
  let S_I := proof.index
  let P := proof.path.length
  if k < 2 then false
  else
    let coords := frontierForSize T k
    let rec find_f_idx (lst : List (Nat × Nat)) (idx : Nat) : Option (Nat × Nat × Nat) :=
      match lst with
      | [] => none
      | (left, height) :: xs =>
        let cap := k ^ height
        if S_I ≥ left ∧ S_I < left + cap then
          some (idx, left, height)
        else
          find_f_idx xs (idx + 1)
    
    match find_f_idx coords 0 with
    | none => false
    | some (target_f_idx, _, height) =>
      match pathLengthToFrontierNode k coords.length target_f_idx with
      | none => false
      | some C =>
        let H := height
        if P < C + H then false
        else
          let d := P - C - H
          let log_path := proof.path.drop d
          if verifyInclusionPathStructure k S_I T log_path then
            let computed_root := reconstructPathRoot leafHash proof.path
            computed_root = root
          else
            false

/-! ## Canonical inclusion proofs — soundness and non-malleability

Under **canonical proof encoding**, zero-sibling ("promoted") steps are
*rejected*: honest provers omit them, because implicit promotion elevates a
digest to its parent slot without hashing, so a promoted step is a hash no-op.
Every step of an accepted proof therefore strictly hashes.

This is distinct from flat null promotion (`eval_flat_null_promotion`), a
null-*valued* collapse (N₀) that appears as null-*valued* siblings; here we
reject zero-*sibling* steps. The two mechanisms are independent.

The log skeleton pinned by `(k, index, tree_size)` is the security boundary
(exact length, per-step position, per-level sibling count). Its concrete
computation is the shared topology module (`neml/src/topology.rs`); the theorems
below take it as an abstract predicate `SkeletonValid`, so they hold for whatever
pinning that module enforces. -/

/-- A step strictly hashes iff it carries at least one sibling. -/
def StrictStep (s : ProofStep) : Prop := s.siblings ≠ []

/-- A canonical path contains no zero-sibling (promoted) steps. -/
def CanonicalPath (path : List ProofStep) : Prop := ∀ s ∈ path, StrictStep s

/-- One strictly-hashing fold step: hash the path node into its slot among the
    siblings. Under `CanonicalPath` this is the only behavior that occurs (the
    `reconstructPathRoot` pass-through branch is dead). -/
noncomputable def applyStep (cur : Digest) (s : ProofStep) : Digest :=
  nodeHash (insertAt s.position cur s.siblings)

/-- Reconstruct the root by strictly hashing along a canonical path. -/
noncomputable def foldCanonical (leaf : Digest) (path : List ProofStep) : Digest :=
  path.foldl applyStep leaf

/-- **Canonical encoding rejects promoted steps.** Any path containing a
    zero-sibling step is non-canonical, hence rejected. This closes the
    prepend-a-promoted-step malleability: padded proofs are no longer accepted. -/
theorem not_canonical_of_promoted (path : List ProofStep)
    (h : ∃ s ∈ path, s.siblings = []) : ¬ CanonicalPath path := by
  obtain ⟨s, hmem, hs⟩ := h
  intro hcanon
  exact (hcanon s hmem) hs

/-- The canonical inclusion verifier's accept relation. Trusted parameters
    `(k, index, tree_size)` come from a signed tree head. The path splits at
    `boundary`: the leading steps are the subtree prefix (hashing `leaf` up to
    its log-position subtree root) and the trailing steps are the log skeleton,
    pinned to log position `index` by `SkeletonValid`. The whole path is
    canonical and strictly hashes `leaf` to `root`. -/
def Accepts (SkeletonValid : Nat → Nat → Nat → List ProofStep → Prop)
    (k index treeSize : Nat) (leaf root : Digest) (path : List ProofStep) : Prop :=
  CanonicalPath path ∧
  foldCanonical leaf path = root ∧
  ∃ boundary, boundary ≤ path.length ∧ SkeletonValid k index treeSize (path.drop boundary)

/-- **Inclusion soundness (existential).** An accepting canonical proof for
    `(leaf, index, tree_size, root)` exhibits a subtree root `R` at log position
    `index` such that `leaf` hashes up to `R` at some depth `d`, and `R` folds
    through the pinned log skeleton to `root`. Depth is existential: implicit
    promotion makes a promoted digest equal its parent slot, so the claim binds
    the log *position*, never the depth (Cyphr SPEC §2.2.12). -/
theorem inclusion_soundness
    (SkeletonValid : Nat → Nat → Nat → List ProofStep → Prop)
    (k index treeSize : Nat) (leaf root : Digest) (path : List ProofStep)
    (h : Accepts SkeletonValid k index treeSize leaf root path) :
    ∃ (R : Digest) (d : Nat), d ≤ path.length ∧
      foldCanonical leaf (path.take d) = R ∧
      SkeletonValid k index treeSize (path.drop d) ∧
      foldCanonical R (path.drop d) = root := by
  obtain ⟨_hcanon, hfolds, boundary, hble, hskel⟩ := h
  refine ⟨foldCanonical leaf (path.take boundary), boundary, hble, rfl, hskel, ?_⟩
  have hsplit : foldCanonical leaf (path.take boundary ++ path.drop boundary) = root := by
    rw [List.take_append_drop]; exact hfolds
  rw [foldCanonical, List.foldl_append] at hsplit
  exact hsplit

/-! Helper lemmas for `inclusion_proof_unique`: injectivity of `insertAt`,
    back-decomposition of lists, indexing across appends, and the
    fold-append step. -/

theorem insertAt_ne_nil {α : Type} (n : Nat) (x : α) (xs : List α) :
    insertAt n x xs ≠ [] := by
  induction xs generalizing n with
  | nil =>
    simp [insertAt]
  | cons y ys ih =>
    cases n with
    | zero =>
      simp [insertAt]
    | succ m =>
      simp [insertAt]

theorem insertAt_injective {α : Type} (n : Nat) (x y : α) (xs ys : List α)
    (h : insertAt n x xs = insertAt n y ys) : x = y ∧ xs = ys := by
  induction n generalizing xs ys with
  | zero =>
    have hxs : insertAt 0 x xs = x :: xs := by
      cases xs <;> rfl
    have hys : insertAt 0 y ys = y :: ys := by
      cases ys <;> rfl
    rw [hxs, hys] at h
    injection h with hxy hxsys
    exact ⟨hxy, hxsys⟩
  | succ m ih =>
    cases xs with
    | nil =>
      have hx : insertAt (m + 1) x [] = [x] := rfl
      rw [hx] at h
      cases ys with
      | nil =>
        have hy : insertAt (m + 1) y [] = [y] := rfl
        rw [hy] at h
        injection h with hxy
        exact ⟨hxy, rfl⟩
      | cons z zs =>
        have hy : insertAt (m + 1) y (z :: zs) = z :: insertAt m y zs := rfl
        rw [hy] at h
        injection h with _ h2
        have hne := insertAt_ne_nil m y zs
        rw [← h2] at hne
        contradiction
    | cons z zs =>
      have hx : insertAt (m + 1) x (z :: zs) = z :: insertAt m x zs := rfl
      rw [hx] at h
      cases ys with
      | nil =>
        have hy : insertAt (m + 1) y [] = [y] := rfl
        rw [hy] at h
        injection h with _ h2
        have hne := insertAt_ne_nil m x zs
        rw [h2] at hne
        contradiction
      | cons w ws =>
        have hy : insertAt (m + 1) y (w :: ws) = w :: insertAt m y ws := rfl
        rw [hy] at h
        injection h with hzw h2
        have ih_res := ih zs ws h2
        obtain ⟨hxy, hzs⟩ := ih_res
        rw [hzw, hzs]
        exact ⟨hxy, rfl⟩

theorem list_decomp_last {α : Type} {m : Nat} (l : List α) (h : l.length = m + 1) :
    ∃ l' x, l = l' ++ [x] ∧ l'.length = m := by
  induction l generalizing m with
  | nil =>
    contradiction
  | cons y ys ih =>
    cases m with
    | zero =>
      cases ys with
      | nil =>
        refine ⟨[], y, rfl, rfl⟩
      | cons z zs =>
        simp only [List.length_cons] at h
        omega
    | succ k =>
      have hlen : ys.length = k + 1 := by
        simp only [List.length_cons] at h
        omega
      obtain ⟨ys', x, hys_eq, hys'_len⟩ := ih hlen
      rw [hys_eq]
      refine ⟨y :: ys', x, rfl, ?_⟩
      simp [hys'_len]

theorem get?_append_left {α : Type} (xs : List α) (ys : List α) (i : Nat) (h : i < xs.length) :
    (xs ++ ys)[i]? = xs[i]? := by
  induction xs generalizing i with
  | nil =>
    contradiction
  | cons z zs ih =>
    cases i with
    | zero =>
      rfl
    | succ j =>
      have h2 : j < zs.length := by
        simp only [List.length_cons] at h
        omega
      exact ih j h2

theorem get?_append_last {α : Type} (xs : List α) (x : α) :
    (xs ++ [x])[xs.length]? = some x := by
  induction xs with
  | nil =>
    rfl
  | cons z zs ih =>
    exact ih

theorem foldCanonical_append_last (leaf : Digest) (p' : List ProofStep) (s : ProofStep) :
    foldCanonical leaf (p' ++ [s]) = applyStep (foldCanonical leaf p') s := by
  simp [foldCanonical]

theorem foldCanonical_unique_of_len (n : Nat) (leaf : Digest) (p₁ p₂ : List ProofStep)
    (hlen1 : p₁.length = n)
    (hlen2 : p₂.length = n)
    (hpos : ∀ i < n, (p₁[i]?).map ProofStep.position = (p₂[i]?).map ProofStep.position)
    (heq : foldCanonical leaf p₁ = foldCanonical leaf p₂)
    (hcol : ¬ NodeHashCollision) :
    p₁ = p₂ := by
  induction n generalizing leaf p₁ p₂ with
  | zero =>
    have hp1 : p₁ = [] := by
      cases p₁ with
      | nil => rfl
      | cons x xs =>
        simp only [List.length_cons] at hlen1
        omega
    have hp2 : p₂ = [] := by
      cases p₂ with
      | nil => rfl
      | cons x xs =>
        simp only [List.length_cons] at hlen2
        omega
    rw [hp1, hp2]
  | succ m ih =>
    obtain ⟨p₁', s₁, hp1_eq, hp1'_len⟩ := list_decomp_last p₁ hlen1
    obtain ⟨p₂', s₂, hp2_eq, hp2'_len⟩ := list_decomp_last p₂ hlen2
    rw [hp1_eq, hp2_eq] at heq
    rw [foldCanonical_append_last, foldCanonical_append_last] at heq
    simp only [applyStep] at heq
    have h_node_eq : insertAt s₁.position (foldCanonical leaf p₁') s₁.siblings = insertAt s₂.position (foldCanonical leaf p₂') s₂.siblings := by
      by_contra hc
      apply hcol
      refine ⟨insertAt s₁.position (foldCanonical leaf p₁') s₁.siblings, insertAt s₂.position (foldCanonical leaf p₂') s₂.siblings, hc, heq⟩
    have hpos_last : (p₁[m]?).map ProofStep.position = (p₂[m]?).map ProofStep.position := by
      apply hpos
      omega
    rw [hp1_eq, hp2_eq] at hpos_last
    have hp1_last_eq : (p₁' ++ [s₁])[p₁'.length]? = some s₁ := get?_append_last p₁' s₁
    have hp2_last_eq : (p₂' ++ [s₂])[p₂'.length]? = some s₂ := get?_append_last p₂' s₂
    rw [hp1'_len] at hp1_last_eq
    rw [hp2'_len] at hp2_last_eq
    rw [hp1_last_eq, hp2_last_eq] at hpos_last
    simp only [Option.map, Option.some.injEq] at hpos_last
    rw [hpos_last] at h_node_eq
    have h_inj := insertAt_injective s₂.position (foldCanonical leaf p₁') (foldCanonical leaf p₂') s₁.siblings s₂.siblings h_node_eq
    obtain ⟨h_fold_eq, h_sib_eq⟩ := h_inj
    have h_step_eq : s₁ = s₂ := by
      cases s₁
      cases s₂
      simp only [ProofStep.mk.injEq] at *
      exact ⟨h_sib_eq, hpos_last⟩
    have hpos' : ∀ i < m, (p₁'[i]?).map ProofStep.position = (p₂'[i]?).map ProofStep.position := by
      intro i hi
      have hpos_i := hpos i (by omega)
      rw [hp1_eq, hp2_eq] at hpos_i
      have h_i_len1 : i < p₁'.length := by omega
      have h_i_len2 : i < p₂'.length := by omega
      have hp1'_i : (p₁' ++ [s₁])[i]? = p₁'[i]? := get?_append_left p₁' [s₁] i h_i_len1
      have hp2'_i : (p₂' ++ [s₂])[i]? = p₂'[i]? := get?_append_left p₂' [s₂] i h_i_len2
      rw [hp1'_i, hp2'_i] at hpos_i
      exact hpos_i
    have hp_eq : p₁' = p₂' := ih leaf p₁' p₂' hp1'_len hp2'_len hpos' h_fold_eq
    rw [hp1_eq, hp2_eq, hp_eq, h_step_eq]

/-- **Inclusion proof-encoding uniqueness (non-malleability).** With zero-sibling
    steps rejected, every remaining step strictly hashes, and the shared topology
    module pins the proof *shape* from `(k, index, tree_size)`: the accepted
    path's length and its per-step position are determined (hypotheses `hlen`,
    `hpos` — what `topology.rs` guarantees, modeled as premises until that module
    is ported to Lean). The only remaining freedom is the sibling *values*, which
    the fold pins to `root`. Hence for a fixed `(leaf, index, tree_size, root)`
    there is at most one accepting canonical path — modulo a `nodeHash` collision
    (where the path could be rerouted by colliding an internal node hash).

    Without `hlen`/`hpos` the claim is false (two paths of different lengths can
    both fold to a fixed point, and a fixed `position` is what makes the
    per-step `insertAt` recoverable); they encode the injective child-ordering
    the canonical-encoding decision relies on.

    Proved by back-to-front induction (`foldCanonical_unique_of_len`): each final
    `nodeHash` is equal, so its preimages either collide or, with `position`
    pinned, `insertAt` injectivity forces the steps and the running digests
    equal, recursing on the prefixes. -/
theorem inclusion_proof_unique
    (SkeletonValid : Nat → Nat → Nat → List ProofStep → Prop)
    (k index treeSize : Nat) (leaf root : Digest) (p₁ p₂ : List ProofStep)
    (h₁ : Accepts SkeletonValid k index treeSize leaf root p₁)
    (h₂ : Accepts SkeletonValid k index treeSize leaf root p₂)
    (hlen : p₁.length = p₂.length)
    (hpos : ∀ i : Nat, (p₁[i]?).map ProofStep.position = (p₂[i]?).map ProofStep.position) :
    p₁ = p₂ ∨ NodeHashCollision := by
  by_cases hcol : NodeHashCollision
  · exact Or.inr hcol
  · have hf₁ := h₁.2.1
    have hf₂ := h₂.2.1
    have hpos_lim : ∀ i < p₁.length, (p₁[i]?).map ProofStep.position = (p₂[i]?).map ProofStep.position := by
      intro i _
      exact hpos i
    have heq : p₁ = p₂ := foldCanonical_unique_of_len p₁.length leaf p₁ p₂ rfl hlen.symm hpos_lim (hf₁.trans hf₂.symm) hcol
    exact Or.inl heq

end NEML

/-!
## Trust base (axiom inventory)

After this realignment the NEML/Projection layer declares **exactly four** axioms,
all legitimate typing/hashing scaffolding, in `Projection.lean`:
`Digest`, `Digest.nonempty`, `H`, `digestToBytes`.

This corrects the earlier count of thirteen. Removed: `numsSeed`, `xof`, the
`eval` axiom and its five `eval_*` equation axioms (now a real `def` with proved
equations), and `domain_separation` (the deleted vacuous EML theorems were its
only consumer). `#print axioms` on the NEML/Projection theorems shows only the
four above plus the Lean built-ins `propext`, `Classical.choice`, `Quot.sound`.

Every theorem in this file is now fully proved and sorry-free.
-/
