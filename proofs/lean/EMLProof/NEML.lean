import EMLProof.Projection
import Mathlib.Logic.Encodable.Basic

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
  /-- Recursive evaluation of an N-ary tree under NEML promotion rules.
      `L` is the digest length of the active hash algorithm (vestigial; see
      `nullDigest`). Arms: leaf hashing; empty node → `emptyHash`; singleton
      promotion; flat null promotion (all children null, arity ≥ 2); standard
      node hashing. -/
  noncomputable def eval (L : Nat) : NaryTree (List UInt8) → Digest
    | NaryTree.leaf data => leafHash data
    | NaryTree.node [] => emptyHash
    | NaryTree.node [c] => eval L c
    | NaryTree.node children =>
        if evalAllNull L children then nullDigest L
        else nodeHash (evalMap L children)
  termination_by t => nsize t
  decreasing_by
    all_goals simp [nsize, nlsize]
    all_goals omega

  /-- Whether every child of a node evaluates to the null digest. -/
  noncomputable def evalAllNull (L : Nat) : List (NaryTree (List UInt8)) → Bool
    | [] => true
    | c :: cs => (eval L c == nullDigest L) && evalAllNull L cs
  termination_by cs => nlsize cs
  decreasing_by
    all_goals simp [nlsize]
    all_goals omega

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

/-- Flat null promotion equation, arity ≥ 2 (was `axiom eval_flat_null_node`). -/
theorem eval_flat_null_node (L : Nat) (children : List (NaryTree (List UInt8)))
    (h_length : children.length ≥ 2)
    (h_all_null : ∀ t ∈ children, eval L t = nullDigest L) :
    eval L (NaryTree.node children) = nullDigest L := by
  obtain ⟨a, b, rest, rfl⟩ : ∃ a b rest, children = a :: b :: rest := by
    match children, h_length with
    | a :: b :: rest, _ => exact ⟨a, b, rest, rfl⟩
  have hAll : evalAllNull L (a :: b :: rest) = true :=
    (evalAllNull_eq_true_iff L _).mpr h_all_null
  simp only [eval]
  rw [if_pos hAll]

/-- Standard node hashing equation, arity ≥ 2 with a non-null child
    (was `axiom eval_node_hash`). -/
theorem eval_node_hash (L : Nat) (children : List (NaryTree (List UInt8)))
    (h_length : children.length ≥ 2)
    (h_some : ∃ t ∈ children, eval L t ≠ nullDigest L) :
    eval L (NaryTree.node children) = nodeHash (children.map (eval L)) := by
  obtain ⟨a, b, rest, rfl⟩ : ∃ a b rest, children = a :: b :: rest := by
    match children, h_length with
    | a :: b :: rest, _ => exact ⟨a, b, rest, rfl⟩
  have hNot : ¬ evalAllNull L (a :: b :: rest) = true := by
    rw [evalAllNull_eq_true_iff]
    intro hall
    obtain ⟨t, ht, htne⟩ := h_some
    exact htne (hall t ht)
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

/-! ## Design A+ — the committed epoch timeline authenticates activity

This section formalizes the Design A+ soundness content. The combined root is a
structural **metaroot**: a tree layer whose preimage commits every algorithm's
root **and** the per-algorithm epoch timeline (the timeline is structure — it
decides which cells are null projections). Two consequences are modeled:

* **Activity is read from the authenticated timeline, never from digest
  null-ness.** This is what renders the `leaf(b"null") = N₀` collision
  (`null_collision`) inert: the inference "cell = N₀ ⇒ inactive" is unsound
  (`inferredActiveFromNull_unsound`), so activity must come from the committed
  field.
* **The metaroot binds the timeline** (`metaroot_binds_timeline`): the two
  histories the collision would conflate — byte-identical trees but timelines
  disagreeing on activity at some `(X, p)` — cannot share a combined root unless
  `H` collides. Inactivity is therefore not forgeable by metadata substitution.

Plus the verification-time consistency check `inactive ⇒ N₀`
(`InactiveImpliesNull`) and its anti-repudiation consequence
(`real_cell_forces_committed_active`).

Mirrors `neml/src/proof.rs` (`committed_active_at`, `combined_root_preimage`,
`validate_committed_epochs`) and `neml/src/tree.rs` (`combined_root_at`,
`verify_audit_payload`). The metaroot is never signature-dependent; signing is an
orthogonal, snapshot-level act performed after a snapshot's leaves are verified. -/

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
    leading mark run) and the suffix `s`. This is the parsing primitive that
    makes the length-prefixed root encoding (`encRoots`) injective and
    prefix-free. -/
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

/-- Injective byte serialization of the committed timeline. The combined-root
    preimage commits this (`combined_root_preimage` in `proof.rs` uses a concrete
    fixed-width big-endian framing; here we use any injective serialization, of
    which that format is one realization). Built as `uNat ∘ encode`, so
    injectivity is immediate. -/
def encTimeline (tl : Timeline) : List UInt8 := uNat (Encodable.encode tl)

theorem encTimeline_injective : Function.Injective encTimeline :=
  uNat_injective.comp Encodable.encode_injective

/-! ## Active-root encoding

The active roots ride the wire as raw bytes (`active_roots : Vec<(u64, Vec<u8>)>`
in `proof.rs`), and `combined_root_preimage` frames each entry length-prefixed:
`id ‖ |root| ‖ root`. We model the root as `List UInt8` — exactly the Rust
`Vec<u8>` — rather than an opaque `Digest`, so the encoding is a concrete
byte function with no reliance on `digestToBytes` (an axiom with no injectivity).
The per-entry length prefix is what makes the encoding parse-unambiguous, hence
injective and prefix-free, which the coupling-verifier soundness theorem needs
(the roots vary between the presented and the genuinely committed proof). -/

/-- One active-root entry, length-prefixed so the encoding self-delimits:
    `id ‖ |root| ‖ root`. Mirrors the `id ‖ r.len() ‖ r` block emitted per entry
    by `combined_root_preimage` (`proof.rs`). -/
def encRootEntry (p : AlgId × List UInt8) : List UInt8 :=
  uNat p.1 ++ uNat p.2.length ++ p.2

/-- A single entry self-delimits: its byte image determines both the entry and
    whatever follows it. -/
theorem encRootEntry_prefixFree {p q : AlgId × List UInt8} {s t : List UInt8}
    (h : encRootEntry p ++ s = encRootEntry q ++ t) : p = q ∧ s = t := by
  simp only [encRootEntry, List.append_assoc] at h
  obtain ⟨hid, h2⟩ := uNat_append_injective h
  obtain ⟨hlen, h3⟩ := uNat_append_injective h2
  obtain ⟨hsnd, hst⟩ := List.append_inj h3 hlen
  refine ⟨?_, hst⟩
  cases p; cases q
  simp_all

/-- Byte serialization of the active per-algorithm roots: a length prefix
    followed by one self-delimiting entry per algorithm. Mirrors the
    `n_active ‖ [id ‖ len ‖ root]*` head of `combined_root_preimage`. -/
def encRoots (ar : List (AlgId × List UInt8)) : List UInt8 :=
  uNat ar.length ++ ar.flatMap encRootEntry

/-- The entry list self-delimits once the count is known: equal-length entry
    lists with equal flattened byte images (sharing a common suffix split) are
    equal, and the suffixes coincide. -/
theorem encRoots_entries_prefixFree :
    ∀ {a b : List (AlgId × List UInt8)} {s t : List UInt8},
      a.length = b.length →
      a.flatMap encRootEntry ++ s = b.flatMap encRootEntry ++ t → a = b ∧ s = t := by
  intro a
  induction a with
  | nil =>
    intro b s t hlen h
    cases b with
    | nil => simpa using h
    | cons q qs => simp at hlen
  | cons p ps ih =>
    intro b s t hlen h
    cases b with
    | nil => simp at hlen
    | cons q qs =>
      simp only [List.flatMap_cons, List.append_assoc] at h
      obtain ⟨hpq, hrest⟩ := encRootEntry_prefixFree h
      have hlen' : ps.length = qs.length := by simpa using hlen
      obtain ⟨hps, hst⟩ := ih hlen' hrest
      exact ⟨by rw [hpq, hps], hst⟩

/-- **`encRoots` is prefix-free.** The leading count fixes the entry total and
    each entry self-delimits, so `encRoots ar ++ s` recovers both `ar` and `s`.
    This is the parse-unambiguity the binding argument relies on when the active
    roots are not held fixed. -/
theorem encRoots_prefixFree {a b : List (AlgId × List UInt8)} {s t : List UInt8}
    (h : encRoots a ++ s = encRoots b ++ t) : a = b ∧ s = t := by
  simp only [encRoots, List.append_assoc] at h
  obtain ⟨hlen, hrest⟩ := uNat_append_injective h
  exact encRoots_entries_prefixFree hlen hrest

/-- **`encRoots` is injective** (the prefix-free property at empty suffix). -/
theorem encRoots_injective : Function.Injective encRoots := by
  intro a b h
  have h' : encRoots a ++ [] = encRoots b ++ [] := by simp [h]
  exact (encRoots_prefixFree h').1

/-- The combined-root metaroot preimage: active roots followed by the committed
    timeline. -/
def metaPreimage (ar : List (AlgId × List UInt8)) (tl : Timeline) : List UInt8 :=
  encRoots ar ++ encTimeline tl

/-- The combined root (metaroot) is `H` of its preimage. -/
noncomputable def combinedRoot (ar : List (AlgId × List UInt8)) (tl : Timeline) : Digest :=
  H (metaPreimage ar tl)

/-- **The metaroot preimage is injective in both fields.** Because `encRoots` is
    prefix-free, the roots/timeline boundary is recoverable: equal preimages
    force equal active roots *and* equal committed timelines. (`encTimeline`'s
    injectivity closes the timeline half.) This is the structural fact behind
    coupling-verifier soundness — a fixed combined root pins both committed
    fields modulo a hash collision. -/
theorem metaPreimage_injective {ar₁ ar₂ : List (AlgId × List UInt8)} {tl₁ tl₂ : Timeline}
    (h : metaPreimage ar₁ tl₁ = metaPreimage ar₂ tl₂) : ar₁ = ar₂ ∧ tl₁ = tl₂ := by
  simp only [metaPreimage] at h
  obtain ⟨har, htl⟩ := encRoots_prefixFree h
  exact ⟨har, encTimeline_injective htl⟩

/-- **A+ non-equivocation: the metaroot binds the committed timeline.** The two
    histories the leaf/null collision would otherwise conflate — byte-identical
    trees (hence identical active roots `ar`) but timelines disagreeing on
    activity at some `(X, p)` — cannot share a combined root unless `H` collides.
    Binding the timeline into the metaroot is exactly what makes inactivity
    non-forgeable by metadata substitution under a fixed root. -/
theorem metaroot_binds_timeline
    (ar : List (AlgId × List UInt8)) (tl₁ tl₂ : Timeline)
    (hne : tl₁ ≠ tl₂) (heq : combinedRoot ar tl₁ = combinedRoot ar tl₂) :
    HashCollision := by
  refine ⟨metaPreimage ar tl₁, metaPreimage ar tl₂, ?_, heq⟩
  intro hpre
  apply hne
  apply encTimeline_injective
  simp only [metaPreimage] at hpre
  exact List.append_cancel_left hpre

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

/-- A collision on the internal node hash: distinct child lists, equal digest.
    A `nodeHash` collision is in particular an `H` collision. -/
def NodeHashCollision : Prop := ∃ a b : List Digest, a ≠ b ∧ nodeHash a = nodeHash b

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
