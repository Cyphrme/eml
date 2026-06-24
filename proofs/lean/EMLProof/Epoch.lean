import EMLProof.Foundations
import EMLProof.NEML
import Mathlib.Tactic
import Mathlib.Logic.Encodable.Basic
import Mathlib.Logic.Equiv.List

/-!
# Epoch combinator — committed activity, the combined root, and coupling soundness

The **epoch combinator** layer of the proof corpus. Where `EMLProof.NEML` holds
the structural Merkle Spine (the canonicalizing evaluator, the eval equations, and
the canonical inclusion proofs), this module holds everything the combinator adds
*on top* of that spine: the committed activation timeline (Design A+), the
**combined root** as the raw-concat canonicalization fold over the per-algorithm
member roots, the per-algorithm **binding root** (no security mixing, D9), and the
coupling-verifier soundness theorem.

The dependency arrow runs **epoch → spine only**: every definition here consumes
the spine's roots as **opaque digest bytes** and never touches `eval` /
`canonical_unique`. The spine modules import nothing from here. This is the second
half of the central uniqueness guarantee:

* **structural injectivity** — distinct canonical structures ⇒ distinct roots —
  is the spine's `canonical_unique` (`EMLProof.Canonical`), and stands alone for a
  single-algorithm consumer with no notion of an epoch;
* **timeline binding** — distinct committed activations ⇒ distinct binding roots —
  is `combinedRoot_binds_timeline` here, the epoch-layer half.

The two are distinct-but-composing guarantees, kept physically separate (the
structural half carries no epoch hypothesis; this half consumes only opaque
digests). The null-run-extents (the one logical count) are committed only here:
general collapse is structural and folds into the spine's canonical form, and only
the per-tree-divergent null subset is committed at the combinator.

Everything below is reused verbatim from the pre-split corpus; the symbols stay in
`namespace NEML`, so their fully-qualified names (`NEML.combinedRoot`,
`NEML.combinedRootWith`, …) are unchanged for every downstream consumer.
-/

namespace NEML

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


end NEML
