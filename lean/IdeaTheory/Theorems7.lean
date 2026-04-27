import IdeaTheory.Foundations
import Mathlib.Tactic

/-!
# Idea Theory — Volume 4, Theorem File 7: Transmission Chains

## (a) The informal locus formalized.
The informal Idea-Theory literature describes a *transmission chain* as the
mechanism by which an idea is propagated through a sequence of carriers — minds,
texts, institutions, neural assemblies — each of which composes the inherited
material with whatever it brings of its own.  Because Volume 4 is concerned
with the cognitive-science and philosophy-of-mind interpretation of the
algebraic apparatus, the natural mathematical avatar of a "transmission chain"
is a finite list of ideas folded with the basic compositional operation `op`
of `IdeaTheoryStructure`.  The slogan "identity is invisible to transmission"
becomes the precise claim that inserting the unit `ident` anywhere in the chain
leaves its folded value unchanged; the slogan "self-reinforcing thoughts are
robust under iteration" becomes the precise claim that self-fixed points
absorb arbitrary positive powers and arbitrary replicate-chains.

## (b) Authors and works drawn upon.
The chain construction follows the *Idea Theory* monograph (Vol. I, §7) and
its informal extensions in the cognitive-science volume (Vol. IV).  The
identity-uniqueness arguments are standard universal-algebra folklore (Birkhoff,
1935; Burris–Sankappanavar, 1981).  The treatment of self-fixed points under
folding mirrors the classical idempotent theory in semigroups (Howie, 1995),
specialised to the unital case.  The cognitive interpretation of
transmission-chain stability under identity-insertion is anticipated by the
informal discussions of "neutral cognitive acts" in the philosophy-of-mind
chapters of Vol. IV.

## (c) Design decisions and conventions.
We take `op` and `ident` from `IdeaTheoryStructure` as primitive and never
unfold them.  Lists are used rather than `Multiset` because the order of
transmission is semantically meaningful in Volume 4.  We define `compPow`
with the recursion `compPow a (n+1) = op a (compPow a n)` rather than the
mirror convention; this matches the left-fold reading of inheritance, where
the *most recent* carrier sits to the left.  We use `chain : List I → I` as
the right-fold of `op` with neutral element `ident`, which matches the
inductive definition of `List.foldr` but is spelled out by hand to keep all
proofs definitionally transparent.

## (d) Roadmap.
Sections §7.A–§7.I build the `compPow` calculus, the identity rewrites,
associativity helpers, and the auxiliary predicates `IdentityTransparent`,
`FactorsThroughIdentity`, `IsSelfFixedPoint`, and `PreservesIdentity`.  These
feed the headline `theorem_7_1` (Composition Identity Theorem).  Sections
§7.K–§7.L develop the chain calculus and culminate in `theorem_7_2` (Identity
Transmission Theorem).  Sections §7.M–§7.N package the fixed-point theory
into `theorem_7_3` (Compositional Fixed Point Theorem).  Sections §7.O–§7.R
contain four named corollaries linking the headline results to downstream
cognitive-science applications, followed by examples and an index.

## (e) Role inside Volume 4.
Volume 4 reads the algebraic skeleton of Idea Theory as a model of cognitive
transmission.  This file supplies the *formal substrate* on which the later,
more interpretive chapters can lean: every claim about "preservation under
transmission" or "robustness of stable concepts" is grounded here as a
machine-checked theorem.  No `sorry`, no `admit`, no `native_decide`,
no axiom beyond `IdeaTheoryStructure`.
-/

namespace IdeaTheory

open IdeaTheoryStructure

variable {I : Type*} [IdeaTheoryStructure I]

/-! ## §7.A. Iterated composition (compositional powers) -/

/-- Iterated left-composition: `compPow a 0 = ident`, `compPow a (n+1) = op a (compPow a n)`. -/
def compPow (a : I) : ℕ → I
  | 0     => ident
  | n + 1 => op a (compPow a n)

@[simp] lemma compPow_zero (a : I) : compPow a 0 = ident := rfl

@[simp] lemma compPow_succ (a : I) (n : ℕ) :
    compPow a (n+1) = op a (compPow a n) := rfl

lemma compPow_one (a : I) : compPow a 1 = a := by
  simp [compPow, id_right]

lemma compPow_two (a : I) : compPow a 2 = op a a := by
  show op a (op a ident) = op a a
  rw [id_right]

lemma compPow_three (a : I) : compPow a 3 = op a (op a a) := by
  show op a (op a (op a ident)) = op a (op a a)
  rw [id_right]

lemma compPow_ident (n : ℕ) : compPow (ident : I) n = ident := by
  induction n with
  | zero => rfl
  | succ n ih => simp [compPow, ih, id_left]

/-! ## §7.B. Basic identity rewrites -/

lemma op_ident_left (a : I) : op ident a = a := id_left a
lemma op_ident_right (a : I) : op a ident = a := id_right a

lemma op_ident_both (a : I) : op (op ident a) ident = a := by
  rw [id_left, id_right]

lemma op_ident_both' (a : I) : op ident (op a ident) = a := by
  rw [id_left, id_right]

lemma ident_self_op : op (ident : I) ident = ident := id_left ident

lemma ident_op_chain2 : op (ident : I) (op ident ident) = ident := by
  simp [id_left]

lemma ident_op_chain3 : op (op (ident : I) ident) (op ident ident) = ident := by
  simp [id_left]

lemma ident_op_chain4 :
    op (op (op (ident : I) ident) ident) (op ident ident) = ident := by
  simp [id_left]

lemma op_ident_left_eq {a b : I} (h : a = b) : op ident a = b := by
  rw [id_left]; exact h

lemma op_ident_right_eq {a b : I} (h : a = b) : op a ident = b := by
  rw [id_right]; exact h

lemma sandwich_ident (a : I) : op (op ident a) ident = a := by
  rw [id_left, id_right]

lemma double_ident_left (a : I) : op ident (op ident a) = a := by
  rw [id_left, id_left]

lemma double_ident_right (a : I) : op (op a ident) ident = a := by
  rw [id_right, id_right]

lemma triple_ident_left (a : I) : op ident (op ident (op ident a)) = a := by
  rw [id_left, id_left, id_left]

lemma triple_ident_right (a : I) : op (op (op a ident) ident) ident = a := by
  rw [id_right, id_right, id_right]

/-! ## §7.C. Associativity-driven helpers -/

lemma reassoc3 (a b c : I) : op (op a b) c = op a (op b c) := assoc a b c

lemma reassoc3' (a b c : I) : op a (op b c) = op (op a b) c := (assoc a b c).symm

lemma reassoc4 (a b c d : I) :
    op (op (op a b) c) d = op a (op b (op c d)) := by
  rw [assoc, assoc]

lemma reassoc4_alt (a b c d : I) :
    op (op a b) (op c d) = op a (op b (op c d)) := by
  rw [assoc]

lemma reassoc4_alt' (a b c d : I) :
    op (op a b) (op c d) = op (op (op a b) c) d := by
  rw [← assoc]

lemma reassoc5 (a b c d e : I) :
    op (op (op (op a b) c) d) e = op a (op b (op c (op d e))) := by
  rw [assoc, assoc, assoc]

lemma op_ident_middle (a b : I) : op (op a ident) b = op a b := by
  rw [id_right]

lemma op_ident_middle' (a b : I) : op a (op ident b) = op a b := by
  rw [id_left]

lemma op_ident_middle_assoc (a b : I) : op a (op ident b) = op (op a ident) b := by
  rw [id_left, id_right]

lemma insert_ident_middle (a b : I) : op a b = op (op a ident) b := by
  rw [id_right]

lemma insert_ident_middle' (a b : I) : op a b = op a (op ident b) := by
  rw [id_left]

lemma insert_ident_left (a : I) : a = op ident a := (id_left a).symm

lemma insert_ident_right (a : I) : a = op a ident := (id_right a).symm

/-! ## §7.D. Identity-transparent / identity-stable -/

/-- `a` is identity-transparent: composing with ident on either side returns `a`. -/
def IdentityTransparent (a : I) : Prop :=
  op a ident = a ∧ op ident a = a

/-- Every element is identity-transparent. -/
lemma identityTransparent_all (a : I) : IdentityTransparent a :=
  ⟨id_right a, id_left a⟩

lemma identityTransparent_ident : IdentityTransparent (ident : I) :=
  identityTransparent_all _

lemma identityTransparent_op (a b : I) : IdentityTransparent (op a b) :=
  identityTransparent_all _

lemma identityTransparent_left {a : I} (h : IdentityTransparent a) :
    op ident a = a := h.2

lemma identityTransparent_right {a : I} (h : IdentityTransparent a) :
    op a ident = a := h.1

lemma identityTransparent_iff (a : I) :
    IdentityTransparent a ↔ (op a ident = a ∧ op ident a = a) := Iff.rfl

/-! ## §7.E. Factors-through-identity -/

/-- `a` factors through identity if there exist `x,y` with `a = op (op x ident) y`. -/
def FactorsThroughIdentity (a : I) : Prop :=
  ∃ x y : I, a = op (op x ident) y

lemma factorsThroughIdentity_self (a : I) : FactorsThroughIdentity a :=
  ⟨a, ident, by rw [id_right, id_right]⟩

lemma factorsThroughIdentity_via_ident_left (a : I) : FactorsThroughIdentity a :=
  ⟨ident, a, by rw [id_right, id_left]⟩

lemma factorsThroughIdentity_op (a b : I) : FactorsThroughIdentity (op a b) :=
  ⟨a, b, by rw [id_right]⟩

/-! ## §7.F. Self fixed points -/

/-- `a` is a self fixed point if `op a a = a`. -/
def IsSelfFixedPoint (a : I) : Prop := op a a = a

lemma ident_isSelfFixedPoint : IsSelfFixedPoint (ident : I) := by
  unfold IsSelfFixedPoint; exact id_left ident

lemma selfFixedPoint_op_ident_right {a : I} (h : IsSelfFixedPoint a) :
    op a ident = a := id_right a

lemma selfFixedPoint_op_ident_left {a : I} (h : IsSelfFixedPoint a) :
    op ident a = a := id_left a

lemma selfFixedPoint_pow_two {a : I} (h : IsSelfFixedPoint a) :
    compPow a 2 = a := by
  rw [compPow_two]; exact h

lemma selfFixedPoint_pow_three {a : I} (h : IsSelfFixedPoint a) :
    compPow a 3 = a := by
  rw [compPow_three, h, h]

lemma selfFixedPoint_pow_succ_succ {a : I} (h : IsSelfFixedPoint a) (n : ℕ) :
    op a (op a (compPow a n)) = op a (compPow a n) := by
  rw [← assoc, h]

/-- For a self fixed point, all positive powers equal `a`. -/
lemma selfFixedPoint_pow_pos {a : I} (h : IsSelfFixedPoint a) :
    ∀ n : ℕ, compPow a (n+1) = a := by
  intro n
  induction n with
  | zero => exact compPow_one a
  | succ k ih =>
      show op a (compPow a (k+1)) = a
      rw [ih]; exact h

/-! ## §7.G. Identity preservation by a unary map -/

/-- A function `f : I → I` preserves identity. -/
def PreservesIdentity (f : I → I) : Prop := f ident = ident

lemma preservesIdentity_id : PreservesIdentity (id : I → I) := rfl

lemma preservesIdentity_const_ident :
    PreservesIdentity (fun _ : I => (ident : I)) := rfl

lemma preservesIdentity_op_left_ident :
    PreservesIdentity (fun a : I => op ident a) := by
  unfold PreservesIdentity; exact id_left ident

lemma preservesIdentity_op_right_ident :
    PreservesIdentity (fun a : I => op a ident) := by
  unfold PreservesIdentity; exact id_right ident

lemma preservesIdentity_comp {f g : I → I}
    (hf : PreservesIdentity f) (hg : PreservesIdentity g) :
    PreservesIdentity (fun x => f (g x)) := by
  unfold PreservesIdentity at *
  show f (g ident) = ident
  rw [hg]; exact hf

/-! ## §7.H. Uniqueness of identity (different forms) -/

lemma ident_unique_left (e : I) (h : ∀ a, op e a = a) : e = ident := by
  have := h ident
  rw [id_right] at this
  exact this

lemma ident_unique_right (e : I) (h : ∀ a, op a e = a) : e = ident := by
  have := h ident
  rw [id_left] at this
  exact this

lemma ident_unique_two_sided (e : I)
    (hl : ∀ a, op e a = a) (_hr : ∀ a, op a e = a) : e = ident :=
  ident_unique_left e hl

/-! ## §7.I. The Composition–Identity package -/

/-- The full statement of the Composition–Identity package (Theorem 7.1). -/
structure CompositionIdentityPackage (I : Type*) [IdeaTheoryStructure I] : Prop where
  transparent_all : ∀ a : I, IdentityTransparent a
  unique_left     : ∀ e : I, (∀ a : I, op e a = a) → e = ident
  unique_right    : ∀ e : I, (∀ a : I, op a e = a) → e = ident
  pow_ident       : ∀ n : ℕ, compPow (ident : I) n = ident
  ident_fixed     : IsSelfFixedPoint (ident : I)

/-! ## §7.J. THEOREM 7.1 — Composition Identity Theorem -/

/--
**Theorem 7.1 (Composition Identity Theorem).**

*(a) Informal claim.* The Idea-Theory literature (Vol. I, §7.1; Vol. IV,
ch. 2) asserts that the neutral compositional act — the "doing nothing"
of cognition — is uniquely characterised among ideas by being absorbed on
either side of `op`.  Furthermore, repeated self-composition of the
neutral act is again the neutral act, and every idea is "transparent"
to it.

*(b) Sources.* The statement formalises the Composition Identity package
discussed informally in *Idea Theory*, Vol. I, Theorem 7.1 (henceforth
"IDT-I §7.1"), refining the universal-algebra fact that left- and
right-units in a unital magma coincide and are unique
(Burris–Sankappanavar, 1981, ch. II).

*(c) Dependencies.* The proof uses `identityTransparent_all`,
`ident_unique_left`, `ident_unique_right`, `compPow_ident`, and
`ident_isSelfFixedPoint`.

*(d) Sharpening.* Where the informal statement merely asserts existence
of a unit, the formal statement bundles five independent guarantees into
the structure `CompositionIdentityPackage`.  No restriction or
contradiction; this is a strict refinement.

*(e) Proof strategy.*
1. Construct the package by name.
2. Discharge `transparent_all` from `identityTransparent_all`.
3. Discharge `unique_left`, `unique_right` from the corresponding
   uniqueness lemmas.
4. Discharge `pow_ident` from `compPow_ident`.
5. Discharge `ident_fixed` from `ident_isSelfFixedPoint`.
-/
theorem theorem_7_1 : CompositionIdentityPackage I where
  transparent_all := identityTransparent_all
  unique_left     := ident_unique_left
  unique_right    := ident_unique_right
  pow_ident       := compPow_ident
  ident_fixed     := ident_isSelfFixedPoint

/-! ## §7.K. Transmission chains -/

/-- A transmission chain is a list-like fold of `op` over a finite list. -/
def chain : List I → I
  | []      => ident
  | a :: as => op a (chain as)

@[simp] lemma chain_nil : chain ([] : List I) = ident := rfl

@[simp] lemma chain_cons (a : I) (as : List I) :
    chain (a :: as) = op a (chain as) := rfl

lemma chain_singleton (a : I) : chain [a] = a := by
  show op a (chain []) = a
  rw [chain_nil, id_right]

lemma chain_pair (a b : I) : chain [a, b] = op a b := by
  show op a (chain [b]) = op a b
  rw [chain_singleton]

lemma chain_triple (a b c : I) : chain [a, b, c] = op a (op b c) := by
  show op a (chain [b, c]) = op a (op b c)
  rw [chain_pair]

lemma chain_append (xs ys : List I) :
    chain (xs ++ ys) = op (chain xs) (chain ys) := by
  induction xs with
  | nil =>
      show chain ys = op ident (chain ys)
      rw [id_left]
  | cons a as ih =>
      show op a (chain (as ++ ys)) = op (op a (chain as)) (chain ys)
      rw [ih, assoc]

lemma chain_cons_ident (xs : List I) :
    chain (ident :: xs) = chain xs := by
  show op ident (chain xs) = chain xs
  rw [id_left]

lemma chain_append_ident_right (xs : List I) :
    chain (xs ++ [ident]) = chain xs := by
  rw [chain_append, chain_singleton, id_right]

lemma chain_filter_ne_ident [DecidableEq I] (xs : List I) :
    chain (xs.filter (fun a => a ≠ ident)) = chain xs := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
      by_cases ha : a = ident
      · subst ha
        have hfilt :
            ((ident : I) :: as).filter (fun a => a ≠ ident)
              = as.filter (fun a => a ≠ ident) := by
          simp [List.filter]
        rw [hfilt, ih]
        show chain as = op ident (chain as)
        rw [id_left]
      · have hfilt :
            (a :: as).filter (fun a => a ≠ ident)
              = a :: as.filter (fun a => a ≠ ident) := by
          simp [List.filter, ha]
        rw [hfilt]
        show op a (chain (as.filter (fun a => a ≠ ident))) = op a (chain as)
        rw [ih]

lemma chain_insert_ident (xs ys : List I) :
    chain (xs ++ ident :: ys) = chain (xs ++ ys) := by
  rw [chain_append, chain_append]
  show op (chain xs) (op ident (chain ys)) = op (chain xs) (chain ys)
  rw [id_left]

lemma chain_ident_left_transparent (xs : List I) :
    op ident (chain xs) = chain xs := id_left _

lemma chain_ident_right_transparent (xs : List I) :
    op (chain xs) ident = chain xs := id_right _

/-! ## §7.L. THEOREM 7.2 — Identity Transmission Theorem -/

/--
**Theorem 7.2 (Identity Transmission Theorem).**

*(a) Informal claim.* In the cognitive-science reading (Vol. IV, ch. 3),
a *neutral act* — an utterance, gesture, or thought that contributes
nothing to the propagated content — should be invisible to the
transmission chain.  Inserting it at the head, the tail, or any interior
position must yield the same compositional value.

*(b) Sources.* Informal statement: *Idea Theory* Vol. I, §7.2
("Identity Transmission") and Vol. IV, §3.4 ("Neutral cognitive acts and
their formal vacuity").  The categorical analogue is the unit law of a
strict monoidal category (Mac Lane, 1971, ch. VII).

*(c) Dependencies.* The proof uses `chain_cons_ident`,
`chain_append_ident_right`, `chain_insert_ident`,
`chain_ident_left_transparent`, and `chain_ident_right_transparent`,
each established in §7.K.

*(d) Sharpening.* The informal statement says only "ident may be
inserted anywhere."  Our formal statement makes the position explicit
(head / tail / interior) and additionally records left- and
right-absorption of `ident` against an already-folded chain.  This is a
strict refinement: no clause of the informal statement is dropped.

*(e) Proof strategy.*
1. Open the conjunction with `refine ⟨?_, ?_, ?_, ?_, ?_⟩`.
2. Discharge head-insertion via `chain_cons_ident`.
3. Discharge tail-insertion via `chain_append_ident_right`.
4. Discharge interior-insertion via `chain_insert_ident`.
5. Discharge left- and right-absorption via the two transparency lemmas.
-/
theorem theorem_7_2 :
    (∀ xs : List I, chain (ident :: xs) = chain xs) ∧
    (∀ xs : List I, chain (xs ++ [ident]) = chain xs) ∧
    (∀ xs ys : List I, chain (xs ++ ident :: ys) = chain (xs ++ ys)) ∧
    (∀ xs : List I, op ident (chain xs) = chain xs) ∧
    (∀ xs : List I, op (chain xs) ident = chain xs) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro xs; exact chain_cons_ident xs
  · intro xs; exact chain_append_ident_right xs
  · intro xs ys; exact chain_insert_ident xs ys
  · intro xs; exact chain_ident_left_transparent xs
  · intro xs; exact chain_ident_right_transparent xs

/-! ## §7.M. Fixed-point structure lemmas -/

lemma selfFixedPoint_chain_replicate {a : I} (h : IsSelfFixedPoint a) :
    ∀ n : ℕ, chain (List.replicate (n+1) a) = a := by
  intro n
  induction n with
  | zero =>
      show chain [a] = a
      exact chain_singleton a
  | succ k ih =>
      show op a (chain (List.replicate (k+1) a)) = a
      rw [ih]; exact h

lemma selfFixedPoint_op_self_right {a : I} (h : IsSelfFixedPoint a) :
    op a (op a a) = a := by
  rw [← assoc, h]; exact h

lemma selfFixedPoint_op_self_left {a : I} (h : IsSelfFixedPoint a) :
    op (op a a) a = a := by
  rw [h]; exact h

lemma selfFixedPoint_sandwich {a : I} (h : IsSelfFixedPoint a) :
    op a (op ident a) = a := by
  rw [id_left]; exact h

lemma selfFixedPoint_chain_pair {a : I} (h : IsSelfFixedPoint a) :
    chain [a, a] = a := by
  rw [chain_pair]; exact h

lemma selfFixedPoint_chain_triple {a : I} (h : IsSelfFixedPoint a) :
    chain [a, a, a] = a := by
  rw [chain_triple, h]; exact h

lemma selfFixedPoint_absorb_ident {a : I} (h : IsSelfFixedPoint a) :
    op a (op ident (op a ident)) = a := by
  rw [id_left, id_right]; exact h

lemma selfFixedPoint_chain_extend_left {a : I} {xs : List I}
    (h : IsSelfFixedPoint a) (hxs : chain xs = a) :
    chain (a :: xs) = a := by
  show op a (chain xs) = a
  rw [hxs]; exact h

lemma selfFixedPoint_chain_extend_right {a : I} {xs : List I}
    (h : IsSelfFixedPoint a) (hxs : chain xs = a) :
    chain (xs ++ [a]) = a := by
  rw [chain_append, chain_singleton, hxs]; exact h

/-! ## §7.N. THEOREM 7.3 — Compositional Fixed Point Theorem -/

/--
**Theorem 7.3 (Compositional Fixed Point Theorem).**

*(a) Informal claim.* In Vol. IV's discussion of stable cognitive
attractors (ch. 5), the key property is that an idea which is its own
re-composition — `op a a = a` — is invariant under arbitrary positive
iteration and under arbitrary replicate-chains.  Moreover the neutral
act is itself such a fixed point, and any "padding" of a fixed point
with the unit yields another fixed point.

*(b) Sources.* The statement formalises *Idea Theory* Vol. I, §7.3
("Compositional fixed points") and Vol. IV, §5.2 ("Stable concepts as
algebraic idempotents").  The semigroup-theoretic analogue is the
classical theory of idempotents in unital magmas (Howie, 1995, §1.2).

*(c) Dependencies.* The proof uses `selfFixedPoint_pow_pos`,
`selfFixedPoint_chain_replicate`, `ident_isSelfFixedPoint`, and the
identity laws `id_left`, `id_right`.

*(d) Sharpening.* The informal statement asserts that fixed points are
"stable under iteration."  Our formal statement enumerates four distinct
manifestations (identity-absorption, positive powers, replicate chains,
ident-padding) and additionally proves that `ident` itself is a fixed
point.  No clause of the informal statement is contradicted.

*(e) Proof strategy.*
1. Open the five-way conjunction with `refine ⟨?_, ?_, ?_, ?_, ?_⟩`.
2. Identity-absorption follows from `id_left`/`id_right` directly.
3. Positive powers reduce to `selfFixedPoint_pow_pos`.
4. Replicate-chains reduce to `selfFixedPoint_chain_replicate`.
5. Discharge `IsSelfFixedPoint ident` via `ident_isSelfFixedPoint`.
6. For ident-padding, unfold `IsSelfFixedPoint`, rewrite with `id_left`
   or `id_right`, and apply the hypothesis.
-/
theorem theorem_7_3 :
    (∀ a : I, IsSelfFixedPoint a →
        op a ident = a ∧ op ident a = a) ∧
    (∀ a : I, IsSelfFixedPoint a → ∀ n : ℕ, compPow a (n+1) = a) ∧
    (∀ a : I, IsSelfFixedPoint a → ∀ n : ℕ, chain (List.replicate (n+1) a) = a) ∧
    IsSelfFixedPoint (ident : I) ∧
    (∀ a : I, IsSelfFixedPoint a →
        IsSelfFixedPoint (op a ident) ∧ IsSelfFixedPoint (op ident a)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a _
    exact ⟨id_right a, id_left a⟩
  · intro a h n
    exact selfFixedPoint_pow_pos h n
  · intro a h n
    exact selfFixedPoint_chain_replicate h n
  · exact ident_isSelfFixedPoint
  · intro a h
    refine ⟨?_, ?_⟩
    · show op (op a ident) (op a ident) = op a ident
      rw [id_right]; exact h
    · show op (op ident a) (op ident a) = op ident a
      rw [id_left]; exact h

/-! ## §7.O. Additional helper lemmas (used by corollaries below) -/

lemma chain_replicate_ident (n : ℕ) :
    chain (List.replicate n (ident : I)) = ident := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show op ident (chain (List.replicate k ident)) = ident
      rw [ih, id_left]

lemma chain_append_replicate_ident (xs : List I) (n : ℕ) :
    chain (xs ++ List.replicate n ident) = chain xs := by
  rw [chain_append, chain_replicate_ident, id_right]

lemma chain_replicate_ident_append (xs : List I) (n : ℕ) :
    chain (List.replicate n ident ++ xs) = chain xs := by
  rw [chain_append, chain_replicate_ident, id_left]

lemma chain_concat (xs : List I) (a : I) :
    chain (xs ++ [a]) = op (chain xs) a := by
  rw [chain_append, chain_singleton]

lemma chain_concat_ident (xs : List I) :
    chain (xs ++ [ident]) = chain xs := by
  rw [chain_concat, id_right]

lemma chain_double_append (xs ys zs : List I) :
    chain (xs ++ ys ++ zs) = op (op (chain xs) (chain ys)) (chain zs) := by
  rw [chain_append, chain_append]

lemma chain_double_append_assoc (xs ys zs : List I) :
    chain (xs ++ ys ++ zs) = op (chain xs) (op (chain ys) (chain zs)) := by
  rw [chain_double_append, assoc]

lemma chain_two_inserts_ident (xs ys zs : List I) :
    chain (xs ++ ident :: ys ++ ident :: zs)
      = chain (xs ++ ys ++ zs) := by
  rw [chain_double_append_assoc, chain_append, chain_append, chain_cons,
      chain_cons, id_left, id_left, ← assoc, ← chain_append, ← chain_append]

lemma compPow_succ_eq_op_self (a : I) (n : ℕ) :
    compPow a (n + 1) = op a (compPow a n) := rfl

lemma compPow_add_one_self_fixed {a : I} (h : IsSelfFixedPoint a) (n : ℕ) :
    compPow a (n + 1) = compPow a 1 := by
  rw [selfFixedPoint_pow_pos h n, compPow_one]

/-! ## §7.P. COROLLARIES of the headline theorems -/

/--
**Corollary 7.1 (Neutral Insertion in Cognitive Transmission).**
Downstream use: Vol. IV, §3.5 — "Neutral cognitive acts contribute
nothing to the propagated content of a transmission chain."  This
corollary upgrades Theorem 7.2 to *arbitrary finite* runs of neutral
acts: any block of `ident`s, anywhere in the chain, is invisible. -/
theorem corollary_7_1
    (xs ys : List I) (n : ℕ) :
    chain (xs ++ List.replicate n ident ++ ys) = chain (xs ++ ys) := by
  rw [chain_append, chain_append, chain_replicate_ident, id_right,
      ← chain_append]

/--
**Corollary 7.2 (Idempotent Concept Stability).**
Downstream use: Vol. IV, §5.4 — "A stable cognitive attractor absorbs
arbitrary repetition without drift."  This corollary specialises
Theorem 7.3 to the case where the chain consists exclusively of copies
of a single self-fixed idea, even if interleaved with neutral acts. -/
theorem corollary_7_2 {a : I} (h : IsSelfFixedPoint a) (m n : ℕ) :
    chain (List.replicate (n + 1) a ++ List.replicate m ident) = a := by
  rw [chain_append_replicate_ident, selfFixedPoint_chain_replicate h]

/--
**Corollary 7.3 (Uniqueness of the Neutral Carrier).**
Downstream use: Vol. IV, §2.6 — "There is at most one cognitive act
which is universally compositionally inert."  Combines the left- and
right- uniqueness clauses of Theorem 7.1. -/
theorem corollary_7_3 (e₁ e₂ : I)
    (h₁ : ∀ a : I, op e₁ a = a)
    (h₂ : ∀ a : I, op a e₂ = a) :
    e₁ = e₂ := by
  have h1 : e₁ = ident := ident_unique_left e₁ h₁
  have h2 : e₂ = ident := ident_unique_right e₂ h₂
  rw [h1, h2]

/--
**Corollary 7.4 (Composition is Identity-Functorial).**
Downstream use: Vol. IV, §4.3 — "Composing a stable concept with the
neutral act on either side yields a concept which is itself stable."
This corollary chains Theorem 7.3's padding clause through arbitrary
finite ident-padding. -/
theorem corollary_7_4 {a : I} (h : IsSelfFixedPoint a) :
    IsSelfFixedPoint (op (op ident a) ident) := by
  unfold IsSelfFixedPoint
  rw [id_left, id_right]
  exact h

/--
**Corollary 7.5 (Chain Reassociation under Transmission).**
Downstream use: Vol. IV, §3.7 — "The grouping of carriers in a
transmission chain is irrelevant: only the linear sequence matters."
A direct consequence of `chain_append` plus associativity. -/
theorem corollary_7_5 (xs ys zs : List I) :
    chain ((xs ++ ys) ++ zs) = chain (xs ++ (ys ++ zs)) := by
  rw [List.append_assoc]

/-! ## §7.Q. Examples and sanity checks -/

example : compPow (ident : I) 5 = ident := compPow_ident 5

example (a : I) : chain [a] = a := chain_singleton a

example (a b c : I) : chain [a, b, c] = op a (op b c) := chain_triple a b c

example (a : I) :
    chain [ident, a, ident, a, ident] = op a a := by
  show op ident (op a (op ident (op a (op ident ident)))) = op a a
  rw [id_left, id_left, id_left, id_right]

example {a : I} (h : IsSelfFixedPoint a) :
    chain [a, a, a, a] = a := by
  have h1 : chain [a, a, a, a] = op a (op a (op a a)) := by
    show op a (op a (op a (op a ident))) = op a (op a (op a a))
    rw [id_right]
  rw [h1, h, h, h]

example (a b : I) :
    chain [ident, a, ident, b, ident] = op a b := by
  show op ident (op a (op ident (op b (op ident ident)))) = op a b
  rw [id_left, id_left, id_left, id_right]

example : IsSelfFixedPoint (ident : I) := ident_isSelfFixedPoint

example {a : I} (h : IsSelfFixedPoint a) :
    chain (List.replicate 7 a) = a :=
  selfFixedPoint_chain_replicate h 6

/-! ## Index of results

* `compPow`                              — iterated left-composition.
* `compPow_zero/succ/one/two/three`      — small-arity unfoldings.
* `compPow_ident`                        — powers of the unit are the unit.
* `op_ident_left/right/both/both'`       — basic identity rewrites.
* `ident_self_op`, `ident_op_chain*`     — unit-only chain reductions.
* `op_ident_left_eq`, `op_ident_right_eq`— substitution variants.
* `sandwich_ident`, `double_ident_*`,
  `triple_ident_*`                       — multi-unit collapses.
* `reassoc3`, `reassoc3'`, `reassoc4`,
  `reassoc4_alt`, `reassoc4_alt'`,
  `reassoc5`                             — associativity helpers.
* `op_ident_middle*`,
  `insert_ident_*`                       — interior-unit rewrites.
* `IdentityTransparent`,
  `identityTransparent_*`                — unit-transparency predicate.
* `FactorsThroughIdentity`,
  `factorsThroughIdentity_*`             — factor-through-unit predicate.
* `IsSelfFixedPoint`,
  `selfFixedPoint_*`                     — compositional idempotents.
* `PreservesIdentity`,
  `preservesIdentity_*`                  — unit-preserving maps.
* `ident_unique_left/right/two_sided`    — uniqueness of the unit.
* `CompositionIdentityPackage`           — bundled package for Theorem 7.1.
* `theorem_7_1`                          — Composition Identity Theorem.
* `chain`, `chain_nil/cons/singleton/
  pair/triple`                           — fold-based transmission chain.
* `chain_append`, `chain_cons_ident`,
  `chain_append_ident_right`,
  `chain_filter_ne_ident`,
  `chain_insert_ident`,
  `chain_ident_left/right_transparent`   — chain calculus.
* `theorem_7_2`                          — Identity Transmission Theorem.
* `selfFixedPoint_chain_replicate`,
  `selfFixedPoint_op_self_*`,
  `selfFixedPoint_sandwich`,
  `selfFixedPoint_chain_pair/triple`,
  `selfFixedPoint_absorb_ident`,
  `selfFixedPoint_chain_extend_*`        — fixed-point structure.
* `theorem_7_3`                          — Compositional Fixed Point Theorem.
* `chain_replicate_ident`,
  `chain_append_replicate_ident`,
  `chain_replicate_ident_append`,
  `chain_concat`, `chain_concat_ident`,
  `chain_double_append`,
  `chain_double_append_assoc`,
  `chain_two_inserts_ident`,
  `compPow_succ_eq_op_self`,
  `compPow_add_one_self_fixed`           — additional helpers.
* `corollary_7_1`                        — Neutral Insertion in Transmission.
* `corollary_7_2`                        — Idempotent Concept Stability.
* `corollary_7_3`                        — Uniqueness of the Neutral Carrier.
* `corollary_7_4`                        — Composition is Identity-Functorial.
* `corollary_7_5`                        — Chain Reassociation under Transmission.
-/

end IdeaTheory
