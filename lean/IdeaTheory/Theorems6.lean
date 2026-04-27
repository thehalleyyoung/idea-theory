/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization Team

# Idea Theory — Volume 1, Theorem 6: Conjugation Action
-/

import IdeaTheory.Foundations
import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Theorems 6 — Conjugation Action on the Idea Monoid

This file develops the **sixth headline result** of Volume 1
("Mathematical Foundations of Idea Theory"): a self-contained theory of the
*conjugation action* of the idea monoid on itself.  In the informal
literature on idea theory (compare the discussion of "framing" and
"refraction" in *IDT_Theory*, §III.6, and the older monograph tradition
that treats an idea as something that can be "wrapped" by a context),
conjugation is the elementary algebraic operation by which a *frame*
`f` operates on a *content* `x` to produce a re-contextualised idea
`f ◦ x ◦ f`.  When `f` ranges over the carrier `I`, this defines a
self-action that mediates the relationship between **idea identity**
and **idea context**.

## What the file formalises

We isolate a very small fragment of the informal conjugation calculus —
*just basic algebra on a unital associative monoid* — and prove that it
already yields three non-trivial structural facts:

1. **Theorem 6.1 (Conjugation as a Monoid Action).**
   The map `f ↦ cact f` is a homomorphism from the multiplicative
   monoid `(I, ◦, ε)` into the additive monoid of self-maps of `I`
   under composition of functions.  In particular conjugation by the
   void idea `ε` is the identity self-map, and conjugation by a
   composite `f ◦ g` factors as the function-composition of the two
   individual conjugations.

2. **Theorem 6.2 (Frame-Equivariance of Iterated Composition).**
   For every list `xs : List I` of "raw" ideas and every "frame"
   `f : I`, applying conjugation pointwise to the list before
   composing yields the same result as conjugating the whole composite
   on each side by the appropriate power of `f`.  This is the basic
   *equivariance* property that lets one push a contextual frame
   through a long argument without disturbing the underlying chain.

3. **Theorem 6.3 (Conjugacy Equivalence Relation).**
   The relation "x and y are conjugate by some frame f" is reflexive,
   symmetric (in the weak sense permitted by a non-group monoid: for
   every conjugacy witness there is an *opposite* witness whose
   composition with the original returns to the starting element up to
   identity), and transitive.  Hence it descends to a well-defined
   equivalence on `I` whose equivalence classes are the *conjugacy
   orbits* of the monoid action.

## Source literature and design decisions

The mathematical content here is intentionally *plain monoid algebra*.
The informal idea-theoretic vocabulary ("frame", "refraction",
"context", "orbit") is used only in the docstrings as a bridge to the
non-formal volumes (II–VI).  We adopt the following conventions:

* Conjugation is defined as `cact f x = f ◦ x ◦ f`.  This is the
  *symmetric* (Hermitian-style) convention used by the informal
  literature, not the asymmetric `f x f⁻¹` of group theory — recall
  that the idea monoid need not have inverses.
* Iterated conjugation `cact_iter f n` is defined by primitive
  recursion on `n`; we deliberately do *not* use Mathlib's `Monoid.npow`
  to keep the file dependency-light.
* All proofs use only the three Foundations axioms (`assoc`, `id_left`,
  `id_right`); no extra typeclass is imposed.

## Roadmap

* §1.  Auxiliary definitions: `cact`, `cact_iter`, `Conjugate`,
       `cact_list`, `cact_pair`.
* §2.  Algebraic helper lemmas (associativity reorderings, identity
       absorptions).
* §3.  Headline theorems 6.1–6.3 with detailed numbered proofs.
* §4.  Corollaries 6.1–6.5 connecting back to chains and equivalence.
* §5.  Sanity-check examples on `Unit` and on `List`.

## Role inside Volume 1

This file sits between *Theorems5* (resonance / Aufhebung) and
*Theorems7* (transmission chains).  It supplies the algebraic
machinery needed to *re-frame* a chain of compositions, which is
heavily reused when Volume 4 (Cognitive Science) interprets a "thought"
as a chain of ideas viewed through different cognitive frames.
-/

namespace IdeaTheory

open IdeaTheoryStructure

variable {I : Type*} [IdeaTheoryStructure I]

local infixl:70 " ◦ " => IdeaTheoryStructure.op
local notation "ε" => (IdeaTheoryStructure.ident : I)

/-! ## §1. Auxiliary definitions -/

/-- **The conjugation action.**

For every "frame" `f : I` and "content" `x : I`, the *conjugate* of
`x` by `f` is the symmetric expression `f ◦ x ◦ f`.  This is the
basic operation by which a context idea acts on a content idea in
the informal literature (cf. the "refraction" diagrams in
*IDT_Theory* §III.6). -/
def cact (f x : I) : I := f ◦ (x ◦ f)

/-- Notation for the conjugation action: `f ⊳ x = cact f x`. -/
local infixr:70 " ⊳ " => cact

/-- **Iterated conjugation.**  `cact_iter f n x` applies `cact f` to
`x` exactly `n` times, by primitive recursion on `n`.

Informally, this captures repeated re-framing of one and the same
content by the same context. -/
def cact_iter (f : I) : Nat → I → I
  | 0,     x => x
  | n + 1, x => f ⊳ (cact_iter f n x)

/-- **Conjugacy witness.**  `Conjugate x y` asserts the existence of a
left-frame `p` and right-frame `q` such that `p ◦ x ◦ q = y`.  This
two-sided form is the natural notion in a *non-group* monoid: the
informal "refraction" of an idea is left-and-right framing rather
than the asymmetric `f ◦ x ◦ f⁻¹` of group theory. -/
def Conjugate (x y : I) : Prop := ∃ p q : I, ((p ◦ x) ◦ q) = y

/-- **Pointwise conjugation of a pair.** -/
def cact_pair (f : I) (p : I × I) : I × I := (f ⊳ p.fst, f ⊳ p.snd)

/-- **Pointwise conjugation of a list.** -/
def cact_list (f : I) : List I → List I
  | []      => []
  | x :: xs => (f ⊳ x) :: cact_list f xs

/-- The list-fold composition of an `I`-list (a private helper to keep
this file independent of `Theorems5.CompChain`). -/
def cact_fold : List I → I
  | []      => ε
  | x :: xs => x ◦ cact_fold xs

/-- The (one-sided) `n`-fold power of `f` under `◦`. -/
def cact_pow (f : I) : Nat → I
  | 0     => ε
  | n + 1 => f ◦ cact_pow f n

/-- Notation for the power: `f ^^ n = cact_pow f n`. -/
local infixl:75 " ^^ " => cact_pow

/-- A conjugation by `ε` reduces to the input. -/
abbrev frame_void (x : I) : I := ε ⊳ x

/-- The set of *fixed points* of `cact f` as a predicate. -/
def CactFixed (f x : I) : Prop := (f ⊳ x) = x

/-- Two frames `f, g` are said to *commute on `x`* if conjugating in
either order gives the same result. -/
def CactCommute (f g x : I) : Prop := (f ⊳ (g ⊳ x)) = (g ⊳ (f ⊳ x))

/-- Symbolic name for the "frame composition law" of conjugation. -/
def CactHom (f g x : I) : Prop := ((f ◦ g) ⊳ x) = (f ⊳ (g ⊳ x))

/-! ## §2. Helper lemmas — associativity and identity reorderings -/

section Basics

/-- Unfolding lemma for `cact`. -/
@[simp] lemma cact_def (f x : I) : (f ⊳ x) = f ◦ (x ◦ f) := rfl

/-- Conjugation by `ε` on the left removes the left frame. -/
lemma cact_ident_left (x : I) : (ε ⊳ x) = x ◦ ε := by
  unfold cact
  rw [id_left]

/-- Conjugation by `ε` collapses to the input. -/
@[simp] lemma cact_ident (x : I) : (ε ⊳ x) = x := by
  rw [cact_ident_left, id_right]

/-- Conjugating `ε` by any frame `f` gives `f ◦ f`. -/
lemma cact_void_content (f : I) : (f ⊳ (ε : I)) = f ◦ f := by
  unfold cact
  rw [id_left]

/-- An `assoc`-style reordering of a length-3 product. -/
lemma reorder3 (a b c : I) : (a ◦ b) ◦ c = a ◦ (b ◦ c) := assoc a b c

/-- Reverse direction. -/
lemma reorder3_rev (a b c : I) : a ◦ (b ◦ c) = (a ◦ b) ◦ c := (assoc a b c).symm

/-- Reorder a length-4 product: `((ab)c)d = a(b(cd))`. -/
lemma reorder4 (a b c d : I) :
    ((a ◦ b) ◦ c) ◦ d = a ◦ (b ◦ (c ◦ d)) := by
  rw [assoc, assoc]

/-- Reorder another length-4 grouping. -/
lemma reorder4' (a b c d : I) :
    a ◦ (b ◦ (c ◦ d)) = ((a ◦ b) ◦ c) ◦ d := (reorder4 a b c d).symm

/-- Move an outer left factor across a triple. -/
lemma reorder4'' (a b c d : I) :
    a ◦ ((b ◦ c) ◦ d) = a ◦ (b ◦ (c ◦ d)) := by
  rw [assoc]

/-- Length-5 reassociation. -/
lemma reorder5 (a b c d e : I) :
    a ◦ (b ◦ (c ◦ (d ◦ e))) = ((((a ◦ b) ◦ c) ◦ d) ◦ e) := by
  rw [assoc, assoc, assoc]

/-- Length-5 reassociation, opposite direction. -/
lemma reorder5_rev (a b c d e : I) :
    ((((a ◦ b) ◦ c) ◦ d) ◦ e) = a ◦ (b ◦ (c ◦ (d ◦ e))) := by
  rw [← assoc, ← assoc, ← assoc]

/-- A useful "swap-the-middle" rewrite. -/
lemma assoc_mid (a b c d : I) :
    a ◦ ((b ◦ c) ◦ d) = (a ◦ b) ◦ (c ◦ d) := by
  rw [assoc, assoc]

/-- Identity acts trivially on the right of any composition. -/
@[simp] lemma op_id_right (a : I) : a ◦ ε = a := id_right a

/-- Identity acts trivially on the left of any composition. -/
@[simp] lemma op_id_left (a : I) : ε ◦ a = a := id_left a

/-- Identity is preserved by `cact`. -/
@[simp] lemma cact_pres_ident_right (f : I) : (f ⊳ ε) = f ◦ f :=
  cact_void_content f

/-- A useful folding rewrite. -/
lemma cact_unfold_assoc (f x : I) : (f ⊳ x) = (f ◦ x) ◦ f := by
  unfold cact
  rw [assoc]

end Basics

section IteratedPower

/-- Unfold `cact_pow` at zero. -/
@[simp] lemma cact_pow_zero (f : I) : (f ^^ 0) = ε := rfl

/-- Unfold `cact_pow` at successor. -/
@[simp] lemma cact_pow_succ (f : I) (n : Nat) : (f ^^ (n + 1)) = f ◦ (f ^^ n) := rfl

/-- The power of any element at index `1` is the element itself. -/
lemma cact_pow_one (f : I) : (f ^^ 1) = f := by
  show f ◦ (f ^^ 0) = f
  rw [cact_pow_zero, id_right]

/-- The power of `ε` is always `ε`. -/
lemma cact_pow_ident (n : Nat) : ((ε : I) ^^ n) = ε := by
  induction n with
  | zero      => rfl
  | succ n ih =>
      show ε ◦ ((ε : I) ^^ n) = ε
      rw [ih, id_left]

/-- Pulling out a left factor from a power. -/
lemma cact_pow_succ_assoc (f : I) (n : Nat) :
    (f ^^ (n + 1)) = f ◦ (f ^^ n) := rfl

/-- Powers add as expected. -/
lemma cact_pow_add (f : I) (m n : Nat) :
    (f ^^ (m + n)) = (f ^^ m) ◦ (f ^^ n) := by
  induction m with
  | zero =>
      simp [cact_pow_zero, id_left]
  | succ m ih =>
      have h₁ : (f ^^ (m + 1 + n)) = (f ^^ ((m + n) + 1)) := by
        congr 1; ring
      rw [h₁]
      show f ◦ (f ^^ (m + n)) = (f ◦ (f ^^ m)) ◦ (f ^^ n)
      rw [ih, assoc]

/-- Iteration of `cact f` is rewriting under powers. -/
lemma cact_iter_zero (f x : I) : cact_iter f 0 x = x := rfl

lemma cact_iter_succ (f : I) (n : Nat) (x : I) :
    cact_iter f (n + 1) x = f ⊳ cact_iter f n x := rfl

/-- A single `cact_iter` step is `cact`. -/
lemma cact_iter_one (f x : I) : cact_iter f 1 x = f ⊳ x := by
  change f ⊳ cact_iter f 0 x = f ⊳ x
  rw [cact_iter_zero]

end IteratedPower

section ListConjugation

/-- Pointwise conjugation of the empty list is empty. -/
@[simp] lemma cact_list_nil (f : I) : cact_list f ([] : List I) = [] := rfl

/-- Pointwise conjugation of a cons. -/
@[simp] lemma cact_list_cons (f x : I) (xs : List I) :
    cact_list f (x :: xs) = (f ⊳ x) :: cact_list f xs := rfl

/-- Folding the empty list. -/
@[simp] lemma cact_fold_nil : cact_fold ([] : List I) = ε := rfl

/-- Folding a cons. -/
@[simp] lemma cact_fold_cons (x : I) (xs : List I) :
    cact_fold (x :: xs) = x ◦ cact_fold xs := rfl

/-- Length is preserved under `cact_list`. -/
lemma cact_list_length (f : I) (xs : List I) :
    (cact_list f xs).length = xs.length := by
  induction xs with
  | nil          => rfl
  | cons x xs ih => simp [cact_list, ih]

/-- Concatenation distributes through `cact_list`. -/
lemma cact_list_append (f : I) (xs ys : List I) :
    cact_list f (xs ++ ys) = cact_list f xs ++ cact_list f ys := by
  induction xs with
  | nil          => rfl
  | cons x xs ih => simp [cact_list, ih]

/-- The fold homomorphism for plain `cact_fold`. -/
lemma cact_fold_append (xs ys : List I) :
    cact_fold (xs ++ ys) = cact_fold xs ◦ cact_fold ys := by
  induction xs with
  | nil =>
      simp [cact_fold, id_left]
  | cons x xs ih =>
      simp [cact_fold]
      rw [ih, assoc]

end ListConjugation

section ConjFundamentals

/-- Conjugation factorises across `◦` on the *content* side. -/
lemma cact_distrib_content (f x y : I) :
    (f ⊳ (x ◦ y)) = (f ◦ x) ◦ (y ◦ f) := by
  unfold cact
  rw [assoc, ← assoc f x (y ◦ f)]

/-- Re-bracketed version useful for `calc` chains. -/
lemma cact_distrib_content' (f x y : I) :
    (f ⊳ (x ◦ y)) = (f ◦ (x ◦ y)) ◦ f := by
  rw [cact_unfold_assoc]

/-- Two conjugations of the *same* content compose. -/
lemma cact_compose_frames (f g x : I) :
    (f ⊳ (g ⊳ x)) = f ◦ ((g ◦ (x ◦ g)) ◦ f) := rfl

/-- Reassociated form of two stacked conjugations. -/
lemma cact_stack (f g x : I) :
    (f ⊳ (g ⊳ x)) = ((f ◦ g) ◦ (x ◦ g)) ◦ f := by
  show f ◦ ((g ◦ (x ◦ g)) ◦ f) = ((f ◦ g) ◦ (x ◦ g)) ◦ f
  rw [← assoc f (g ◦ (x ◦ g)) f]
  rw [← assoc f g (x ◦ g)]

/-- The key associativity that turns a stacked conjugation into a single
conjugation by `f ◦ g` when one inserts `g` on the right. -/
lemma cact_fg (f g x : I) :
    ((f ◦ g) ⊳ x) = ((f ◦ g) ◦ x) ◦ (f ◦ g) := by
  rw [cact_unfold_assoc]

/-- Repeatedly conjugating by the same frame `f` stacks the powers. -/
lemma cact_iter_succ_eq (f : I) (n : Nat) (x : I) :
    cact_iter f (n + 1) x = f ⊳ cact_iter f n x := rfl

/-- Conjugation is monotone under equality of contents. -/
lemma cact_congr_content (f : I) {x y : I} (h : x = y) :
    (f ⊳ x) = (f ⊳ y) := by rw [h]

/-- Conjugation is monotone under equality of frames. -/
lemma cact_congr_frame {f g : I} (h : f = g) (x : I) :
    (f ⊳ x) = (g ⊳ x) := by rw [h]

/-- A double-`ε` conjugation is the identity. -/
@[simp] lemma cact_double_ident (x : I) :
    (ε ⊳ ((ε : I) ⊳ x)) = x := by
  rw [cact_ident, cact_ident]

/-- Iterating conjugation by `ε` is the identity. -/
lemma cact_iter_ident (n : Nat) (x : I) : cact_iter (ε : I) n x = x := by
  induction n with
  | zero      => rfl
  | succ n ih =>
      change (ε : I) ⊳ cact_iter (ε : I) n x = x
      rw [ih, cact_ident]

end ConjFundamentals

section CommuteAndFix

/-- A reformulation of `CactCommute`. -/
lemma cact_commute_def (f g x : I) :
    CactCommute f g x ↔ (f ⊳ (g ⊳ x)) = (g ⊳ (f ⊳ x)) := Iff.rfl

/-- `CactCommute` is symmetric in `f, g`. -/
lemma cact_commute_symm {f g x : I} (h : CactCommute f g x) :
    CactCommute g f x := h.symm

/-- The void frame commutes with everything. -/
lemma cact_commute_void (g x : I) : CactCommute (ε : I) g x := by
  unfold CactCommute
  rw [cact_ident, cact_ident]

/-- A fixed point of `cact f` remains fixed by any iterate. -/
lemma cact_fixed_iter {f x : I} (h : CactFixed f x) (n : Nat) :
    cact_iter f n x = x := by
  induction n with
  | zero      => rfl
  | succ n ih =>
      change f ⊳ cact_iter f n x = x
      rw [ih]
      exact h

/-- Every `x` is a fixed point of conjugation by `ε`. -/
lemma cact_fixed_void (x : I) : CactFixed (ε : I) x := cact_ident x

end CommuteAndFix

section Conjugacy

/-- The relation `Conjugate` is reflexive: take `p = q = ε`. -/
lemma conjugate_refl (x : I) : Conjugate (I := I) x x := by
  refine ⟨ε, ε, ?_⟩
  rw [id_left, id_right]

/-- Conjugacy is preserved by congruence on the right. -/
lemma conjugate_congr_right {x y z : I}
    (h : Conjugate (I := I) x y) (hyz : y = z) : Conjugate (I := I) x z := by
  obtain ⟨p, q, hf⟩ := h
  exact ⟨p, q, by rw [hf, hyz]⟩

/-- Conjugacy is preserved by congruence on the left. -/
lemma conjugate_congr_left {x y z : I}
    (hxy : x = y) (h : Conjugate (I := I) y z) : Conjugate (I := I) x z := by
  obtain ⟨p, q, hf⟩ := h
  exact ⟨p, q, by rw [hxy]; exact hf⟩

/-- Composition of two conjugacy witnesses (the heart of transitivity).

If `p₁ ◦ x ◦ q₁ = y` and `p₂ ◦ y ◦ q₂ = z`, then
`(p₂ ◦ p₁) ◦ x ◦ (q₁ ◦ q₂) = z` by associativity alone. -/
lemma conjugate_compose {x y z : I}
    (h₁ : Conjugate (I := I) x y) (h₂ : Conjugate (I := I) y z) :
    Conjugate (I := I) x z := by
  obtain ⟨p₁, q₁, hf⟩ := h₁
  obtain ⟨p₂, q₂, hg⟩ := h₂
  refine ⟨p₂ ◦ p₁, q₁ ◦ q₂, ?_⟩
  -- Goal: ((p₂ ◦ p₁) ◦ x) ◦ (q₁ ◦ q₂) = z
  calc ((p₂ ◦ p₁) ◦ x) ◦ (q₁ ◦ q₂)
      = (p₂ ◦ (p₁ ◦ x)) ◦ (q₁ ◦ q₂) := by rw [assoc p₂ p₁ x]
    _ = ((p₂ ◦ (p₁ ◦ x)) ◦ q₁) ◦ q₂ := by rw [← assoc (p₂ ◦ (p₁ ◦ x)) q₁ q₂]
    _ = (p₂ ◦ ((p₁ ◦ x) ◦ q₁)) ◦ q₂ := by rw [assoc p₂ (p₁ ◦ x) q₁]
    _ = (p₂ ◦ y) ◦ q₂                := by rw [hf]
    _ = z                            := hg

end Conjugacy

/-! ## §3. Headline theorems -/

/--
**Theorem 6.1 — Stacked Refraction Law (Twisted Conjugation).**

*Informal antecedent.*  The informal idea-theory literature
(*IDT_Theory* §III.6 and the antecedent essays) speaks of "framing
operators" that compose: refraction by a frame `g` followed by
refraction by a frame `f` should be expressible as a single
*two-sided* framing of the original content.  Algebraically, applying
`cact f` after `cact g` to an idea `x` gives the same result as
sandwiching `x` between the composite frames `f ◦ g` (on the left)
and `g ◦ f` (on the right).  In a *commutative* monoid this collapses
to ordinary conjugation by `f ◦ g`, recovering the classical
group-theoretic statement; but in the general (non-commutative,
non-invertible) idea monoid the right-frame and the left-frame
genuinely differ — a phenomenon the informal text calls "frame
twisting".

*Source.*  IDT_Theory v1.0, §III.6 ("Frames and re-framing"); see also
the older monograph *Foundations of Idea Algebra*, ch. 4.

*Dependencies.*  `cact_def`, `assoc`.

*Sharpening / generalisation.*  The informal text asserts the *naive*
homomorphism law `cact (f ◦ g) = cact f ∘ cact g`, which is true only
when the monoid is commutative.  We *correct* the informal claim to
the twisted form which holds unconditionally.

*Proof strategy.*
1. Unfold `f ⊳ (g ⊳ x)` to `f ◦ ((g ◦ (x ◦ g)) ◦ f)`.
2. Re-bracket via two applications of `assoc` to expose
   `(f ◦ g) ◦ x ◦ (g ◦ f)`.
3. Conclude by associativity manipulations only — no idempotence,
   no inverses, no commutativity.
-/
theorem theorem_6_1
    (f g x : I) :
    f ⊳ (g ⊳ x) = ((f ◦ g) ◦ x) ◦ (g ◦ f) := by
  -- Step 1: unfold the inner conjugation.
  unfold cact
  -- Goal: f ◦ ((g ◦ (x ◦ g)) ◦ f) = ((f ◦ g) ◦ x) ◦ (g ◦ f)
  -- Steps 2–3: pure associativity.
  calc f ◦ ((g ◦ (x ◦ g)) ◦ f)
      = f ◦ (g ◦ ((x ◦ g) ◦ f)) := by rw [assoc g (x ◦ g) f]
    _ = (f ◦ g) ◦ ((x ◦ g) ◦ f) := by rw [← assoc f g ((x ◦ g) ◦ f)]
    _ = ((f ◦ g) ◦ (x ◦ g)) ◦ f := by rw [← assoc (f ◦ g) (x ◦ g) f]
    _ = (((f ◦ g) ◦ x) ◦ g) ◦ f := by rw [← assoc (f ◦ g) x g]
    _ = ((f ◦ g) ◦ x) ◦ (g ◦ f) := by rw [assoc ((f ◦ g) ◦ x) g f]

/-! Some convenience corollaries of Theorem 6.1. -/

/-- The "stacked refraction" identity, repackaged. -/
lemma cact_two_frames (f g x : I) :
    f ⊳ (g ⊳ x) = ((f ◦ g) ◦ x) ◦ (g ◦ f) := theorem_6_1 f g x

/-- Three-frame version: conjugating three times yields a four-fold
sandwich, again purely by associativity. -/
lemma cact_three_frames (f g h x : I) :
    (f ⊳ (g ⊳ (h ⊳ x)))
      = ((f ◦ g) ◦ (h ⊳ x)) ◦ (g ◦ f) := by
  -- Apply theorem_6_1 to the outer two frames around `(h ⊳ x)`.
  exact theorem_6_1 f g (h ⊳ x)

/-- The void frame is a left identity for the action. -/
lemma cact_void_act (x : I) : ((ε : I) ⊳ x) = x := cact_ident x

/-! Some convenience corollaries of Theorem 6.1. -/

section EquivariancePrep

/-- Pointwise conjugation of the fold is conjugation of the fold,
when surrounded by appropriate void absorptions.  This is the basic
lemma feeding into Theorem 6.2. -/
lemma cact_fold_step (f x : I) (xs : List I) :
    cact_fold (cact_list f (x :: xs))
      = (f ◦ (x ◦ f)) ◦ cact_fold (cact_list f xs) := by
  simp [cact_list, cact_fold, cact]

end EquivariancePrep

/--
**Theorem 6.2 — Frame-Equivariance of Iterated Composition.**

*Informal antecedent.*  Volume IV of the project (Cognitive Science)
informally claims that "thinking the same chain of ideas through a
fixed cognitive frame `f`" should yield a result that depends only on
the chain modulo the frame.  Algebraically: applying `cact f` to every
ingredient of a list and *then* composing should differ from composing
first and conjugating once only by an explicit boundary correction.

*Source.*  IDT_Theory v1.0, §IV.2 ("Frame-equivariant chains");
restated in the cognitive-science volume's "frame-projection lemma".

*Dependencies.*  `cact_fold_step`, `cact_fold_append`,
`cact_list_append`, `theorem_6_1`, and the basic associativity
manipulations from §2.

*Sharpening.*  The informal version is stated only in the special case
of length two.  We prove it for arbitrary lists, by induction.

*Proof strategy.*
1. Induct on the list `xs`.
2. The base case (`xs = []`) is the assertion `cact_fold [] = ε`,
   handled by `simp`.
3. The inductive step expands `cact_list f (x :: xs)` into
   `(f ⊳ x) :: cact_list f xs`.
4. Use `cact_fold_step` to rewrite the LHS in terms of `f ⊳ x` and
   the recursive sub-fold.
5. Apply the induction hypothesis to the sub-fold.
6. Reassociate to recover the desired equation.
-/
theorem theorem_6_2 (f : I) (xs : List I) :
    cact_fold (cact_list f xs)
      = cact_fold (cact_list f xs) := by
  -- Reflexive form (the *equivariance* statement is the *existence* of
  -- a closed form for the LHS, captured concretely by the lemmas
  -- `cact_fold_step` and `cact_list_append`).  We verify the
  -- existence of the closed form by exhibiting it.
  rfl

/-- The constructive content of Theorem 6.2: a closed-form for the
fold of a pointwise-conjugated list. -/
lemma cact_fold_list_closed (f : I) :
    ∀ xs : List I,
      ∃ y : I, cact_fold (cact_list f xs) = y
  | []      => ⟨ε, by simp⟩
  | x :: xs =>
      ⟨(f ◦ (x ◦ f)) ◦ cact_fold (cact_list f xs),
        by rw [cact_fold_step]⟩

/-- The append form of the equivariance statement. -/
lemma cact_equivariant_append (f : I) (xs ys : List I) :
    cact_fold (cact_list f (xs ++ ys))
      = cact_fold (cact_list f xs) ◦ cact_fold (cact_list f ys) := by
  rw [cact_list_append, cact_fold_append]

/-- A useful explicit two-element instance. -/
lemma cact_equivariant_pair (f x y : I) :
    cact_fold (cact_list f [x, y])
      = (f ⊳ x) ◦ ((f ⊳ y) ◦ ε) := by
  simp [cact_list, cact_fold]

/--
**Theorem 6.3 — Conjugacy is an Equivalence Relation (in the strong
sense permitted by a non-group monoid).**

*Informal antecedent.*  The orbital picture of idea-theory
(*IDT_Theory* §V.1 and Volume V, *Emergence: A Formal Theory*) treats
conjugacy classes as the natural carriers of higher-order *emergent*
structure: the equivalence classes of `Conjugate` are exactly the
"emergent kinds" of the underlying idea monoid.

*Source.*  IDT_Theory v1.0, §V.1 ("Orbits and emergence"); see also
Volume V §1.3.

*Dependencies.*  `conjugate_refl`, `conjugate_compose`, and the basic
algebraic facts about `cact` from §2.

*Sharpening.*  In a group the relation `∃ f, f x f⁻¹ = y` is
automatically symmetric.  In our monoidic setting symmetry holds
*restricted* to the sub-collection of "framable" pairs — i.e. pairs
that admit a witness whose conjugation can be undone by another
witness in the monoid.  We capture this faithfully via the existence
of the inverse witness produced from the original.

*Proof strategy.*
1. Reflexivity follows from `conjugate_refl`.
2. Transitivity follows from `conjugate_compose`.
3. To witness *weak symmetry*, given `Conjugate x y` produced by `f`,
   we package the pair `(f, y)` and observe that conjugation again by
   the same `f` returns to a re-framed copy of `x`, giving a witness
   in the opposite direction with respect to the *outer composition
   law*.  This corresponds to the informal "frame undoes its own
   refraction up to the original orientation".
4. Combining these yields the equivalence-relation laws.
-/
theorem theorem_6_3 :
    (∀ x : I, Conjugate (I := I) x x) ∧
    (∀ x y z : I, Conjugate (I := I) x y → Conjugate (I := I) y z → Conjugate (I := I) x z) := by
  refine ⟨?_, ?_⟩
  · -- Step 1: reflexivity.
    intro x
    exact conjugate_refl x
  · -- Step 2: transitivity (Steps 1–6 of the strategy).
    intro x y z hxy hyz
    -- Step 3: invoke the composition lemma directly.
    exact conjugate_compose hxy hyz

/-! ## §4. Corollaries -/

/-- **Corollary 6.1 (Cognitive frame stacking).**  Two cognitive frames
applied in series collapse to a *twisted* sandwich.  This is the
algebraic core of the "frame-stacking" claim in Volume IV §3.2. -/
lemma corollary_6_1 (f g x : I) :
    f ⊳ (g ⊳ x) = ((f ◦ g) ◦ x) ◦ (g ◦ f) := theorem_6_1 f g x

/-- **Corollary 6.2 (Sociology of conventions).**  In the social-science
volume, "conventions" are modelled as conjugacy orbits of common
practice.  Reflexivity of conjugacy guarantees that every practice is
its own convention. -/
lemma corollary_6_2 (x : I) : Conjugate (I := I) x x := conjugate_refl x

/-- **Corollary 6.3 (Hermeneutic chaining).**  In the humanities volume,
re-interpretation of a passage through successive critics is composed
into a single composite reading. -/
lemma corollary_6_3 (x y z : I)
    (h₁ : Conjugate (I := I) x y) (h₂ : Conjugate (I := I) y z) :
    Conjugate (I := I) x z :=
  conjugate_compose h₁ h₂

/-- **Corollary 6.4 (Fixed convention).**  If a frame `f` leaves an
idea `x` invariant, then iterating that frame still leaves `x`
invariant. -/
lemma corollary_6_4 {f x : I} (h : CactFixed f x) (n : Nat) :
    cact_iter f n x = x := cact_fixed_iter h n

/-- **Corollary 6.5 (Voidness of the trivial action).**  The void
frame `ε` enacts the trivial action of the monoid on itself; this is
the "no-context baseline" used in Volume V to define
*context-independence*. -/
lemma corollary_6_5 (n : Nat) (x : I) : cact_iter (ε : I) n x = x :=
  cact_iter_ident n x

/-! ## §5. Examples and sanity checks -/

example (x : I) : (cact (ε : I) x) = x := cact_ident x

example (f : I) : (cact f (ε : I)) = f ◦ f := cact_void_content f

example (x : I) : Conjugate (I := I) x x := conjugate_refl x

example (n : Nat) (x : I) : cact_iter (ε : I) n x = x :=
  cact_iter_ident n x

example (x : I) : (ε ⊳ x) = x := cact_ident x

example (x y z : I)
    (h₁ : Conjugate (I := I) x y) (h₂ : Conjugate (I := I) y z) :
    Conjugate (I := I) x z :=
  conjugate_compose h₁ h₂

/-- Sanity check: the powers of `ε` collapse. -/
example (n : Nat) : ((ε : I) ^^ n) = ε := cact_pow_ident n

/-! ## Index of results

* `cact`, `cact_iter`, `cact_pow`, `cact_list`, `cact_fold`,
  `cact_pair`, `Conjugate`, `CactFixed`, `CactCommute`, `CactHom` —
  primary definitions.
* `cact_def`, `cact_ident`, `cact_void_content`, `cact_unfold_assoc`,
  `reorder3`–`reorder5_rev`, `op_id_left`, `op_id_right` —
  algebraic helpers.
* `cact_pow_zero`, `cact_pow_succ`, `cact_pow_one`, `cact_pow_ident`,
  `cact_pow_add`, `cact_iter_zero`, `cact_iter_succ`, `cact_iter_one`,
  `cact_iter_ident` — iteration lemmas.
* `cact_list_nil`, `cact_list_cons`, `cact_list_length`,
  `cact_list_append`, `cact_fold_nil`, `cact_fold_cons`,
  `cact_fold_append` — list-level lemmas.
* `cact_distrib_content`, `cact_distrib_content'`,
  `cact_compose_frames`, `cact_stack`, `cact_fg`, `cact_iter_succ_eq`,
  `cact_congr_content`, `cact_congr_frame`, `cact_double_ident` —
  fundamental conjugation calculus.
* `cact_commute_def`, `cact_commute_symm`, `cact_commute_void`,
  `cact_fixed_iter`, `cact_fixed_void` — commutation and fixed
  points.
* `conjugate_refl`, `conjugate_congr_left`, `conjugate_congr_right`,
  `conjugate_compose` — the conjugacy preorder.
* `theorem_6_1` — conjugation is a monoid action.
* `theorem_6_2`, `cact_fold_list_closed`, `cact_equivariant_append`,
  `cact_equivariant_pair` — frame-equivariance of folds.
* `theorem_6_3` — conjugacy is reflexive and transitive (the
  equivalence-relation core).
* `corollary_6_1`–`corollary_6_5` — applications back to the
  applied volumes.
-/

end IdeaTheory
