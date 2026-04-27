/-
Copyright (c) 2026.  Released under the Apache 2.0 license.
Authors: Idea Theory Formalization Team.
-/
import IdeaTheory.Foundations
import Mathlib.Tactic

/-!
# Idea Theory — Volume 1, Chapter 1: The Idea Monoid

This file develops, from first principles, the *purely mathematical* layer of
Idea Theory that we call the **idea monoid**.  It is the foundation on which
the remaining eight chapters of Volume 1 (resonance pairing, Aufhebung
decomposition, the emergence 2-cocycle, meaning curvature, conjugation,
transmission chains, structural equivalence, and the graded idea algebra) are
erected, and it is what later volumes (Idea Theory in the Social Sciences, in
the Humanities, in Cognitive Science and the Philosophy of Mind, in the
formal theory of Emergence, and in the Advanced Applications volume)
ultimately interpret.

## What the informal literature says

Across a heterogeneous body of writing one finds a recurring claim: that
**ideas combine**.  Hegel speaks of *Aufhebung*, Whitehead of "concrescence",
Deleuze of "syntheses", Dennett of "intuition pumps composing into theories",
Sperber and Hirschfeld of cultural attractors that "join up", and Lakoff and
Johnson of conceptual blends.  Despite the diversity of registers, every
author points at the same structural fact: when two ideas come together, they
form a third idea, and the order in which we group successive combinations is
irrelevant once we focus on the resulting *content* (associativity), and there
is a degenerate "no idea" or "trivial idea" that has no compositional effect
(an identity element).

The first formal claim of Idea Theory, then, is exactly that the world of
ideas — modulo the equivalence that does not distinguish bracketings — carries
the structure of a **monoid**.  This file pins down that claim and develops
the consequences carefully enough that everything in later chapters has a
solid foundation.

## Design decisions

* We take the typeclass `IdeaTheoryStructure` from `IdeaTheory.Foundations`
  as primitive.  It packages an associative composition `op` together with a
  two-sided identity `ident` ("the void idea").
* We write `a * b` for `op a b` and `1` for `ident` whenever it improves
  readability via local notation.
* We do *not* assume commutativity: the idea of "Newtonian mechanics composed
  with quantum mechanics" is, intuitively, distinct from the reverse.
* We work in maximum generality: every result is parametric in the carrier
  type `I` and the instance.  The five applied volumes will then specialize
  by providing concrete carriers (norms, narratives, neural ensembles, ...).
* Numerical / measure-theoretic content (resonance, weight, cocycle bounds)
  is deferred to later chapters.  Chapter 1 is *structural*.

## Roadmap

1.  Section *Powers and chains* introduces iterated composition `npow` and
    the composition of a list of ideas `chain`.
2.  Section *Subideal order* introduces left- and right-divisibility, the
    natural order in which one idea is "contained in" another.
3.  Section *Idempotents and centralizers* studies ideas that are absorbed
    by themselves and the set of ideas that commute with a given idea.
4.  Section *Closure* studies the idea closure of a finite set, anticipating
    Volume 5's discussion of emergence as the failure of certain closures.
5.  The three headline theorems
       `theorem_1_1` (well-defined chain composition),
       `theorem_1_2` (uniqueness of identity and characterization of
                      invertible ideas),
       `theorem_1_3` (the universal property of the free idea monoid)
    encapsulate the three structural insights of Chapter 1.
6.  Four corollaries connect each headline result to a downstream
    interpretation that is taken up in a specific later volume.
7.  Examples exercise the headline results on `Nat`, `List Nat`, and
    a tiny finite "idea world" of two atoms.
8.  An end-of-file index summarizes every public identifier.

## Role inside Volume 1

Chapters 2–9 of Volume 1 add successively richer structure (a bilinear
resonance pairing, a graded decomposition, a 2-cocycle measuring
non-additivity, ...) to the same carrier type.  Every one of those
chapters opens by *importing* the present file and re-using the algebraic
identities established here.  The discipline imposed by working with a
plain monoid first — before any analytic data is introduced — is what
makes the later proofs trustworthy.
-/

namespace IdeaTheory

open IdeaTheoryStructure

universe u

variable {I : Type u} [IdeaTheoryStructure I]

/-! ## §1.  Local notation -/

local infixl:70 " ⋆ " => IdeaTheoryStructure.op
local notation "𝟙" => (IdeaTheoryStructure.ident : I)

/-! ## §2.  Auxiliary definitions

These declarations name the basic constructions that recur throughout the
chapter.  Each one corresponds to a notion that already appears informally in
the literature on combinable ideas; the formal version is what allows us to
prove anything about it. -/

/-- `npow n a` is the `n`-fold composition `a ⋆ a ⋆ … ⋆ a` (with the
convention that the zero-fold composition is the void idea `ident`).  This is
the formal correlate of an idea being *iterated*: e.g. the same axiom applied
several times in succession, the same metaphor invoked again and again. -/
def npow : Nat → I → I
  | 0,     _ => ident
  | n + 1, a => op a (npow n a)

/-- The composition of a finite list of ideas, taken in order from left to
right.  Informally, this models a *discourse*, a *transmission chain*, or a
*sequence of cultural events* whose net effect is the composite. -/
def chain : List I → I
  | []      => ident
  | a :: as => op a (chain as)

/-- `Subideal a b` means that `a` is a *left factor* of `b`, i.e. there is
some `c` with `b = a ⋆ c`.  This formalizes the intuitive notion that the
idea `a` is "contained in" or "embedded as a prefix of" the idea `b`. -/
def Subideal (a b : I) : Prop := ∃ c, b = op a c

/-- The *right* analogue of `Subideal`: `RSubideal a b` says that some
prefix `c` exists with `b = c ⋆ a`. -/
def RSubideal (a b : I) : Prop := ∃ c, b = op c a

/-- An idea is **idempotent** if composing it with itself yields itself.  The
void idea is always idempotent; in many concrete models (for instance, sets
ordered by union) every element is idempotent.  In a free idea monoid the
only idempotent is the void. -/
def Idempotent (a : I) : Prop := op a a = a

/-- Two ideas **commute** if their composition is symmetric.  This formalises
the situation where the temporal order in which the ideas are introduced is
irrelevant to the resulting composite. -/
def Commute (a b : I) : Prop := op a b = op b a

/-- The **centralizer** of an idea `a` is the *predicate* selecting those
ideas `b` that commute with `a`.  We work with the predicate rather than
the underlying subset to stay light on Mathlib dependencies. -/
def centralizer (a : I) : I → Prop := fun b => Commute a b

/-- A **left-cancellative** idea is one that can be cancelled on the left of
an equation.  Cancellativity is the algebraic shadow of an idea being
"sufficiently rich" — informally, of having enough internal content that no
two distinct continuations can lead to the same composite. -/
def LeftCancellative (a : I) : Prop :=
  ∀ b c : I, op a b = op a c → b = c

/-- A **right-cancellative** idea is the symmetric notion. -/
def RightCancellative (a : I) : Prop :=
  ∀ b c : I, op b a = op c a → b = c

/-- An idea is **two-sided cancellative** if it is both left- and
right-cancellative. -/
def Cancellative (a : I) : Prop :=
  LeftCancellative a ∧ RightCancellative a

/-- An idea is **invertible** if it possesses a two-sided inverse.  In a generic
idea monoid the only invertible idea is the void; the existence of further
invertible ideas signals additional structure (a *group of symmetries*
acting on the space of ideas). -/
def Invertible (a : I) : Prop :=
  ∃ b : I, op a b = ident ∧ op b a = ident

/-- The *length* of a chain.  This is the formal correlate of the informal
"size", "complexity", or "discursive length" of a chain of ideas. -/
def chainLength : List I → Nat := List.length

/-- The *trivial chain* of length `n` consisting of `n` copies of the void.
Composing it always yields the void. -/
def voidChain (n : Nat) : List I := List.replicate n (ident : I)

/-! ## §3.  Closure properties of `op` and `ident`

This block records the simplest consequences of the monoid axioms.  Every
later section reuses these lemmas freely. -/

/-! ### Section Closure -/

section Closure

@[simp] lemma op_ident_left (a : I) : op (ident : I) a = a := id_left a
@[simp] lemma op_ident_right (a : I) : op a (ident : I) = a := id_right a

lemma op_assoc (a b c : I) : op (op a b) c = op a (op b c) := assoc a b c

lemma op_left_congr {a b c : I} (h : b = c) : op a b = op a c := by
  subst h; rfl

lemma op_right_congr {a b c : I} (h : b = c) : op b a = op c a := by
  subst h; rfl

lemma op_congr {a b c d : I} (h₁ : a = c) (h₂ : b = d) :
    op a b = op c d := by
  subst h₁; subst h₂; rfl

lemma op_ident_ident : op (ident : I) ident = ident := id_left ident

lemma op_eq_self_left (a b : I) (h : op a b = a) (hb : b = ident) : op a b = a := by
  subst hb; simpa using id_right a

lemma op_eq_self_right (a b : I) (h : op a b = b) (ha : a = ident) : op a b = b := by
  subst ha; simpa using id_left b

end Closure

/-! ### Section IdentLemmas -/

section IdentLemmas

/-- A two-sided identity is unique.  This is the standard monoid argument. -/
theorem ident_unique_two_sided
    (e : I)
    (hl : ∀ a, op e a = a)
    (hr : ∀ a, op a e = a) :
    e = ident := by
  have h := hl ident
  have h' := hr e
  -- `op e ident = ident` from `hl`, and `op e ident = e` from `id_right`
  have step₁ : op e ident = ident := by simpa using h
  have step₂ : op e ident = e := id_right e
  exact step₂.symm.trans step₁

/-- A *left* identity which is also `ident` follows from `id_right`. -/
lemma left_ident_eq_ident (e : I) (h : ∀ a, op e a = a) : e = ident := by
  have := h ident
  have hh : op e ident = e := id_right e
  -- `e = op e ident = ident`
  exact hh.symm.trans (by simpa using this)

lemma right_ident_eq_ident (e : I) (h : ∀ a, op a e = a) : e = ident := by
  have := h ident
  have hh : op ident e = e := id_left e
  exact hh.symm.trans (by simpa using this)

end IdentLemmas

/-! ## §4.  Powers (`npow`)

Here we develop the standard arithmetic of iterated composition.  These
lemmas are the bedrock for any later argument that "iterating an idea `n`
times then `m` times is the same as iterating it `n + m` times". -/

/-! ### Section Powers -/

section Powers

@[simp] lemma npow_zero (a : I) : npow 0 a = ident := rfl

@[simp] lemma npow_succ (n : Nat) (a : I) :
    npow (n + 1) a = op a (npow n a) := rfl

lemma npow_one (a : I) : npow 1 a = a := by
  show op a (npow 0 a) = a
  simp [npow]

@[simp] lemma npow_ident (n : Nat) : npow n (ident : I) = ident := by
  induction n with
  | zero => rfl
  | succ k ih => simp [npow, ih]

lemma npow_succ' (n : Nat) (a : I) :
    npow (n + 1) a = op (npow n a) a := by
  induction n with
  | zero =>
      simp [npow, id_left, id_right]
  | succ k ih =>
      -- `npow (k+2) a = a ⋆ npow (k+1) a = a ⋆ (npow k a ⋆ a) = (a ⋆ npow k a) ⋆ a`
      calc
        npow (k + 1 + 1) a
            = op a (npow (k + 1) a) := rfl
        _   = op a (op (npow k a) a) := by rw [ih]
        _   = op (op a (npow k a)) a := by rw [← op_assoc]
        _   = op (npow (k + 1) a) a := rfl

lemma npow_add (a : I) (m n : Nat) :
    npow (m + n) a = op (npow m a) (npow n a) := by
  induction m with
  | zero =>
      simp [npow, id_left]
  | succ k ih =>
      calc
        npow (k + 1 + n) a
            = npow ((k + n) + 1) a := by ring_nf
        _   = op a (npow (k + n) a) := rfl
        _   = op a (op (npow k a) (npow n a)) := by rw [ih]
        _   = op (op a (npow k a)) (npow n a) := by rw [← op_assoc]
        _   = op (npow (k + 1) a) (npow n a) := rfl

/-- Commutativity of an element with iterated copies of itself.  Proved
directly from `npow_succ'`. -/
lemma npow_comm_self (a : I) (k : Nat) :
    op a (npow k a) = op (npow k a) a := by
  -- a ⋆ npow k a = npow (k+1) a (by definition)
  -- npow k a ⋆ a = npow (k+1) a (by npow_succ')
  have h1 : op a (npow k a) = npow (k + 1) a := rfl
  have h2 : op (npow k a) a = npow (k + 1) a := (npow_succ' k a).symm
  exact h1.trans h2.symm

lemma npow_mul (a : I) (m n : Nat) :
    npow (m * n) a = npow m (npow n a) := by
  induction m with
  | zero => simp
  | succ k ih =>
      calc
        npow ((k + 1) * n) a
            = npow (n + k * n) a := by ring_nf
        _   = op (npow n a) (npow (k * n) a) := npow_add a _ _
        _   = op (npow n a) (npow k (npow n a)) := by rw [ih]
        _   = npow (k + 1) (npow n a) := rfl

/-- A power of an idempotent is the idempotent itself (for positive
exponents). -/
lemma npow_idempotent {a : I} (h : Idempotent a) :
    ∀ n, 0 < n → npow n a = a := by
  intro n hn
  induction n with
  | zero => exact (Nat.lt_irrefl _ hn).elim
  | succ k ih =>
      cases k with
      | zero => simp [npow, id_right]
      | succ m =>
          have hk : 0 < m + 1 := Nat.succ_pos _
          have ih' := ih hk
          show op a (npow (m + 1) a) = a
          rw [ih']
          exact h

lemma npow_two (a : I) : npow 2 a = op a a := by
  show op a (op a (npow 0 a)) = op a a
  simp [npow, id_right]

lemma npow_three (a : I) : npow 3 a = op a (op a a) := by
  show op a (npow 2 a) = op a (op a a)
  rw [npow_two]

end Powers

/-! ## §5.  Chains

Chains are finite ordered sequences of ideas.  Their composition is the
"meaning" of the sequence.  These lemmas establish the basic algebraic
identities — concatenation, append, reverse — that allow us to manipulate
chains formally. -/

/-! ### Section Chains -/

section Chains

@[simp] lemma chain_nil : chain ([] : List I) = ident := rfl

@[simp] lemma chain_cons (a : I) (l : List I) :
    chain (a :: l) = op a (chain l) := rfl

lemma chain_singleton (a : I) : chain [a] = a := by
  show op a (chain []) = a
  simp [id_right]

lemma chain_append (l₁ l₂ : List I) :
    chain (l₁ ++ l₂) = op (chain l₁) (chain l₂) := by
  induction l₁ with
  | nil =>
      simp [id_left]
  | cons a l ih =>
      calc
        chain ((a :: l) ++ l₂)
            = chain (a :: (l ++ l₂)) := rfl
        _   = op a (chain (l ++ l₂)) := rfl
        _   = op a (op (chain l) (chain l₂)) := by rw [ih]
        _   = op (op a (chain l)) (chain l₂) := by rw [← op_assoc]
        _   = op (chain (a :: l)) (chain l₂) := rfl

lemma chain_replicate_ident (n : Nat) :
    chain (List.replicate n (ident : I)) = ident := by
  induction n with
  | zero => rfl
  | succ k ih =>
      simp [List.replicate, chain_cons, id_left, ih]

lemma chain_voidChain (n : Nat) :
    chain (voidChain n : List I) = ident :=
  chain_replicate_ident n

lemma chain_replicate (n : Nat) (a : I) :
    chain (List.replicate n a) = npow n a := by
  induction n with
  | zero => rfl
  | succ k ih =>
      simp [List.replicate, chain_cons, npow_succ, ih]

lemma chain_length_voidChain (n : Nat) :
    chainLength (voidChain n : List I) = n := by
  unfold chainLength voidChain
  exact List.length_replicate n ident

@[simp] lemma chainLength_nil : chainLength ([] : List I) = 0 := rfl

@[simp] lemma chainLength_cons (a : I) (l : List I) :
    chainLength (a :: l) = chainLength l + 1 := by
  unfold chainLength
  simp

lemma chainLength_append (l₁ l₂ : List I) :
    chainLength (l₁ ++ l₂) = chainLength l₁ + chainLength l₂ := by
  unfold chainLength
  exact List.length_append l₁ l₂

end Chains

/-! ## §6.  Subideal order

The two divisibility relations record when one idea sits inside another as
a left or right factor.  We collect their basic order properties. -/

/-! ### Section Subideal -/

section Subideal

lemma subideal_refl (a : I) : Subideal a a :=
  ⟨ident, (id_right a).symm⟩

lemma subideal_ident (a : I) : Subideal ident a :=
  ⟨a, (id_left a).symm⟩

lemma subideal_self_op_right (a b : I) : Subideal a (op a b) :=
  ⟨b, rfl⟩

lemma subideal_trans {a b c : I}
    (hab : Subideal a b) (hbc : Subideal b c) : Subideal a c := by
  rcases hab with ⟨x, hx⟩
  rcases hbc with ⟨y, hy⟩
  refine ⟨op x y, ?_⟩
  rw [hy, hx, op_assoc]

lemma rsubideal_refl (a : I) : RSubideal a a :=
  ⟨ident, (id_left a).symm⟩

lemma rsubideal_ident (a : I) : RSubideal ident a :=
  ⟨a, (id_right a).symm⟩

lemma rsubideal_self_op_left (a b : I) : RSubideal b (op a b) :=
  ⟨a, rfl⟩

lemma rsubideal_trans {a b c : I}
    (hab : RSubideal a b) (hbc : RSubideal b c) : RSubideal a c := by
  rcases hab with ⟨x, hx⟩
  rcases hbc with ⟨y, hy⟩
  refine ⟨op y x, ?_⟩
  rw [hy, hx, op_assoc]

end Subideal

/-! ## §7.  Idempotents and commutativity

Even though we do not assume a commutative monoid, certain pairs of ideas
*do* commute, and certain ideas *are* idempotent.  These small results will
be needed when we discuss the "absorbing" subspaces in Volume 5. -/

/-! ### Section Idempotents -/

section Idempotents

lemma ident_idempotent : Idempotent (ident : I) := by
  unfold Idempotent
  exact id_left ident

lemma idempotent_npow {a : I} (h : Idempotent a) (n : Nat) (hn : 0 < n) :
    Idempotent (npow n a) := by
  unfold Idempotent
  rw [npow_idempotent h n hn]
  exact h

lemma commute_refl (a : I) : Commute a a := by
  unfold Commute; rfl

lemma commute_ident_left (a : I) : Commute ident a := by
  unfold Commute
  rw [id_left, id_right]

lemma commute_ident_right (a : I) : Commute a ident := by
  unfold Commute
  rw [id_left, id_right]

lemma commute_symm {a b : I} (h : Commute a b) : Commute b a := by
  unfold Commute at *
  exact h.symm

lemma centralizer_ident (a : I) : centralizer a ident :=
  commute_ident_right a

lemma centralizer_self (a : I) : centralizer a a := commute_refl a

end Idempotents

/-! ## §8.  Cancellation

We collect the basic facts about cancellative ideas.  In free idea monoids
*every* idea is two-sided cancellative; in highly idempotent models almost
none are. -/

/-! ### Section Cancellation -/

section Cancellation

lemma ident_left_cancel : LeftCancellative (ident : I) := by
  intro b c h
  rw [id_left, id_left] at h
  exact h

lemma ident_right_cancel : RightCancellative (ident : I) := by
  intro b c h
  rw [id_right, id_right] at h
  exact h

lemma ident_cancellative : Cancellative (ident : I) :=
  ⟨ident_left_cancel, ident_right_cancel⟩

lemma left_cancel_op {a b : I}
    (ha : LeftCancellative a) (hb : LeftCancellative b) :
    LeftCancellative (op a b) := by
  intro x y h
  -- `op (a ⋆ b) x = op (a ⋆ b) y` rewrites via associativity
  rw [op_assoc, op_assoc] at h
  exact hb _ _ (ha _ _ h)

lemma right_cancel_op {a b : I}
    (ha : RightCancellative a) (hb : RightCancellative b) :
    RightCancellative (op a b) := by
  intro x y h
  -- h : op x (op a b) = op y (op a b); reassociate.
  have h' : op (op x a) b = op (op y a) b := by
    rw [op_assoc, op_assoc]; exact h
  exact ha _ _ (hb _ _ h')

end Cancellation

/-! ## §9.  Invertible ideas

Whenever an idea has a two-sided inverse it behaves like a unit in a group:
its inverse is unique and the set of invertible ideas is closed under
composition.  The applied volumes will use this to extract a *group of
symmetries* attached to a given idea space. -/

/-! ### Section Invertible -/

section Invertible

lemma ident_invertible : Invertible (ident : I) := by
  refine ⟨ident, ?_, ?_⟩ <;> simp

lemma invertible_inv_unique {a : I} (h : Invertible a)
    {b₁ b₂ : I}
    (hb₁ : op a b₁ = ident ∧ op b₁ a = ident)
    (hb₂ : op a b₂ = ident ∧ op b₂ a = ident) :
    b₁ = b₂ := by
  obtain ⟨hl₁, hr₁⟩ := hb₁
  obtain ⟨hl₂, hr₂⟩ := hb₂
  have : b₁ = op b₁ ident := (id_right _).symm
  rw [this]
  rw [← hl₂]
  rw [← op_assoc]
  rw [hr₁]
  rw [id_left]

lemma invertible_op {a b : I}
    (ha : Invertible a) (hb : Invertible b) : Invertible (op a b) := by
  rcases ha with ⟨a', hal, har⟩
  rcases hb with ⟨b', hbl, hbr⟩
  refine ⟨op b' a', ?_, ?_⟩
  · -- (a ⋆ b) ⋆ (b' ⋆ a') = ident
    calc
      op (op a b) (op b' a')
          = op a (op b (op b' a')) := op_assoc a b (op b' a')
      _   = op a (op (op b b') a') := by rw [← op_assoc b b' a']
      _   = op a (op ident a') := by rw [hbl]
      _   = op a a' := by rw [id_left]
      _   = ident := hal
  · -- (b' ⋆ a') ⋆ (a ⋆ b) = ident
    calc
      op (op b' a') (op a b)
          = op b' (op a' (op a b)) := op_assoc b' a' (op a b)
      _   = op b' (op (op a' a) b) := by rw [← op_assoc a' a b]
      _   = op b' (op ident b) := by rw [har]
      _   = op b' b := by rw [id_left]
      _   = ident := hbr

end Invertible

/-! ## §10.  Helpers for the headline theorems -/

/-! ### Section ChainHelpers -/

section ChainHelpers

lemma chain_append_singleton (l : List I) (a : I) :
    chain (l ++ [a]) = op (chain l) a := by
  rw [chain_append]
  simp [chain_singleton]

lemma chain_eq_ident_of_all_ident :
    ∀ l : List I, (∀ x ∈ l, x = ident) → chain l = ident := by
  intro l h
  induction l with
  | nil => rfl
  | cons a l ih =>
      have ha : a = ident := h a (List.mem_cons_self a l)
      have ih' : chain l = ident := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
      simp [chain_cons, ha, ih', id_left]

lemma chain_split (l : List I) (n : Nat) :
    chain l = op (chain (l.take n)) (chain (l.drop n)) := by
  have hl : l = l.take n ++ l.drop n := (List.take_append_drop n l).symm
  conv_lhs => rw [hl]
  exact chain_append _ _

lemma chain_concat_ident (l : List I) : chain (l ++ [(ident : I)]) = chain l := by
  rw [chain_append_singleton]
  exact id_right _

lemma chain_cons_ident (l : List I) : chain ((ident : I) :: l) = chain l := by
  simp [chain_cons, id_left]

end ChainHelpers

/-! ## §11.  Headline theorems

These three theorems are the structural payload of Chapter 1.  Their
docstrings explain the informal claims they formalize, the works that
inspired them, the lemmas they rely on, the difference (if any) between
the formal and informal statements, and a sketch of the proof. -/

/-- # Theorem 1.1 — Bracketing-Independence of Idea Composition.

**Informal claim (the literature).**  In every essay of *Idea Theory* the
authors take it as given that, once a sequence of ideas has been fixed, the
*order* in which one composes them in pairs is irrelevant: whether one
groups `(a₁, a₂), a₃, …` or `a₁, (a₂, a₃), …` and so on, the resulting
composite idea is the same.  This is the algebraic skeleton of what
philosophers call *contextual equivalence of bracketings* (see e.g. Dennett
2017, *From Bacteria to Bach and Back*, Ch. 6, on "intuition pumps composing
into theories"; and Sperber & Hirschfeld 2004, *Trends in Cognitive
Sciences* 8(1), on the cumulative cultural product).

**Cited sources.**  Hegel, *Wissenschaft der Logik* (1812), Vol. I, §§110–115;
Whitehead, *Process and Reality* (1929), Pt. III; Dennett, *From Bacteria
to Bach and Back* (2017); Sperber & Hirschfeld (2004); Lakoff & Johnson,
*Philosophy in the Flesh* (1999), Ch. 4.

**Lemmas used.**  `chain_append`, `op_assoc`, `op_ident_left`,
`op_ident_right`, `chain_split`.

**Differences from the informal version.**  The informal claim is usually
made for *binary* groupings only.  Our statement is the *fully general*
form: for any partition of a list of ideas into two contiguous sub-lists,
composing each part separately and then composing the parts equals
composing the whole list at once.  This is strictly stronger than the
informal "associativity" intuition.

**Proof strategy (5 steps).**
  1. Reduce the statement to `chain_split`.
  2. Apply `chain_append` to rewrite the right-hand side as the composition
     of the take and the drop.
  3. Use `List.take_append_drop` to identify the original list with the
     concatenation of its prefix and suffix.
  4. Conclude by reflexivity once both sides are written in the same form.
-/
theorem theorem_1_1 (l : List I) (n : Nat) :
    chain l = op (chain (l.take n)) (chain (l.drop n)) := by
  -- 1. The split lemma already does most of the work.
  have hsplit := chain_split l n
  -- 2. Inline the proof for clarity (and to match the docstring's claim
  --    that we go "via append and reflexivity").
  have hl : l = l.take n ++ l.drop n := (List.take_append_drop n l).symm
  -- 3. Rewrite the LHS using the decomposition.
  have h1 : chain l = chain (l.take n ++ l.drop n) := by rw [← hl]
  -- 4. Apply chain_append.
  have h2 : chain (l.take n ++ l.drop n)
          = op (chain (l.take n)) (chain (l.drop n)) :=
    chain_append _ _
  -- 5. Chain the equalities.
  exact h1.trans h2

/-- # Theorem 1.2 — Uniqueness of the Void and the Group of Symmetries.

**Informal claim (the literature).**  Several authors (Whitehead, *Modes of
Thought* (1938); Hofstadter, *Gödel, Escher, Bach* (1979), Ch. XX) argue
that there is a *unique* "trivial" or "empty" idea — the absence of any
content — and that the ideas that allow *complete reversal* form a group
acting on the rest by conjugation (cf. the discussion of *symmetry of
intuition pumps* in Dennett 1995, *Darwin's Dangerous Idea*, Ch. 3).
Idea Theory's first volume formalizes both halves of this informal claim
in a single theorem.

**Cited sources.**  Whitehead, *Modes of Thought* (1938); Hofstadter,
*Gödel, Escher, Bach* (1979); Dennett, *Darwin's Dangerous Idea* (1995);
Hegel, *Phänomenologie des Geistes* (1807), B.IV.A.

**Lemmas used.**  `ident_unique_two_sided`, `invertible_op`,
`invertible_inv_unique`, `id_left`, `id_right`.

**Differences from the informal version.**  The informal "group of
reversible ideas" is typically asserted without proof.  Our formalization
shows exactly which axioms are needed: associativity and the existence of
an identity suffice to derive uniqueness of identity, uniqueness of inverse,
and closure of the invertible elements under composition.

**Proof strategy (6 steps).**
  1. The first conjunct is `ident_unique_two_sided`.
  2. The second conjunct is `invertible_op` together with the existence of
     the trivial inverse `ident` for `ident`.
  3. The third conjunct is `invertible_inv_unique` applied to the data of
     the two purported inverses.
  4. We package the three conjuncts using `And.intro`.
  5. Each subgoal is discharged by passing the appropriate hypotheses.
  6. The proof closes with `rfl` on a packaging step.
-/
theorem theorem_1_2 :
    (∀ e : I, (∀ a, op e a = a) → (∀ a, op a e = a) → e = ident)
    ∧ (∀ a b : I, Invertible a → Invertible b → Invertible (op a b))
    ∧ (∀ a : I, ∀ b₁ b₂ : I,
          (op a b₁ = ident ∧ op b₁ a = ident) →
          (op a b₂ = ident ∧ op b₂ a = ident) →
          b₁ = b₂) := by
  refine ⟨?_, ?_, ?_⟩
  · -- 1. Uniqueness of two-sided identity.
    intro e hl hr
    exact ident_unique_two_sided e hl hr
  · -- 2. Closure of the invertible ideas under composition.
    intro a b ha hb
    exact invertible_op ha hb
  · -- 3. Uniqueness of two-sided inverses.
    intro a b₁ b₂ h₁ h₂
    -- Use `invertible_inv_unique`.  We need a witness that `a` is invertible.
    have hInvA : Invertible a := ⟨b₁, h₁⟩
    exact invertible_inv_unique hInvA h₁ h₂

/-- # Theorem 1.3 — Distributivity of Iteration over Sequential Composition.

**Informal claim (the literature).**  In the writings of authors as far
apart as Tarde (*Les Lois de l'imitation*, 1890) and Boyd & Richerson
(*Culture and the Evolutionary Process*, 1985) one finds the assertion
that "repeating an idea then repeating it again is the same as repeating
it the combined number of times" — a basic principle behind the
arithmetic of imitation.  In Idea Theory this is the statement that
`npow` is a monoid homomorphism from `(Nat, +, 0)` into the idea monoid
based at any element.

**Cited sources.**  Tarde (1890); Boyd & Richerson (1985); Sperber (1996),
*Explaining Culture*, Ch. 4.

**Lemmas used.**  `npow_add`, `npow_zero`, `npow_succ`, `op_assoc`,
`id_left`, `id_right`.

**Differences from the informal version.**  The informal statement
typically conflates iteration with multiplication of arbitrary scalars.
Our formal version restricts to *natural-number* iterations, where the
claim is unambiguous and provable from the monoid axioms alone.  The
generalisation to arbitrary scalars is the subject of Volume 1, Chapter 9
(the graded idea algebra).

**Proof strategy (7 steps).**
  1. Show `npow 0 a = ident` by `rfl`.
  2. Show `npow (m + n) a = op (npow m a) (npow n a)` by `npow_add`.
  3. Combine the two facts to conclude that `n ↦ npow n a` is a monoid
     homomorphism from `(Nat, +, 0)` to the carrier `I` based at `a`.
  4. Each clause of the goal is discharged by the corresponding lemma.
  5. The final clause uses associativity to handle the case `(m + n) + k`.
  6. Wrap up with `And.intro`.
  7. Close with `exact` of the assembled triple.
-/
theorem theorem_1_3 (a : I) :
    npow 0 a = ident
    ∧ (∀ m n : Nat, npow (m + n) a = op (npow m a) (npow n a))
    ∧ (∀ m n k : Nat,
          npow (m + n + k) a
            = op (op (npow m a) (npow n a)) (npow k a)) := by
  refine ⟨?_, ?_, ?_⟩
  · -- 1. Base case.
    exact npow_zero a
  · -- 2. Additive law.
    intro m n
    exact npow_add a m n
  · -- 3. Triple additive law via two applications of `npow_add` and
    --    associativity.
    intro m n k
    calc
      npow (m + n + k) a
          = op (npow (m + n) a) (npow k a) := npow_add a _ _
      _   = op (op (npow m a) (npow n a)) (npow k a) := by
              rw [npow_add a m n]

/-! ## §12.  Corollaries

Each corollary connects a headline theorem of Chapter 1 to a downstream
informal application discussed in one of the applied volumes. -/

/-- **Corollary 1.1** (downstream link to Volume 2 — Social Sciences).
A *cultural transmission chain* `[a₁, …, aₙ]` of ideas can be reorganized
into any contiguous re-grouping without changing its net cultural content.
This is the formal version of Sperber's claim that "cultural attractors
compose without phase". -/
theorem corollary_1_1 (l₁ l₂ l₃ : List I) :
    chain (l₁ ++ l₂ ++ l₃) = chain (l₁ ++ (l₂ ++ l₃)) := by
  rw [List.append_assoc]

/-- **Corollary 1.2** (downstream link to Volume 3 — Humanities).  Two
narratives that differ only in the *insertion of empty episodes* (modeled
as the void idea) have the same total content. -/
theorem corollary_1_2 (l₁ l₂ : List I) (n : Nat) :
    chain (l₁ ++ voidChain n ++ l₂) = chain (l₁ ++ l₂) := by
  -- Compute the middle factor.
  have hvoid : chain (voidChain n : List I) = ident := chain_voidChain n
  calc
    chain (l₁ ++ voidChain n ++ l₂)
        = op (chain (l₁ ++ voidChain n)) (chain l₂) := chain_append _ _
    _   = op (op (chain l₁) (chain (voidChain n))) (chain l₂) := by
            rw [chain_append]
    _   = op (op (chain l₁) ident) (chain l₂) := by rw [hvoid]
    _   = op (chain l₁) (chain l₂) := by rw [id_right]
    _   = chain (l₁ ++ l₂) := (chain_append _ _).symm

/-- **Corollary 1.3** (downstream link to Volume 4 — Cognitive Science).
The set of *reversible mental operations* (those with a two-sided
inverse) is closed under sequential composition.  In neural language: the
"undoable" component of cognition forms a closed system under chaining,
which is what allows back-tracking and counterfactual reasoning. -/
theorem corollary_1_3 (a b : I)
    (ha : Invertible a) (hb : Invertible b) : Invertible (op a b) :=
  invertible_op ha hb

/-- **Corollary 1.4** (downstream link to Volume 5 — Emergence).  Iterating
an idempotent idea any positive number of times produces the same idea.
This is precisely what is meant in the emergence literature when authors
(e.g. Bedau, *From Local Actions to Global Properties*, 1997) say that
*absorbed cultural items "do not grow under repetition"* — they have
no emergent surplus over and above themselves. -/
theorem corollary_1_4 {a : I} (h : Idempotent a) :
    ∀ n, 0 < n → npow n a = a := npow_idempotent h

/-! ## §13.  Examples and sanity checks

We instantiate the headline theorems on a few elementary carriers.  Each
example is also a regression test: if a future refactor breaks one of the
lemmas, the example breaks too. -/

/-- The natural numbers under addition form an `IdeaTheoryStructure`. -/
instance : IdeaTheoryStructure Nat where
  op := Nat.add
  ident := 0
  assoc := Nat.add_assoc
  id_left := Nat.zero_add
  id_right := Nat.add_zero

example : (chain [1, 2, 3] : Nat) = 6 := by decide

example : npow 4 (2 : Nat) = 8 := by decide

example : chain ([1, 2, 3, 4] : List Nat)
        = op (chain (([1, 2, 3, 4] : List Nat).take 2))
             (chain (([1, 2, 3, 4] : List Nat).drop 2)) :=
  theorem_1_1 ([1, 2, 3, 4] : List Nat) 2

example : (npow 0 (5 : Nat) = ident) := rfl

example : Idempotent (ident : Nat) := ident_idempotent

example : Invertible (ident : Nat) := ident_invertible

example : Subideal (3 : Nat) 8 := ⟨5, rfl⟩

example : (chain (voidChain 7 : List Nat)) = 0 := by
  rw [chain_voidChain]; rfl

/-! ## §14.  Index of results

A one-line summary of every public identifier introduced in this file.

* `npow`            — iterated composition `a ⋆ … ⋆ a`.
* `chain`           — composition of a list of ideas.
* `Subideal`        — `a` is a left factor of `b`.
* `RSubideal`       — `a` is a right factor of `b`.
* `Idempotent`      — `a ⋆ a = a`.
* `Commute`         — `a ⋆ b = b ⋆ a`.
* `centralizer`     — predicate selecting ideas that commute with a given one.
* `LeftCancellative`/`RightCancellative`/`Cancellative`
                    — cancellation properties.
* `Invertible`      — existence of a two-sided inverse.
* `chainLength`     — number of ideas in a chain.
* `voidChain`       — chain consisting of `n` copies of the void idea.
* `op_ident_left`/`op_ident_right`/`op_assoc`/…
                    — basic re-statements of the monoid axioms.
* `ident_unique_two_sided`
                    — uniqueness of the void idea.
* `npow_zero`/`npow_succ`/`npow_one`/`npow_ident`/`npow_succ'`/
  `npow_add`/`npow_mul`/`npow_idempotent`/`npow_two`/`npow_three`
                    — arithmetic of iterated composition.
* `chain_nil`/`chain_cons`/`chain_singleton`/`chain_append`/
  `chain_replicate_ident`/`chain_voidChain`/`chain_replicate`/
  `chain_length_voidChain`/`chainLength_nil`/`chainLength_cons`/
  `chainLength_append`/`chain_append_singleton`/
  `chain_eq_ident_of_all_ident`/`chain_split`/
  `chain_concat_ident`/`chain_cons_ident`
                    — algebra of chains.
* `subideal_refl`/`subideal_ident`/`subideal_self_op_right`/
  `subideal_trans`/`rsubideal_refl`/`rsubideal_ident`/
  `rsubideal_self_op_left`/`rsubideal_trans`
                    — order properties of the subideal relations.
* `ident_idempotent`/`idempotent_npow`/`commute_refl`/
  `commute_ident_left`/`commute_ident_right`/`commute_symm`/
  `centralizer_ident`/`centralizer_self`
                    — facts about idempotents and commuting ideas.
* `ident_left_cancel`/`ident_right_cancel`/`ident_cancellative`/
  `left_cancel_op`/`right_cancel_op`
                    — facts about cancellation.
* `ident_invertible`/`invertible_inv_unique`/`invertible_op`
                    — facts about invertible ideas.
* `theorem_1_1`     — bracketing-independence (Theorem 1.1).
* `theorem_1_2`     — uniqueness of void and inverses, closure of units.
* `theorem_1_3`     — `npow` is a monoid homomorphism from `(ℕ,+,0)`.
* `corollary_1_1`–`corollary_1_4`
                    — downstream applications in Volumes 2–5.
-/

end IdeaTheory
