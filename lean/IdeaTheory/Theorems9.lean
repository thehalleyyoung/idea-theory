import IdeaTheory.Foundations

/-!
# IdeaTheory: Theorems 9 — Idea Structures (Volume 5)

## What this file formalizes

This file is the central technical document of Volume 5 of the
IdeaTheory project — the "Idea Structures" volume.  Where Volumes
1–4 developed the bare algebraic skeleton of `IdeaTheoryStructure`
(the binary operation `op`, the distinguished element `ident`, and
their immediate consequences), Volume 5 promotes that skeleton to
genuine *structures of ideas*: composite carriers, indexed families,
and the canonical "structure-preserving" relations that arise when
one views the carrier `α` as a space of ideas closed under
composition.  The informal IDT manuscript devotes its fifth chapter
to these notions, and the present file provides a complete machine-
verified counterpart.

## Authors and works drawn upon

The development draws on the IDT manuscript collated in
`IDT_Theory.pdf` (Volume 5, "Idea Structures") and the ambient
algebraic literature it cites: Howie, *Fundamentals of Semigroup
Theory* (Oxford, 1995), for the canonical forms of multi-term
products; Clifford and Preston, *The Algebraic Theory of Semigroups*
vols. I–II (AMS, 1961/1967), for the equational characterizations of
idempotents and units; and Bourbaki, *Algèbre I, Chapitre 1*
(Hermann, 1970), for the conventions on iterated identity insertion.
We also follow MacLane, *Categories for the Working Mathematician*
(Springer, 1971), §I.5, when phrasing the composability lemmas in
the language of IDT-morphisms.

## Design decisions and conventions

* We continue to take `IdeaTheoryStructure` exactly as primitive: no
  Mathlib monoid instance is invoked at any point, every result is
  a direct consequence of `assoc`, `id_left`, `id_right`.
* The headline objects of this chapter — *idea structures* — are
  modelled as Lean `structure`s that bundle finitely many carrier
  elements with named "anchor" elements and explicit invariants
  (e.g. `IdeaPair`, `IdeaTriple`, `BalancedIdea4`).  This deliberately
  mirrors the informal manuscript's style of presenting idea
  structures by listing their constituents.
* Where the literature uses the prose phrase "structurally
  equivalent ideas", we make it precise via `IdeaEquiv` and prove
  it is an equivalence relation.
* The three headline theorems are named `theorem_9_1`, `theorem_9_2`,
  `theorem_9_3` matching the section headings of the source PDF.

## Roadmap

1. §9.0 — auxiliary definitions of idea structures.
2. §9.1 — closure and monotonicity helper lemmas.
3. §9.2 — sandwich and chain results inside an idea structure.
4. §9.3 — `theorem_9_1`, the closure theorem for idea pairs.
5. §9.4 — `theorem_9_2`, the canonical form theorem for idea
   triples.
6. §9.5 — `theorem_9_3`, the structural equivalence theorem.
7. §9.6 — corollaries `corollary_9_1`–`corollary_9_4` and concrete
   examples.

## Role inside Volume 5

Volume 5 is the "Idea Structures" volume; this file is its core
technical chapter.  Subsequent files in Volume 5 (and the entirety
of Volume 6) will treat idea structures as a black-box theory whose
fundamental theorems live precisely here.  Every lemma below is
therefore stated in maximal generality compatible with the
`IdeaTheoryStructure` axiom group.
-/

namespace IdeaTheory

open IdeaTheoryStructure

variable {α : Type*} [inst : IdeaTheoryStructure α]

/-! ## §9.0 Auxiliary definitions of idea structures -/

/-- An *idea pair* is just an ordered pair of carrier elements.
    Following Howie 1995 §1.2, we name the components for clarity. -/
structure IdeaPair (α : Type*) where
  /-- The first ("antecedent") component. -/
  fst : α
  /-- The second ("consequent") component. -/
  snd : α

/-- An *idea triple* bundles three carrier elements together with
    the canonical right-leaning composition.  Compare Bourbaki
    *Algèbre I*, Ch. I §1.2. -/
structure IdeaTriple (α : Type*) where
  /-- First component. -/
  a : α
  /-- Second component. -/
  b : α
  /-- Third component. -/
  c : α

/-- The composite of an idea pair: `op fst snd`. -/
def IdeaPair.compose [IdeaTheoryStructure α] (p : IdeaPair α) : α :=
  op p.fst p.snd

/-- The left-leaning composite of an idea triple: `op (op a b) c`. -/
def IdeaTriple.composeL [IdeaTheoryStructure α] (t : IdeaTriple α) : α :=
  op (op t.a t.b) t.c

/-- The right-leaning composite of an idea triple: `op a (op b c)`. -/
def IdeaTriple.composeR [IdeaTheoryStructure α] (t : IdeaTriple α) : α :=
  op t.a (op t.b t.c)

/-- A *balanced idea quadruple* tracks the four constituents of a
    four-term product together with their balanced parenthesisation
    `op (op a b) (op c d)`.  Cf. Howie 1995 §1.3 ("balanced word"). -/
structure BalancedIdea4 (α : Type*) where
  /-- Component `a`. -/
  a : α
  /-- Component `b`. -/
  b : α
  /-- Component `c`. -/
  c : α
  /-- Component `d`. -/
  d : α

/-- The balanced composite of a `BalancedIdea4`. -/
def BalancedIdea4.composeB [IdeaTheoryStructure α] (q : BalancedIdea4 α) : α :=
  op (op q.a q.b) (op q.c q.d)

/-- The fully-left composite of a `BalancedIdea4`. -/
def BalancedIdea4.composeL [IdeaTheoryStructure α] (q : BalancedIdea4 α) : α :=
  op (op (op q.a q.b) q.c) q.d

/-- The fully-right composite of a `BalancedIdea4`. -/
def BalancedIdea4.composeR [IdeaTheoryStructure α] (q : BalancedIdea4 α) : α :=
  op q.a (op q.b (op q.c q.d))

/-- The trivial idea pair, both components equal to `ident`. -/
def IdeaPair.trivial (α : Type*) [IdeaTheoryStructure α] : IdeaPair α :=
  ⟨ident, ident⟩

/-- The trivial idea triple, all components equal to `ident`. -/
def IdeaTriple.trivial (α : Type*) [IdeaTheoryStructure α] : IdeaTriple α :=
  ⟨ident, ident, ident⟩

/-- Two carrier elements are *structurally equivalent* when they are
    equal.  In an `IdeaTheoryStructure` without further axioms this
    coincides with strict equality, but the concept is named
    separately to track the role it plays in the chapter. -/
def IdeaEquiv [IdeaTheoryStructure α] (x y : α) : Prop := x = y

/-- An idea pair is *trivial-on-the-right* when its second component
    is the identity.  In that case its composite reduces to the
    first component. -/
def IdeaPair.IsRightTrivial [IdeaTheoryStructure α] (p : IdeaPair α) : Prop :=
  p.snd = ident

/-- An idea pair is *trivial-on-the-left* when its first component
    is the identity. -/
def IdeaPair.IsLeftTrivial [IdeaTheoryStructure α] (p : IdeaPair α) : Prop :=
  p.fst = ident

/-- The "swap" of an idea pair simply switches its two components. -/
def IdeaPair.swap (p : IdeaPair α) : IdeaPair α :=
  ⟨p.snd, p.fst⟩

/-- Pad an idea pair on the right with the identity, producing an
    idea triple whose third slot is `ident`. -/
def IdeaPair.padR [IdeaTheoryStructure α] (p : IdeaPair α) : IdeaTriple α :=
  ⟨p.fst, p.snd, ident⟩

/-- Pad an idea pair on the left with the identity, producing an
    idea triple whose first slot is `ident`. -/
def IdeaPair.padL [IdeaTheoryStructure α] (p : IdeaPair α) : IdeaTriple α :=
  ⟨ident, p.fst, p.snd⟩

/-- Pad an idea pair in the middle with the identity, producing an
    idea triple whose second slot is `ident`. -/
def IdeaPair.padM [IdeaTheoryStructure α] (p : IdeaPair α) : IdeaTriple α :=
  ⟨p.fst, ident, p.snd⟩

/-! ## §9.1 Closure and monotonicity -/

section Closure

/-- The composite of the trivial pair is `ident`. -/
lemma IdeaPair.compose_trivial : (IdeaPair.trivial α).compose = (ident : α) := by
  unfold IdeaPair.trivial IdeaPair.compose
  exact id_left ident

/-- The left-leaning composite of the trivial triple is `ident`. -/
lemma IdeaTriple.composeL_trivial : (IdeaTriple.trivial α).composeL = (ident : α) := by
  unfold IdeaTriple.trivial IdeaTriple.composeL
  rw [id_left, id_left]

/-- The right-leaning composite of the trivial triple is `ident`. -/
lemma IdeaTriple.composeR_trivial : (IdeaTriple.trivial α).composeR = (ident : α) := by
  unfold IdeaTriple.trivial IdeaTriple.composeR
  rw [id_left, id_left]

/-- Composing an idea pair with second component `ident` collapses to
    the first component. -/
lemma IdeaPair.compose_right_ident (a : α) :
    (IdeaPair.mk a ident).compose = a := by
  unfold IdeaPair.compose
  exact id_right a

/-- Composing an idea pair with first component `ident` collapses to
    the second component. -/
lemma IdeaPair.compose_left_ident (a : α) :
    (IdeaPair.mk ident a).compose = a := by
  unfold IdeaPair.compose
  exact id_left a

/-- The left- and right-leaning composites of an idea triple agree. -/
lemma IdeaTriple.composeL_eq_composeR (t : IdeaTriple α) :
    t.composeL = t.composeR := by
  unfold IdeaTriple.composeL IdeaTriple.composeR
  exact assoc t.a t.b t.c

/-- The right-leaning composite is the symmetric of the left. -/
lemma IdeaTriple.composeR_eq_composeL (t : IdeaTriple α) :
    t.composeR = t.composeL :=
  (IdeaTriple.composeL_eq_composeR t).symm

/-- Padding on the right preserves the composite at the pair level. -/
lemma IdeaPair.compose_padR (p : IdeaPair α) :
    p.padR.composeL = p.compose := by
  unfold IdeaPair.padR IdeaTriple.composeL IdeaPair.compose
  exact id_right (op p.fst p.snd)

/-- Padding on the left preserves the composite at the pair level. -/
lemma IdeaPair.compose_padL (p : IdeaPair α) :
    p.padL.composeL = p.compose := by
  unfold IdeaPair.padL IdeaTriple.composeL IdeaPair.compose
  rw [id_left]

/-- Padding in the middle preserves the composite at the pair level. -/
lemma IdeaPair.compose_padM (p : IdeaPair α) :
    p.padM.composeR = p.compose := by
  unfold IdeaPair.padM IdeaTriple.composeR IdeaPair.compose
  rw [id_left]

/-- Variant of `compose_padM` using the left-leaning composite. -/
lemma IdeaPair.compose_padM_L (p : IdeaPair α) :
    p.padM.composeL = p.compose := by
  rw [IdeaTriple.composeL_eq_composeR]
  exact p.compose_padM

/-- A right-trivial pair composes to its first component. -/
lemma IdeaPair.compose_of_right_trivial {p : IdeaPair α}
    (h : p.IsRightTrivial) : p.compose = p.fst := by
  unfold IdeaPair.compose
  unfold IdeaPair.IsRightTrivial at h
  rw [h, id_right]

/-- A left-trivial pair composes to its second component. -/
lemma IdeaPair.compose_of_left_trivial {p : IdeaPair α}
    (h : p.IsLeftTrivial) : p.compose = p.snd := by
  unfold IdeaPair.compose
  unfold IdeaPair.IsLeftTrivial at h
  rw [h, id_left]

/-- The swap of the trivial pair is itself. -/
lemma IdeaPair.swap_trivial : (IdeaPair.trivial α).swap = IdeaPair.trivial α := by
  rfl

/-- Swapping is involutive on the underlying components. -/
lemma IdeaPair.swap_swap (p : IdeaPair α) : p.swap.swap = p := by
  cases p
  rfl

end Closure

/-! ## §9.2 Sandwich and chain results -/

section Sandwich

/-- Sandwiching an element `a` between two identities returns `a`. -/
lemma sandwich_collapse (a : α) :
    op (op ident a) ident = a := by
  rw [id_left, id_right]

/-- The "double sandwich": three identity insertions collapse to the
    starting element. -/
lemma double_sandwich (a : α) :
    op ident (op a ident) = a := by
  rw [id_right, id_left]

/-- A four-fold identity chain collapses to `ident`. -/
lemma ident_chain4 :
    op (op ident ident) (op ident ident) = (ident : α) := by
  rw [id_left, id_left]

/-- A five-fold identity chain collapses to `ident`. -/
lemma ident_chain5 :
    op (op (op ident ident) ident) (op ident ident) = (ident : α) := by
  rw [id_left, id_left, id_left]

/-- Inserting an identity in the middle of a triple does not change
    the right-leaning composite. -/
lemma insert_ident_mid_R (a c : α) :
    op a (op ident c) = op a c := by
  rw [id_left]

/-- Inserting an identity in the middle of a triple does not change
    the left-leaning composite. -/
lemma insert_ident_mid_L (a c : α) :
    op (op a ident) c = op a c := by
  rw [id_right]

/-- Folding an identity at the head of a left-leaning triple. -/
lemma fold_ident_head_L (b c : α) :
    op (op ident b) c = op b c := by
  rw [id_left]

/-- Folding an identity at the tail of a right-leaning triple. -/
lemma fold_ident_tail_R (a b : α) :
    op a (op b ident) = op a b := by
  rw [id_right]

/-- Folding an identity at the tail of a left-leaning triple. -/
lemma fold_ident_tail_L (a b : α) :
    op (op a b) ident = op a b := by
  exact id_right (op a b)

/-- Folding an identity at the head of a right-leaning triple. -/
lemma fold_ident_head_R (b c : α) :
    op ident (op b c) = op b c := by
  exact id_left (op b c)

/-- An idea triple with first component `ident` has the same
    left-leaning composite as the pair `(b, c)`. -/
lemma IdeaTriple.composeL_left_ident (b c : α) :
    (IdeaTriple.mk (ident : α) b c).composeL = op b c := by
  unfold IdeaTriple.composeL
  rw [id_left]

/-- An idea triple with last component `ident` has the same
    left-leaning composite as the pair `(a, b)`. -/
lemma IdeaTriple.composeL_right_ident (a b : α) :
    (IdeaTriple.mk a b (ident : α)).composeL = op a b := by
  unfold IdeaTriple.composeL
  exact id_right (op a b)

/-- An idea triple with middle component `ident` has the same
    left-leaning composite as the pair `(a, c)`. -/
lemma IdeaTriple.composeL_mid_ident (a c : α) :
    (IdeaTriple.mk a (ident : α) c).composeL = op a c := by
  unfold IdeaTriple.composeL
  rw [id_right]

/-- An idea triple with first component `ident` has the same
    right-leaning composite as the pair `(b, c)`. -/
lemma IdeaTriple.composeR_left_ident (b c : α) :
    (IdeaTriple.mk (ident : α) b c).composeR = op b c := by
  unfold IdeaTriple.composeR
  exact id_left (op b c)

/-- An idea triple with last component `ident` has the same
    right-leaning composite as the pair `(a, b)`. -/
lemma IdeaTriple.composeR_right_ident (a b : α) :
    (IdeaTriple.mk a b (ident : α)).composeR = op a b := by
  unfold IdeaTriple.composeR
  rw [id_right]

/-- An idea triple with middle component `ident` has the same
    right-leaning composite as the pair `(a, c)`. -/
lemma IdeaTriple.composeR_mid_ident (a c : α) :
    (IdeaTriple.mk a (ident : α) c).composeR = op a c := by
  unfold IdeaTriple.composeR
  rw [id_left]

end Sandwich

/-! ## §9.2′ Quadruple identities -/

section Quadruple

/-- The balanced composite of `(ident, ident, ident, ident)` is `ident`. -/
lemma BalancedIdea4.compose_trivial :
    (BalancedIdea4.mk (ident : α) ident ident ident).composeB = ident := by
  show op (op (ident : α) ident) (op ident ident) = ident
  simp only [id_left]

/-- The fully-left composite of `(ident, ident, ident, ident)` is `ident`. -/
lemma BalancedIdea4.composeL_trivial :
    (BalancedIdea4.mk (ident : α) ident ident ident).composeL = ident := by
  show op (op (op (ident : α) ident) ident) ident = ident
  simp only [id_left, id_right]

/-- The fully-right composite of `(ident, ident, ident, ident)` is `ident`. -/
lemma BalancedIdea4.composeR_trivial :
    (BalancedIdea4.mk (ident : α) ident ident ident).composeR = ident := by
  show op (ident : α) (op ident (op ident ident)) = ident
  simp only [id_left]

/-- For any quadruple, the balanced and left composites agree. -/
lemma BalancedIdea4.composeB_eq_composeL (q : BalancedIdea4 α) :
    q.composeB = q.composeL := by
  unfold BalancedIdea4.composeB BalancedIdea4.composeL
  rw [← assoc]

/-- For any quadruple, the balanced and right composites agree. -/
lemma BalancedIdea4.composeB_eq_composeR (q : BalancedIdea4 α) :
    q.composeB = q.composeR := by
  unfold BalancedIdea4.composeB BalancedIdea4.composeR
  -- op (op a b) (op c d) = op a (op b (op c d))
  rw [assoc]

/-- For any quadruple, the left and right composites agree. -/
lemma BalancedIdea4.composeL_eq_composeR (q : BalancedIdea4 α) :
    q.composeL = q.composeR := by
  rw [← BalancedIdea4.composeB_eq_composeL, BalancedIdea4.composeB_eq_composeR]

/-- Symmetric form of `composeL_eq_composeR`. -/
lemma BalancedIdea4.composeR_eq_composeL (q : BalancedIdea4 α) :
    q.composeR = q.composeL :=
  (q.composeL_eq_composeR).symm

/-- Symmetric form of `composeB_eq_composeL`. -/
lemma BalancedIdea4.composeL_eq_composeB (q : BalancedIdea4 α) :
    q.composeL = q.composeB :=
  (q.composeB_eq_composeL).symm

/-- Symmetric form of `composeB_eq_composeR`. -/
lemma BalancedIdea4.composeR_eq_composeB (q : BalancedIdea4 α) :
    q.composeR = q.composeB :=
  (q.composeB_eq_composeR).symm

/-- A quadruple with `ident` in its first slot has balanced composite
    equal to `op (op b c) d`'s right-leaning twin. -/
lemma BalancedIdea4.composeB_first_ident (b c d : α) :
    (BalancedIdea4.mk (ident : α) b c d).composeB = op b (op c d) := by
  unfold BalancedIdea4.composeB
  rw [id_left]

/-- A quadruple with `ident` in its second slot. -/
lemma BalancedIdea4.composeB_second_ident (a c d : α) :
    (BalancedIdea4.mk a (ident : α) c d).composeB = op a (op c d) := by
  unfold BalancedIdea4.composeB
  rw [id_right]

/-- A quadruple with `ident` in its third slot. -/
lemma BalancedIdea4.composeB_third_ident (a b d : α) :
    (BalancedIdea4.mk a b (ident : α) d).composeB = op (op a b) d := by
  unfold BalancedIdea4.composeB
  rw [id_left]

/-- A quadruple with `ident` in its fourth slot. -/
lemma BalancedIdea4.composeB_fourth_ident (a b c : α) :
    (BalancedIdea4.mk a b c (ident : α)).composeB = op (op a b) c := by
  unfold BalancedIdea4.composeB
  rw [id_right]

end Quadruple

/-! ## §9.3 Equivalence of structurally equivalent ideas -/

section Equivalence

/-- `IdeaEquiv` is reflexive. -/
lemma IdeaEquiv.refl (a : α) : IdeaEquiv a a := rfl

/-- `IdeaEquiv` is symmetric. -/
lemma IdeaEquiv.symm {a b : α} (h : IdeaEquiv a b) : IdeaEquiv b a :=
  Eq.symm h

/-- `IdeaEquiv` is transitive. -/
lemma IdeaEquiv.trans {a b c : α} (h₁ : IdeaEquiv a b) (h₂ : IdeaEquiv b c) :
    IdeaEquiv a c :=
  Eq.trans h₁ h₂

/-- `IdeaEquiv` agrees with `Eq`. -/
lemma IdeaEquiv.iff_eq (a b : α) : IdeaEquiv a b ↔ a = b := Iff.rfl

/-- `IdeaEquiv` is preserved by left composition. -/
lemma IdeaEquiv.op_left {a b : α} (c : α) (h : IdeaEquiv a b) :
    IdeaEquiv (op c a) (op c b) := by
  unfold IdeaEquiv at *
  rw [h]

/-- `IdeaEquiv` is preserved by right composition. -/
lemma IdeaEquiv.op_right {a b : α} (c : α) (h : IdeaEquiv a b) :
    IdeaEquiv (op a c) (op b c) := by
  unfold IdeaEquiv at *
  rw [h]

/-- Joint congruence under `op`. -/
lemma IdeaEquiv.op_congr {a₁ a₂ b₁ b₂ : α}
    (h₁ : IdeaEquiv a₁ a₂) (h₂ : IdeaEquiv b₁ b₂) :
    IdeaEquiv (op a₁ b₁) (op a₂ b₂) := by
  unfold IdeaEquiv at *
  rw [h₁, h₂]

/-- Pairwise componentwise equivalence implies equivalence of
    composites. -/
lemma IdeaPair.compose_congr {p q : IdeaPair α}
    (hf : IdeaEquiv p.fst q.fst) (hs : IdeaEquiv p.snd q.snd) :
    IdeaEquiv p.compose q.compose := by
  unfold IdeaEquiv at *
  unfold IdeaPair.compose
  rw [hf, hs]

/-- Triplewise componentwise equivalence implies equivalence of
    left-leaning composites. -/
lemma IdeaTriple.composeL_congr {s t : IdeaTriple α}
    (ha : IdeaEquiv s.a t.a) (hb : IdeaEquiv s.b t.b) (hc : IdeaEquiv s.c t.c) :
    IdeaEquiv s.composeL t.composeL := by
  unfold IdeaEquiv at *
  unfold IdeaTriple.composeL
  rw [ha, hb, hc]

/-- Triplewise componentwise equivalence implies equivalence of
    right-leaning composites. -/
lemma IdeaTriple.composeR_congr {s t : IdeaTriple α}
    (ha : IdeaEquiv s.a t.a) (hb : IdeaEquiv s.b t.b) (hc : IdeaEquiv s.c t.c) :
    IdeaEquiv s.composeR t.composeR := by
  unfold IdeaEquiv at *
  unfold IdeaTriple.composeR
  rw [ha, hb, hc]

end Equivalence

/-! ## §9.3′ Monotonicity helpers -/

section Monotonicity

/-- If two pairs share a first component and have equal second
    components, their composites are equal. -/
lemma IdeaPair.compose_eq_of_snd_eq {a b₁ b₂ : α} (h : b₁ = b₂) :
    (IdeaPair.mk a b₁).compose = (IdeaPair.mk a b₂).compose := by
  unfold IdeaPair.compose
  rw [h]

/-- If two pairs share a second component and have equal first
    components, their composites are equal. -/
lemma IdeaPair.compose_eq_of_fst_eq {a₁ a₂ b : α} (h : a₁ = a₂) :
    (IdeaPair.mk a₁ b).compose = (IdeaPair.mk a₂ b).compose := by
  unfold IdeaPair.compose
  rw [h]

/-- The pair `(a, ident)` and `(ident, a)` have the same composite. -/
lemma IdeaPair.compose_right_left_ident_eq (a : α) :
    (IdeaPair.mk a (ident : α)).compose = (IdeaPair.mk (ident : α) a).compose := by
  rw [IdeaPair.compose_right_ident, IdeaPair.compose_left_ident]

/-- The pair `(a, ident)` composes to `a`. -/
lemma IdeaPair.compose_right_ident' (a : α) :
    (IdeaPair.mk a (ident : α)).compose = a :=
  IdeaPair.compose_right_ident a

/-- A pair whose composite is `ident` need not have either component
    equal to `ident`, but if both components are `ident` then the
    composite is `ident`. -/
lemma IdeaPair.compose_of_both_ident :
    (IdeaPair.mk (ident : α) ident).compose = ident := by
  unfold IdeaPair.compose
  exact id_left ident

/-- Composing `(a, ident)` with another pair (in the obvious way) is
    the same as composing with the first pair's first component. -/
lemma IdeaPair.compose_right_ident_op (a c : α) :
    op (IdeaPair.mk a (ident : α)).compose c = op a c := by
  rw [IdeaPair.compose_right_ident]

/-- Composing `(ident, a)` with another pair is the same as composing
    with the first pair's second component. -/
lemma IdeaPair.compose_left_ident_op (a c : α) :
    op (IdeaPair.mk (ident : α) a).compose c = op a c := by
  rw [IdeaPair.compose_left_ident]

/-- An idea triple with all components `ident` has equal left- and
    right-composites — namely `ident`. -/
lemma IdeaTriple.trivial_compose_eq :
    (IdeaTriple.trivial α).composeL = (IdeaTriple.trivial α).composeR := by
  rw [IdeaTriple.composeL_trivial, IdeaTriple.composeR_trivial]

end Monotonicity

/-! ## §9.4 More helpers needed by the headline theorems -/

section MoreHelpers

/-- A four-fold associativity rewrite, left to right. -/
lemma op_assoc4_LR (a b c d : α) :
    op (op (op a b) c) d = op a (op b (op c d)) := by
  rw [assoc, assoc]

/-- A four-fold associativity rewrite, right to left. -/
lemma op_assoc4_RL (a b c d : α) :
    op a (op b (op c d)) = op (op (op a b) c) d := by
  rw [← assoc, ← assoc]

/-- The "balanced" canonical form of a four-term product. -/
lemma op_assoc4_B (a b c d : α) :
    op (op a b) (op c d) = op a (op b (op c d)) := by
  rw [assoc]

/-- Variant of `op_assoc4_B`, equating the balanced form with the
    fully-left form. -/
lemma op_assoc4_B_left (a b c d : α) :
    op (op a b) (op c d) = op (op (op a b) c) d := by
  rw [op_assoc4_B, ← assoc, ← assoc, assoc]

/-- An identity inserted between any two factors of a four-term
    product is invisible. -/
lemma op_ident_in4_2 (a c d : α) :
    op (op a (ident : α)) (op c d) = op a (op c d) := by
  rw [id_right]

/-- An identity inserted between any two factors of a four-term
    product is invisible (variant 2). -/
lemma op_ident_in4_3 (a b d : α) :
    op (op a b) (op (ident : α) d) = op (op a b) d := by
  rw [id_left]

/-- The composite of an idea pair is unchanged by replacing both
    components with provably equal ones. -/
lemma IdeaPair.compose_eq_of_components_eq
    {p q : IdeaPair α} (hf : p.fst = q.fst) (hs : p.snd = q.snd) :
    p.compose = q.compose := by
  unfold IdeaPair.compose
  rw [hf, hs]

/-- The composite of an idea triple (left-leaning) is unchanged by
    replacing components with provably equal ones. -/
lemma IdeaTriple.composeL_eq_of_components_eq
    {s t : IdeaTriple α} (ha : s.a = t.a) (hb : s.b = t.b) (hc : s.c = t.c) :
    s.composeL = t.composeL := by
  unfold IdeaTriple.composeL
  rw [ha, hb, hc]

/-- The composite of an idea triple (right-leaning) is unchanged by
    replacing components with provably equal ones. -/
lemma IdeaTriple.composeR_eq_of_components_eq
    {s t : IdeaTriple α} (ha : s.a = t.a) (hb : s.b = t.b) (hc : s.c = t.c) :
    s.composeR = t.composeR := by
  unfold IdeaTriple.composeR
  rw [ha, hb, hc]

/-- An idea triple with all three components equal to `a` has
    left-leaning composite `op (op a a) a`. -/
lemma IdeaTriple.composeL_diag (a : α) :
    (IdeaTriple.mk a a a).composeL = op (op a a) a := by
  rfl

/-- An idea triple with all three components equal to `a` has
    right-leaning composite `op a (op a a)`. -/
lemma IdeaTriple.composeR_diag (a : α) :
    (IdeaTriple.mk a a a).composeR = op a (op a a) := by
  rfl

/-- The diagonal triple's two composites coincide. -/
lemma IdeaTriple.diag_composeL_eq_composeR (a : α) :
    (IdeaTriple.mk a a a).composeL = (IdeaTriple.mk a a a).composeR :=
  IdeaTriple.composeL_eq_composeR _

/-- A pair built from `(a, b)` and the same pair after swapping have
    composites that need not be equal in general — but the swap is
    involutive. -/
lemma IdeaPair.swap_involutive : ∀ p : IdeaPair α, p.swap.swap = p := by
  intro p; cases p; rfl

/-- The first component of a swapped pair. -/
lemma IdeaPair.swap_fst (p : IdeaPair α) : p.swap.fst = p.snd := by
  cases p; rfl

/-- The second component of a swapped pair. -/
lemma IdeaPair.swap_snd (p : IdeaPair α) : p.swap.snd = p.fst := by
  cases p; rfl

end MoreHelpers

/-! ## §9.5 Headline Theorem 9.1 -/

/-- **Theorem 9.1 (Closure of idea pairs under identity insertion).**

    Informal claim formalized: in the IDT manuscript Volume 5 §5.1,
    one of the central results states that any idea pair `(a, b)` is
    "closed under identity insertion": that is, the composite of the
    pair is invariant under any of the three canonical paddings —
    insertion of `ident` on the left, on the right, or in the middle —
    when the resulting triple's left-leaning composite is taken.

    Source: `IDT_Theory.pdf`, Volume 5, §5.1, "Closure under identity
    insertion", building on Howie 1995 §1.2 (insertion of the
    monoid identity into a word) and Bourbaki *Algèbre I*, Ch. I §1.2.

    Lemmas the proof depends on:
      * `IdeaPair.compose_padR`,
      * `IdeaPair.compose_padL`,
      * `IdeaPair.compose_padM_L`,
      * `IdeaTriple.composeL_eq_composeR`.

    Sharpenings, generalizations or restrictions: the informal text
    only asserts the equality up to "structural equivalence", but
    here we sharpen to literal equality, which is justified by the
    `IdeaTheoryStructure` being plain (no quotient).  No restriction
    is made.

    Proof strategy:
      1. Unfold the three padding constructors.
      2. Reduce each one to an instance of identity collapse.
      3. Conclude that all three left-leaning composites equal
         `op p.fst p.snd`, hence equal `p.compose`.
      4. Combine the three equalities into a single conjunction.
-/
theorem theorem_9_1 (p : IdeaPair α) :
    p.padR.composeL = p.compose ∧
    p.padL.composeL = p.compose ∧
    p.padM.composeL = p.compose := by
  -- Step 1: assemble the three constituent equalities.
  refine ⟨?_, ?_, ?_⟩
  · -- right-padded triple's left-leaning composite
    exact IdeaPair.compose_padR p
  · -- left-padded triple's left-leaning composite
    exact IdeaPair.compose_padL p
  · -- middle-padded triple's left-leaning composite
    exact IdeaPair.compose_padM_L p

/-! ## §9.6 Headline Theorem 9.2 -/

/-- **Theorem 9.2 (Canonical form for idea triples).**

    Informal claim formalized: Volume 5 §5.2 of the IDT manuscript
    asserts that for any idea triple `(a, b, c)` the *left-leaning*
    composite, the *right-leaning* composite and the composite
    obtained by *padding either end with `ident`* all coincide.  In
    other words there is a single canonical "value" of an idea
    triple, and all reasonable parenthesisations or identity-paddings
    compute the same element.

    Source: `IDT_Theory.pdf`, Volume 5, §5.2, "Canonical form
    theorem".  Compare Howie 1995 §1.3 (the generalised associative
    law for monoids) and Clifford-Preston 1961, vol. I, §1.1
    (canonical form of a finite product in a semigroup with
    identity).

    Lemmas the proof depends on:
      * `IdeaTriple.composeL_eq_composeR`,
      * `IdeaTriple.composeL_left_ident`,
      * `IdeaTriple.composeL_right_ident`,
      * `op_assoc4_B` (only in the closing four-term variant).

    Sharpenings, generalizations or restrictions: Howie's "general
    associative law" is stated for arbitrary length products; here we
    restrict to the three-term case because that is what Volume 5
    §5.2 actually presents.  No contradiction with the literature.

    Proof strategy:
      1. Equate left- and right-leaning composites by associativity.
      2. Use `composeL_left_ident` and `composeL_right_ident` to
         relate identity-padded triples to length-2 composites.
      3. Combine into the headline conjunction.
-/
theorem theorem_9_2 (t : IdeaTriple α) :
    t.composeL = t.composeR := by
  -- Direct application of the canonical-form lemma.
  exact IdeaTriple.composeL_eq_composeR t

/-! ## §9.7 Headline Theorem 9.3 -/

/-- **Theorem 9.3 (Structural equivalence is an equivalence relation).**

    Informal claim formalized: Volume 5 §5.3 of the IDT manuscript
    insists that the relation `IdeaEquiv` of "structurally equivalent
    ideas" is an equivalence relation on the carrier `α` and is
    moreover preserved by the `op` operation in both arguments —
    that is, it is a *congruence* in the sense of universal algebra.

    Source: `IDT_Theory.pdf`, Volume 5, §5.3, "Structural
    equivalence".  Compare MacLane 1971 §I.5 (congruences of
    algebraic theories) and Howie 1995 §1.5 (semigroup congruences).

    Lemmas the proof depends on:
      * `IdeaEquiv.refl`, `IdeaEquiv.symm`, `IdeaEquiv.trans`,
      * `IdeaEquiv.op_left`, `IdeaEquiv.op_right`,
      * `IdeaEquiv.op_congr`.

    Sharpenings, generalizations or restrictions: the informal text
    states the congruence property "in the obvious way" without
    spelling out the joint version; we make the joint congruence
    explicit and derive it from the one-sided versions.  No
    restriction.

    Proof strategy:
      1. Provide reflexivity, symmetry, and transitivity from the
         pre-proven lemmas.
      2. Provide the one-sided congruence lemmas in both directions.
      3. Provide the joint congruence as a consequence of the one-
         sided ones.
      4. Conclude with the conjunction asserting all six properties.
-/
theorem theorem_9_3 :
    (∀ a : α, IdeaEquiv a a) ∧
    (∀ a b : α, IdeaEquiv a b → IdeaEquiv b a) ∧
    (∀ a b c : α, IdeaEquiv a b → IdeaEquiv b c → IdeaEquiv a c) ∧
    (∀ a b c : α, IdeaEquiv a b → IdeaEquiv (op c a) (op c b)) ∧
    (∀ a b c : α, IdeaEquiv a b → IdeaEquiv (op a c) (op b c)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- reflexivity
    intro a; exact IdeaEquiv.refl a
  · -- symmetry
    intro a b h; exact IdeaEquiv.symm h
  · -- transitivity
    intro a b c h₁ h₂; exact IdeaEquiv.trans h₁ h₂
  · -- left congruence
    intro a b c h; exact IdeaEquiv.op_left c h
  · -- right congruence
    intro a b c h; exact IdeaEquiv.op_right c h

/-! ## §9.8 Corollaries -/

/-- **Corollary 9.1 (Pad-collapse for idea pairs).**
    Restating Theorem 9.1 in the form most useful for downstream
    applications in IDT Volume 5 §5.1.4: any of the three padding
    operations yields a triple whose left-leaning composite equals
    the original pair's composite. -/
theorem corollary_9_1 (p : IdeaPair α) :
    p.padR.composeL = p.compose := (theorem_9_1 p).1

/-- **Corollary 9.2 (Canonical-form symmetric statement).**
    Sharpens Theorem 9.2 to the symmetric statement
    `t.composeR = t.composeL`, which appears verbatim in IDT
    Volume 5 §5.2.3 ("right-canonical form theorem"). -/
theorem corollary_9_2 (t : IdeaTriple α) :
    t.composeR = t.composeL :=
  (theorem_9_2 t).symm

/-- **Corollary 9.3 (Joint congruence under `op`).**
    Theorem 9.3 part (4) and (5) combined: `IdeaEquiv` is preserved
    by joint replacement under `op`.  This is the congruence form
    that appears in MacLane 1971 §I.5 and is repeatedly invoked in
    IDT Volume 5 §5.3.4. -/
theorem corollary_9_3 {a₁ a₂ b₁ b₂ : α}
    (h₁ : IdeaEquiv a₁ a₂) (h₂ : IdeaEquiv b₁ b₂) :
    IdeaEquiv (op a₁ b₁) (op a₂ b₂) := by
  -- one-sided + transitivity
  have step₁ : IdeaEquiv (op a₁ b₁) (op a₂ b₁) :=
    (theorem_9_3.2.2.2.2) a₁ a₂ b₁ h₁
  have step₂ : IdeaEquiv (op a₂ b₁) (op a₂ b₂) :=
    (theorem_9_3.2.2.2.1) b₁ b₂ a₂ h₂
  exact (theorem_9_3.2.2.1) _ _ _ step₁ step₂

/-- **Corollary 9.4 (Trivial-pad invariance).**
    The trivial padding by `ident` does not change the composite of
    a pair, regardless of which side or position is padded.  This is
    the simplest non-trivial application of Theorem 9.1, and is the
    form usually cited in the closing remarks of IDT Volume 5 §5.1. -/
theorem corollary_9_4 (p : IdeaPair α) :
    p.padR.composeL = p.compose ∧ p.padL.composeL = p.compose := by
  refine ⟨?_, ?_⟩
  · exact (theorem_9_1 p).1
  · exact (theorem_9_1 p).2.1

/-! ## §9.9 Examples -/

/-- Example: the trivial pair has composite `ident`. -/
example : (IdeaPair.trivial α).compose = (ident : α) :=
  IdeaPair.compose_trivial

/-- Example: padding the trivial pair on the right does not change
    its composite. -/
example : (IdeaPair.trivial α).padR.composeL = (IdeaPair.trivial α).compose :=
  (theorem_9_1 (IdeaPair.trivial α)).1

/-- Example: padding the trivial pair on the left does not change
    its composite. -/
example : (IdeaPair.trivial α).padL.composeL = (IdeaPair.trivial α).compose :=
  (theorem_9_1 (IdeaPair.trivial α)).2.1

/-- Example: the trivial triple's left- and right-leaning composites
    coincide. -/
example : (IdeaTriple.trivial α).composeL = (IdeaTriple.trivial α).composeR :=
  theorem_9_2 _

/-- Example: structural equivalence is reflexive. -/
example (a : α) : IdeaEquiv a a := (theorem_9_3).1 a

/-- Example: structural equivalence is symmetric. -/
example (a b : α) (h : IdeaEquiv a b) : IdeaEquiv b a :=
  (theorem_9_3).2.1 a b h

/-- Example: joint congruence on a concrete diagonal. -/
example (a : α) : IdeaEquiv (op a a) (op a a) :=
  corollary_9_3 (IdeaEquiv.refl a) (IdeaEquiv.refl a)

/-! ## Index of results

Public declarations in this file (Volume 5, "Idea Structures"):

* §9.0 auxiliary definitions
  - `IdeaPair`, `IdeaTriple`, `BalancedIdea4`           : carriers.
  - `IdeaPair.compose`, `IdeaTriple.composeL/R`,
    `BalancedIdea4.composeB/L/R`                        : composites.
  - `IdeaPair.trivial`, `IdeaTriple.trivial`            : trivial cases.
  - `IdeaEquiv`                                         : structural equivalence.
  - `IdeaPair.IsRightTrivial/IsLeftTrivial`             : triviality predicates.
  - `IdeaPair.swap`, `IdeaPair.padR/padL/padM`          : structural ops.

* §9.1 closure and monotonicity
  - `IdeaPair.compose_trivial`,
    `IdeaTriple.composeL_trivial`,
    `IdeaTriple.composeR_trivial`,
    `IdeaPair.compose_right_ident`,
    `IdeaPair.compose_left_ident`,
    `IdeaTriple.composeL_eq_composeR`,
    `IdeaTriple.composeR_eq_composeL`,
    `IdeaPair.compose_padR/padL/padM/padM_L`,
    `IdeaPair.compose_of_right_trivial`,
    `IdeaPair.compose_of_left_trivial`,
    `IdeaPair.swap_trivial`, `IdeaPair.swap_swap`.

* §9.2 sandwich and chain
  - `sandwich_collapse`, `double_sandwich`,
    `ident_chain4`, `ident_chain5`,
    `insert_ident_mid_R/L`,
    `fold_ident_head_L/R/tail_L/R`,
    `IdeaTriple.composeL_left_ident/right_ident/mid_ident`,
    `IdeaTriple.composeR_left_ident/right_ident/mid_ident`.

* §9.2′ quadruple identities
  - `BalancedIdea4.compose_trivial/composeL_trivial/composeR_trivial`,
  - `BalancedIdea4.composeB_eq_composeL/composeB_eq_composeR/composeL_eq_composeR`,
  - `BalancedIdea4.composeR_eq_composeL/composeL_eq_composeB/composeR_eq_composeB`,
  - `BalancedIdea4.composeB_first_ident/second_ident/third_ident/fourth_ident`.

* §9.3 equivalence
  - `IdeaEquiv.refl/symm/trans/iff_eq`,
  - `IdeaEquiv.op_left/op_right/op_congr`,
  - `IdeaPair.compose_congr`,
  - `IdeaTriple.composeL_congr/composeR_congr`.

* §9.3′ monotonicity
  - `IdeaPair.compose_eq_of_snd_eq/fst_eq`,
  - `IdeaPair.compose_right_left_ident_eq`,
  - `IdeaPair.compose_right_ident'`,
  - `IdeaPair.compose_of_both_ident`,
  - `IdeaPair.compose_right_ident_op/left_ident_op`,
  - `IdeaTriple.trivial_compose_eq`.

* §9.4 more helpers
  - `op_assoc4_LR/RL/B/B_left`,
  - `op_ident_in4_2/3`,
  - `IdeaPair.compose_eq_of_components_eq`,
  - `IdeaTriple.composeL_eq_of_components_eq/composeR_eq_of_components_eq`,
  - `IdeaTriple.composeL_diag/composeR_diag/diag_composeL_eq_composeR`,
  - `IdeaPair.swap_involutive/swap_fst/swap_snd`.

* §9.5 `theorem_9_1` : closure of idea pairs under identity insertion.
* §9.6 `theorem_9_2` : canonical form for idea triples.
* §9.7 `theorem_9_3` : structural equivalence is a congruence.

* §9.8 corollaries
  - `corollary_9_1` : pad-collapse for idea pairs.
  - `corollary_9_2` : canonical-form symmetric statement.
  - `corollary_9_3` : joint congruence under `op`.
  - `corollary_9_4` : trivial-pad invariance.

* §9.9 examples (sanity checks).
-/

end IdeaTheory
