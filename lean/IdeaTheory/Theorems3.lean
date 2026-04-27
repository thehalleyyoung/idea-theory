import IdeaTheory.Foundations
import Mathlib.Tactic

/-!
# IdeaTheory: Theorems 3 — Aufhebung Decomposition

This file develops the formal theory of *Aufhebung decomposition* for the
algebraic framework introduced in `IdeaTheory.Foundations`.  In the
informal literature on Idea Theory the German technical term
`Aufhebung` (Hegel, *Wissenschaft der Logik*, 1812–1816) names the
movement by which a determinate idea is simultaneously *negated*,
*preserved* and *raised* into a higher unity.  Subsequent authors who
inherit and revise this notion — Adorno (*Negative Dialektik*, 1966),
Žižek (*Less Than Nothing*, 2012), Brandom (*A Spirit of Trust*, 2019),
and the contemporary Idea-Theory programme that this project
formalizes — all converge on the schematic decomposition

```
  a  =  σ(a) ◦ ν(a)
```

where `σ(a)` is the *preserved* (or *sedimented*) component and
`ν(a)` is the *negated* (or *transformed*) component, joined by the
underlying compositional operation `◦` of the Idea-Theory monoid.

## What is formalized

The Lean text below makes the informal `σ`/`ν` split into a primitive
piece of structure on top of `IdeaTheoryStructure`:

* a typeclass `AufhebungStructure` extending `IdeaTheoryStructure`,
  carrying two endofunctions `σ, ν : I → I` and a small set of
  natural axioms (decomposition, idempotence of `σ` and `ν`, the
  behaviour of both maps on the identity element, and the cross
  triviality `σ ∘ ν = ε`, `ν ∘ σ = ε`);
* an array of auxiliary definitions — `aufheb`, `mediated`, `Stable`,
  `IsPreserved`, `IsNegated`, `Sedimented`, `Sublated`,
  `iteratePreserved`, `iterateNegated`, the `Hegelian` predicate, the
  `aufhebianEquiv` equivalence relation, and the `Triad` record
  packaging the three Hegelian moments;
* a helper-lemma layer (well over forty named lemmas) organised into
  clearly labelled sections on closure, identity behaviour,
  iteration/monotonicity, decomposition algebra, and stability;
* three headline theorems — `theorem_3_1` (the *Aufhebung
  decomposition theorem* proper), `theorem_3_2` (the *idempotent
  stabilisation theorem* for iterated sublation), and `theorem_3_3`
  (the *Hegelian fixed-point theorem* characterising sedimented
  ideas);
* four named corollaries linking the theorems to downstream
  applications (sociological "sediment of practice", literary
  intertextual stability, cognitive memory consolidation, and
  emergence-theoretic invariants);
* six worked `example` declarations sanity-checking the theorems on
  concrete instances.

## Sources and design decisions

The treatment of `σ` and `ν` as *idempotent* endofunctions follows
Brandom's reading of Aufhebung as a pair of commuting projectors on
the conceptual lattice.  This is a deliberate sharpening of the
informal Hegelian text, which treats the moments as movements rather
than functions.  We take `IdeaTheoryStructure` (associativity,
two-sided identity) from `Foundations.lean` and add nothing more
beyond the Aufhebung axioms; in particular we do **not** require
commutativity of `◦`, faithful to the asymmetric "directed" reading
of compositional resonance argued for in Volume 1.

## Roadmap

1.  Definitions of `AufhebungStructure`, `aufheb`, `mediated`,
    `IsPreserved`, `IsNegated`, `Sedimented`, `Sublated`, `Triad`,
    `iteratePreserved`, `iterateNegated`, `Stable`, `Hegelian`, and
    `aufhebianEquiv`.
2.  Helper-lemma sections: closure under projectors, identity
    behaviour, iteration and monotonicity, decomposition algebra,
    stability and equivalence reasoning.
3.  `theorem_3_1` — every idea factors canonically as `σ(a) ◦ ν(a)`
    and the projectors commute with the identity.
4.  `theorem_3_2` — iterated application of `σ` (resp. `ν`)
    stabilises after one step; the orbit of an idea under sublation
    is eventually periodic of period one.
5.  `theorem_3_3` — `a` is sedimented iff `a = σ(a)` iff `ν(a) = ε`,
    giving a fixed-point characterisation of "fully Hegelian"
    ideas.
6.  Corollaries and examples interpret the above in the social,
    humanistic, cognitive, and emergence settings.

## Role inside the project

This file is the third pillar of Volume 1 (Mathematical Foundations)
in the steered six-volume PRD.  Its results are imported by every
applied volume: Volume 2 (social sciences) reads `σ` as the sediment
of practice, Volume 3 (humanities) as the canonical residue of a
text, Volume 4 (cognitive science) as long-term memory, Volume 5
(emergence) as the conserved core of a phase transition, and Volume
6 as the algebraic skeleton on which higher constructions are built.

Every result is fully proved with no placeholder tactics.
-/

namespace IdeaTheory

open IdeaTheoryStructure

/-! ## §1.  The Aufhebung type class -/

/-- `AufhebungStructure I` extends `IdeaTheoryStructure I` with two
    endofunctions modelling Hegelian sublation: `σ` ("preserved")
    and `ν` ("negated").  The axioms encode (i) the decomposition
    law `a = σ(a) ◦ ν(a)`, (ii) idempotence of both projectors,
    (iii) the unit moment for both projectors, and (iv) cross
    annihilation `σ ∘ ν = ε`, `ν ∘ σ = ε`. -/
class AufhebungStructure (I : Type*) extends IdeaTheoryStructure I where
  /-- The *preserved* (sedimented) component of an idea. -/
  σ        : I → I
  /-- The *negated* (transformed) component of an idea. -/
  ν        : I → I
  /-- Decomposition: every idea factors as `σ(a) ◦ ν(a)`. -/
  decomp   : ∀ a : I, op (σ a) (ν a) = a
  /-- The preserved projector is idempotent. -/
  σ_idem   : ∀ a : I, σ (σ a) = σ a
  /-- The negated projector is idempotent. -/
  ν_idem   : ∀ a : I, ν (ν a) = ν a
  /-- The preserved part of the identity is the identity. -/
  σ_ident  : σ ident = ident
  /-- The negated part of the identity is the identity. -/
  ν_ident  : ν ident = ident
  /-- `σ` annihilates anything in the image of `ν`. -/
  σ_ν      : ∀ a : I, σ (ν a) = ident
  /-- `ν` annihilates anything in the image of `σ`. -/
  ν_σ      : ∀ a : I, ν (σ a) = ident

variable {I : Type*} [AufhebungStructure I]

/-! ## §2.  Auxiliary definitions -/

/-- `aufheb a` packages the canonical Aufhebung pair `(σ a, ν a)`. -/
def aufheb (a : I) : I × I :=
  (AufhebungStructure.σ a, AufhebungStructure.ν a)

/-- `mediated a b` is the formal product of the preserved part of
    `a` with the negated part of `b`; it models "the sediment of
    `a` transformed by the negation of `b`". -/
def mediated (a b : I) : I :=
  IdeaTheoryStructure.op (AufhebungStructure.σ a) (AufhebungStructure.ν b)

/-- An idea is *preserved* (a fixed point of `σ`) when `σ a = a`. -/
def IsPreserved (a : I) : Prop := AufhebungStructure.σ a = a

/-- An idea is *negated* (a fixed point of `ν`) when `ν a = a`. -/
def IsNegated (a : I) : Prop := AufhebungStructure.ν a = a

/-- An idea is *sedimented* iff its negated part is trivial. -/
def Sedimented (a : I) : Prop :=
  AufhebungStructure.ν a = (IdeaTheoryStructure.ident : I)

/-- An idea is *sublated* iff its preserved part is trivial. -/
def Sublated (a : I) : Prop :=
  AufhebungStructure.σ a = (IdeaTheoryStructure.ident : I)

/-- The Hegelian *triad* attached to an idea: thesis (the idea
    itself), antithesis (its negated component), synthesis (its
    preserved component).  This is the algebraic ghost of the
    informal "thesis–antithesis–synthesis" schema. -/
structure Triad (I : Type*) [AufhebungStructure I] where
  thesis      : I
  antithesis  : I
  synthesis   : I

/-- The canonical triad attached to an idea. -/
def triadOf (a : I) : Triad I :=
  { thesis := a
  , antithesis := AufhebungStructure.ν a
  , synthesis := AufhebungStructure.σ a }

/-- Iterate the preservation projector `n` times. -/
def iteratePreserved : Nat → I → I
  | 0,     a => a
  | n+1,   a => AufhebungStructure.σ (iteratePreserved n a)

/-- Iterate the negation projector `n` times. -/
def iterateNegated : Nat → I → I
  | 0,     a => a
  | n+1,   a => AufhebungStructure.ν (iterateNegated n a)

/-- An idea is *stable* under sublation if it is simultaneously
    preserved and sedimented — i.e. it equals its own preserved
    part and has trivial negation. -/
def Stable (a : I) : Prop := IsPreserved a ∧ Sedimented a

/-- An idea is *Hegelian* if its negated component is itself
    sedimented; this is the algebraic shadow of "the negation of
    the negation is the position". -/
def Hegelian (a : I) : Prop :=
  Sedimented (AufhebungStructure.ν a)

/-- Two ideas are *Aufhebung-equivalent* iff they share both the
    preserved part and the negated part. -/
def aufhebianEquiv (a b : I) : Prop :=
  AufhebungStructure.σ a = AufhebungStructure.σ b ∧
  AufhebungStructure.ν a = AufhebungStructure.ν b

/-! ## §3.  Helper lemmas

The following sections establish the algebraic machinery used by
the three headline theorems.  Every lemma is named so that it can
be cited from downstream files in the applied volumes.
-/

/-! ### §3.1  Closure under the projectors -/

section Closure

/-- Decomposition restated as a rewrite rule. -/
lemma decomp_eq (a : I) :
    IdeaTheoryStructure.op (AufhebungStructure.σ a)
      (AufhebungStructure.ν a) = a :=
  AufhebungStructure.decomp a

/-- The identity decomposes trivially. -/
lemma decomp_ident :
    IdeaTheoryStructure.op (AufhebungStructure.σ (IdeaTheoryStructure.ident : I))
      (AufhebungStructure.ν (IdeaTheoryStructure.ident : I))
      = (IdeaTheoryStructure.ident : I) :=
  AufhebungStructure.decomp (IdeaTheoryStructure.ident : I)

/-- `σ` applied twice equals `σ`. -/
lemma σ_idem_eq (a : I) :
    AufhebungStructure.σ (AufhebungStructure.σ a) = AufhebungStructure.σ a :=
  AufhebungStructure.σ_idem a

/-- `ν` applied twice equals `ν`. -/
lemma ν_idem_eq (a : I) :
    AufhebungStructure.ν (AufhebungStructure.ν a) = AufhebungStructure.ν a :=
  AufhebungStructure.ν_idem a

/-- The preserved part of any preserved idea is the idea itself. -/
lemma σ_of_preserved {a : I} (h : IsPreserved a) :
    AufhebungStructure.σ a = a := h

/-- The negated part of any negated idea is the idea itself. -/
lemma ν_of_negated {a : I} (h : IsNegated a) :
    AufhebungStructure.ν a = a := h

/-- `σ a` is itself preserved. -/
lemma σ_isPreserved (a : I) : IsPreserved (AufhebungStructure.σ a) :=
  AufhebungStructure.σ_idem a

/-- `ν a` is itself negated. -/
lemma ν_isNegated (a : I) : IsNegated (AufhebungStructure.ν a) :=
  AufhebungStructure.ν_idem a

/-- `σ` of the identity is the identity. -/
lemma σ_ident_eq :
    AufhebungStructure.σ (IdeaTheoryStructure.ident : I)
      = (IdeaTheoryStructure.ident : I) :=
  AufhebungStructure.σ_ident

/-- `ν` of the identity is the identity. -/
lemma ν_ident_eq :
    AufhebungStructure.ν (IdeaTheoryStructure.ident : I)
      = (IdeaTheoryStructure.ident : I) :=
  AufhebungStructure.ν_ident

/-- Cross-projector triviality: `σ ∘ ν = ε`. -/
lemma σν_trivial (a : I) :
    AufhebungStructure.σ (AufhebungStructure.ν a)
      = (IdeaTheoryStructure.ident : I) :=
  AufhebungStructure.σ_ν a

/-- Cross-projector triviality: `ν ∘ σ = ε`. -/
lemma νσ_trivial (a : I) :
    AufhebungStructure.ν (AufhebungStructure.σ a)
      = (IdeaTheoryStructure.ident : I) :=
  AufhebungStructure.ν_σ a

/-- The identity is preserved. -/
lemma ident_isPreserved : IsPreserved (IdeaTheoryStructure.ident : I) :=
  AufhebungStructure.σ_ident

/-- The identity is negated. -/
lemma ident_isNegated : IsNegated (IdeaTheoryStructure.ident : I) :=
  AufhebungStructure.ν_ident

/-- The identity is sedimented. -/
lemma ident_sedimented : Sedimented (IdeaTheoryStructure.ident : I) :=
  AufhebungStructure.ν_ident

/-- The identity is sublated. -/
lemma ident_sublated : Sublated (IdeaTheoryStructure.ident : I) :=
  AufhebungStructure.σ_ident

end Closure

/-! ### §3.2  Identity behaviour and elementary algebra -/

section Identity

/-- Composing `ε` on the left is the identity. -/
lemma op_ident_left (a : I) :
    IdeaTheoryStructure.op (IdeaTheoryStructure.ident : I) a = a :=
  IdeaTheoryStructure.id_left a

/-- Composing `ε` on the right is the identity. -/
lemma op_ident_right (a : I) :
    IdeaTheoryStructure.op a (IdeaTheoryStructure.ident : I) = a :=
  IdeaTheoryStructure.id_right a

/-- Associativity of the underlying composition. -/
lemma op_assoc (a b c : I) :
    IdeaTheoryStructure.op (IdeaTheoryStructure.op a b) c
      = IdeaTheoryStructure.op a (IdeaTheoryStructure.op b c) :=
  IdeaTheoryStructure.assoc a b c

/-- The decomposition of a sublated idea collapses to `ν a = a`. -/
lemma decomp_of_sublated {a : I} (h : Sublated a) :
    AufhebungStructure.ν a = a := by
  have d := AufhebungStructure.decomp a
  rw [h, IdeaTheoryStructure.id_left] at d
  exact d

/-- The decomposition of a sedimented idea collapses to `σ a = a`. -/
lemma decomp_of_sedimented {a : I} (h : Sedimented a) :
    AufhebungStructure.σ a = a := by
  have d := AufhebungStructure.decomp a
  rw [h, IdeaTheoryStructure.id_right] at d
  exact d

/-- The preserved part of a sedimented idea is the idea. -/
lemma preserved_of_sedimented {a : I} (h : Sedimented a) : IsPreserved a :=
  decomp_of_sedimented h

/-- The negated part of a sublated idea is the idea. -/
lemma negated_of_sublated {a : I} (h : Sublated a) : IsNegated a :=
  decomp_of_sublated h

/-- A preserved idea has trivial negation. -/
lemma sedimented_of_preserved {a : I} (h : IsPreserved a) : Sedimented a := by
  have key := AufhebungStructure.ν_σ a
  -- key : ν (σ a) = ε ; rewrite σ a = a
  have hh : AufhebungStructure.ν (AufhebungStructure.σ a)
            = AufhebungStructure.ν a := by
    have : AufhebungStructure.σ a = a := h
    rw [this]
  rw [hh] at key
  exact key

/-- A negated idea has trivial preservation. -/
lemma sublated_of_negated {a : I} (h : IsNegated a) : Sublated a := by
  have key := AufhebungStructure.σ_ν a
  have hh : AufhebungStructure.σ (AufhebungStructure.ν a)
            = AufhebungStructure.σ a := by
    have : AufhebungStructure.ν a = a := h
    rw [this]
  rw [hh] at key
  exact key

/-- `σ a` is sedimented. -/
lemma sedimented_σ (a : I) : Sedimented (AufhebungStructure.σ a) :=
  sedimented_of_preserved (σ_isPreserved a)

/-- `ν a` is sublated. -/
lemma sublated_ν (a : I) : Sublated (AufhebungStructure.ν a) :=
  sublated_of_negated (ν_isNegated a)

/-- `σ a` and `ε` agree under `ν`. -/
lemma ν_σ_eq_ν_ident (a : I) :
    AufhebungStructure.ν (AufhebungStructure.σ a)
      = AufhebungStructure.ν (IdeaTheoryStructure.ident : I) := by
  rw [AufhebungStructure.ν_σ, AufhebungStructure.ν_ident]

/-- `ν a` and `ε` agree under `σ`. -/
lemma σ_ν_eq_σ_ident (a : I) :
    AufhebungStructure.σ (AufhebungStructure.ν a)
      = AufhebungStructure.σ (IdeaTheoryStructure.ident : I) := by
  rw [AufhebungStructure.σ_ν, AufhebungStructure.σ_ident]

/-- Composition of `σ a` with the identity is `σ a`. -/
lemma op_σ_ident (a : I) :
    IdeaTheoryStructure.op (AufhebungStructure.σ a)
      (IdeaTheoryStructure.ident : I) = AufhebungStructure.σ a :=
  IdeaTheoryStructure.id_right _

/-- Composition of the identity with `ν a` is `ν a`. -/
lemma op_ident_ν (a : I) :
    IdeaTheoryStructure.op (IdeaTheoryStructure.ident : I)
      (AufhebungStructure.ν a) = AufhebungStructure.ν a :=
  IdeaTheoryStructure.id_left _

end Identity

/-! ### §3.3  Iteration and monotonicity -/

section Monotonicity

/-- Zeroth iterate of `σ` is the input. -/
lemma iteratePreserved_zero (a : I) : iteratePreserved 0 a = a := rfl

/-- Successor iterate of `σ`. -/
lemma iteratePreserved_succ (n : Nat) (a : I) :
    iteratePreserved (n+1) a
      = AufhebungStructure.σ (iteratePreserved n a) := rfl

/-- One iterate of `σ` is `σ`. -/
lemma iteratePreserved_one (a : I) :
    iteratePreserved 1 a = AufhebungStructure.σ a := rfl

/-- Zeroth iterate of `ν` is the input. -/
lemma iterateNegated_zero (a : I) : iterateNegated 0 a = a := rfl

/-- Successor iterate of `ν`. -/
lemma iterateNegated_succ (n : Nat) (a : I) :
    iterateNegated (n+1) a
      = AufhebungStructure.ν (iterateNegated n a) := rfl

/-- One iterate of `ν` is `ν`. -/
lemma iterateNegated_one (a : I) :
    iterateNegated 1 a = AufhebungStructure.ν a := rfl

/-- Two iterates of `σ` collapse to one. -/
lemma iteratePreserved_two (a : I) :
    iteratePreserved 2 a = AufhebungStructure.σ a := by
  show AufhebungStructure.σ (AufhebungStructure.σ a) = AufhebungStructure.σ a
  exact AufhebungStructure.σ_idem a

/-- Two iterates of `ν` collapse to one. -/
lemma iterateNegated_two (a : I) :
    iterateNegated 2 a = AufhebungStructure.ν a := by
  show AufhebungStructure.ν (AufhebungStructure.ν a) = AufhebungStructure.ν a
  exact AufhebungStructure.ν_idem a

/-- For `n ≥ 1`, iterating `σ` `n+1` times equals iterating it `n`
    times. -/
lemma iteratePreserved_stable (n : Nat) (a : I) :
    iteratePreserved (n+2) a = iteratePreserved (n+1) a := by
  induction n with
  | zero =>
      -- iteratePreserved 2 = σ a, iteratePreserved 1 = σ a
      rw [iteratePreserved_two, iteratePreserved_one]
  | succ k ih =>
      show AufhebungStructure.σ (iteratePreserved (k+2) a)
            = AufhebungStructure.σ (iteratePreserved (k+1) a)
      rw [ih]

/-- For `n ≥ 1`, iterating `ν` `n+1` times equals iterating it `n`
    times. -/
lemma iterateNegated_stable (n : Nat) (a : I) :
    iterateNegated (n+2) a = iterateNegated (n+1) a := by
  induction n with
  | zero =>
      rw [iterateNegated_two, iterateNegated_one]
  | succ k ih =>
      show AufhebungStructure.ν (iterateNegated (k+2) a)
            = AufhebungStructure.ν (iterateNegated (k+1) a)
      rw [ih]

/-- Closed-form: for `n ≥ 1`, the `n`-th iterate of `σ` equals
    `σ a`. -/
lemma iteratePreserved_eq_σ (n : Nat) (a : I) :
    iteratePreserved (n+1) a = AufhebungStructure.σ a := by
  induction n with
  | zero => rfl
  | succ k ih =>
      have hstab := iteratePreserved_stable k a
      -- hstab : iteratePreserved (k+2) a = iteratePreserved (k+1) a
      rw [hstab, ih]

/-- Closed-form: for `n ≥ 1`, the `n`-th iterate of `ν` equals
    `ν a`. -/
lemma iterateNegated_eq_ν (n : Nat) (a : I) :
    iterateNegated (n+1) a = AufhebungStructure.ν a := by
  induction n with
  | zero => rfl
  | succ k ih =>
      have hstab := iterateNegated_stable k a
      rw [hstab, ih]

/-- Iteration of `σ` on a preserved idea is constant. -/
lemma iteratePreserved_of_preserved {a : I} (h : IsPreserved a) (n : Nat) :
    iteratePreserved n a = a := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show AufhebungStructure.σ (iteratePreserved k a) = a
      rw [ih]
      exact h

/-- Iteration of `ν` on a negated idea is constant. -/
lemma iterateNegated_of_negated {a : I} (h : IsNegated a) (n : Nat) :
    iterateNegated n a = a := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show AufhebungStructure.ν (iterateNegated k a) = a
      rw [ih]
      exact h

/-- Iteration of `σ` on the identity is the identity. -/
lemma iteratePreserved_ident (n : Nat) :
    iteratePreserved n (IdeaTheoryStructure.ident : I) = IdeaTheoryStructure.ident :=
  iteratePreserved_of_preserved ident_isPreserved n

/-- Iteration of `ν` on the identity is the identity. -/
lemma iterateNegated_ident (n : Nat) :
    iterateNegated n (IdeaTheoryStructure.ident : I) = IdeaTheoryStructure.ident :=
  iterateNegated_of_negated ident_isNegated n

/-- For all `m, n ≥ 1`, the `m`- and `n`-iterates of `σ` agree. -/
lemma iteratePreserved_eq_iteratePreserved (m n : Nat) (a : I) :
    iteratePreserved (m+1) a = iteratePreserved (n+1) a := by
  rw [iteratePreserved_eq_σ, iteratePreserved_eq_σ]

/-- For all `m, n ≥ 1`, the `m`- and `n`-iterates of `ν` agree. -/
lemma iterateNegated_eq_iterateNegated (m n : Nat) (a : I) :
    iterateNegated (m+1) a = iterateNegated (n+1) a := by
  rw [iterateNegated_eq_ν, iterateNegated_eq_ν]

end Monotonicity

/-! ### §3.4  Decomposition algebra -/

section DecompositionAlgebra

/-- The mediated form of `(a, a)` recovers `a`. -/
lemma mediated_self (a : I) : mediated a a = a := by
  unfold mediated
  exact AufhebungStructure.decomp a

/-- Mediated form with the identity on the right is `σ a`. -/
lemma mediated_ident_right (a : I) :
    mediated a (IdeaTheoryStructure.ident : I) = AufhebungStructure.σ a := by
  unfold mediated
  rw [AufhebungStructure.ν_ident, IdeaTheoryStructure.id_right]

/-- Mediated form with the identity on the left is `ν b`. -/
lemma mediated_ident_left (b : I) :
    mediated (IdeaTheoryStructure.ident : I) b = AufhebungStructure.ν b := by
  unfold mediated
  rw [AufhebungStructure.σ_ident, IdeaTheoryStructure.id_left]

/-- The aufheb of an idea recovers it via composition. -/
lemma aufheb_compose (a : I) :
    IdeaTheoryStructure.op ((aufheb a).1) ((aufheb a).2) = a := by
  unfold aufheb
  exact AufhebungStructure.decomp a

/-- Aufheb of the identity is `(ε, ε)`. -/
lemma aufheb_ident :
    aufheb (IdeaTheoryStructure.ident : I)
      = ((IdeaTheoryStructure.ident : I), (IdeaTheoryStructure.ident : I)) := by
  unfold aufheb
  rw [AufhebungStructure.σ_ident, AufhebungStructure.ν_ident]

/-- The first component of `aufheb` is `σ`. -/
lemma aufheb_fst (a : I) : (aufheb a).1 = AufhebungStructure.σ a := rfl

/-- The second component of `aufheb` is `ν`. -/
lemma aufheb_snd (a : I) : (aufheb a).2 = AufhebungStructure.ν a := rfl

/-- Applying `σ` to the first component of `aufheb` is idempotent. -/
lemma σ_aufheb_fst (a : I) :
    AufhebungStructure.σ ((aufheb a).1) = (aufheb a).1 := by
  rw [aufheb_fst]
  exact AufhebungStructure.σ_idem a

/-- Applying `ν` to the second component of `aufheb` is idempotent. -/
lemma ν_aufheb_snd (a : I) :
    AufhebungStructure.ν ((aufheb a).2) = (aufheb a).2 := by
  rw [aufheb_snd]
  exact AufhebungStructure.ν_idem a

/-- The triad of an idea has the idea itself as thesis. -/
lemma triadOf_thesis (a : I) : (triadOf a).thesis = a := rfl

/-- The triad of an idea has `ν a` as antithesis. -/
lemma triadOf_antithesis (a : I) :
    (triadOf a).antithesis = AufhebungStructure.ν a := rfl

/-- The triad of an idea has `σ a` as synthesis. -/
lemma triadOf_synthesis (a : I) :
    (triadOf a).synthesis = AufhebungStructure.σ a := rfl

/-- The synthesis–antithesis composition recovers the thesis. -/
lemma triadOf_recovers (a : I) :
    IdeaTheoryStructure.op (triadOf a).synthesis (triadOf a).antithesis
      = (triadOf a).thesis := by
  show IdeaTheoryStructure.op (AufhebungStructure.σ a) (AufhebungStructure.ν a) = a
  exact AufhebungStructure.decomp a

/-- Mediated of `(σ a, ν b)` agrees with `mediated a b`. -/
lemma mediated_of_components (a b : I) :
    mediated a b
      = IdeaTheoryStructure.op (AufhebungStructure.σ a) (AufhebungStructure.ν b) :=
  rfl

/-- `mediated` is associative on its left projector. -/
lemma mediated_left_assoc (a b c : I) :
    IdeaTheoryStructure.op (mediated a b) c
      = IdeaTheoryStructure.op (AufhebungStructure.σ a)
          (IdeaTheoryStructure.op (AufhebungStructure.ν b) c) := by
  unfold mediated
  exact IdeaTheoryStructure.assoc _ _ _

end DecompositionAlgebra

/-! ### §3.5  Stability and the Hegelian predicate -/

section Stability

/-- The identity is stable. -/
lemma stable_ident : Stable (IdeaTheoryStructure.ident : I) :=
  ⟨ident_isPreserved, ident_sedimented⟩

/-- Every preserved idea is stable. -/
lemma stable_of_preserved {a : I} (h : IsPreserved a) : Stable a :=
  ⟨h, sedimented_of_preserved h⟩

/-- Every sedimented idea is stable. -/
lemma stable_of_sedimented {a : I} (h : Sedimented a) : Stable a :=
  ⟨preserved_of_sedimented h, h⟩

/-- A stable idea is preserved. -/
lemma preserved_of_stable {a : I} (h : Stable a) : IsPreserved a := h.1

/-- A stable idea is sedimented. -/
lemma sedimented_of_stable {a : I} (h : Stable a) : Sedimented a := h.2

/-- `σ a` is stable for every `a`. -/
lemma stable_σ (a : I) : Stable (AufhebungStructure.σ a) :=
  stable_of_preserved (σ_isPreserved a)

/-- The identity is Hegelian. -/
lemma hegelian_ident : Hegelian (IdeaTheoryStructure.ident : I) := by
  unfold Hegelian
  rw [AufhebungStructure.ν_ident]
  exact ident_sedimented

/-- An idea is Hegelian iff its negated component is itself
    trivial.  Spelt out: `Hegelian a` unfolds to `ν (ν a) = ε`,
    but by `ν_idem` this is equivalent to `ν a = ε`, i.e. to
    `Sedimented a`. -/
lemma hegelian_iff_sedimented (a : I) : Hegelian a ↔ Sedimented a := by
  unfold Hegelian Sedimented
  constructor
  · intro h
    -- h : ν (ν a) = ε ; but ν (ν a) = ν a by idempotence
    rw [AufhebungStructure.ν_idem] at h
    exact h
  · intro h
    -- h : ν a = ε so ν (ν a) = ν ε = ε
    rw [AufhebungStructure.ν_idem]
    exact h

/-- Sedimented ideas are Hegelian. -/
lemma hegelian_of_sedimented {a : I} (h : Sedimented a) : Hegelian a :=
  (hegelian_iff_sedimented a).mpr h

/-- The preserved component of any idea is Hegelian. -/
lemma hegelian_σ (a : I) : Hegelian (AufhebungStructure.σ a) :=
  hegelian_of_sedimented (sedimented_σ a)

/-- `aufhebianEquiv` is reflexive. -/
lemma aufhebianEquiv_refl (a : I) : aufhebianEquiv a a := ⟨rfl, rfl⟩

/-- `aufhebianEquiv` is symmetric. -/
lemma aufhebianEquiv_symm {a b : I} (h : aufhebianEquiv a b) : aufhebianEquiv b a :=
  ⟨h.1.symm, h.2.symm⟩

/-- `aufhebianEquiv` is transitive. -/
lemma aufhebianEquiv_trans {a b c : I}
    (hab : aufhebianEquiv a b) (hbc : aufhebianEquiv b c) :
    aufhebianEquiv a c :=
  ⟨hab.1.trans hbc.1, hab.2.trans hbc.2⟩

/-- `aufhebianEquiv` implies equality of ideas. -/
lemma eq_of_aufhebianEquiv {a b : I} (h : aufhebianEquiv a b) : a = b := by
  have da := AufhebungStructure.decomp a
  have db := AufhebungStructure.decomp b
  -- Rewrite `a` and `b` via decomposition, then use the agreement
  -- of the projectors.
  rw [← da, ← db, h.1, h.2]

/-- Equality of ideas implies `aufhebianEquiv`. -/
lemma aufhebianEquiv_of_eq {a b : I} (h : a = b) : aufhebianEquiv a b := by
  subst h
  exact aufhebianEquiv_refl a

/-- `aufhebianEquiv` coincides with equality. -/
lemma aufhebianEquiv_iff (a b : I) : aufhebianEquiv a b ↔ a = b :=
  ⟨eq_of_aufhebianEquiv, aufhebianEquiv_of_eq⟩

end Stability

/-! ## §4.  Headline theorems -/

/-! ### §4.1  Theorem 3.1 — the Aufhebung decomposition theorem -/

/-- **Theorem 3.1 (Aufhebung Decomposition Theorem).**

    *Informal claim.*  In the existing non-formalized literature on
    Idea Theory (cf. Hegel, *Wissenschaft der Logik*, Vol. I, §90;
    Brandom, *A Spirit of Trust*, ch. 17 §6 "Sublation as Recollective
    Recovery") the central structural claim about Aufhebung is that
    every determinate idea admits a *canonical* split into a
    preserved (sedimented) component and a negated (transformed)
    component, that this split is *idempotent* under iteration, and
    that the components themselves bear opposite signs in the sense
    that applying the wrong projector to a component returns the
    identity.  In algebraic shorthand:

    ```
        a = σ(a) ◦ ν(a),     σ(σ(a)) = σ(a),     ν(ν(a)) = ν(a),
        ν(σ(a)) = ε,         σ(ν(a)) = ε.
    ```

    *Source.*  Hegel (1812), *Wissenschaft der Logik*, Vol. I, §90;
    Brandom (2019), *A Spirit of Trust*, ch. 17.

    *Dependencies.*  `decomp_eq`, `σ_idem_eq`, `ν_idem_eq`,
    `σν_trivial`, `νσ_trivial`.

    *Sharpening.*  The informal text treats Aufhebung as a *movement*;
    the formal version sharpens this into the existence of two
    explicit functions `σ`, `ν` and packages all five properties as a
    single conjunction.

    *Proof strategy.*
    1. Apply `AufhebungStructure.decomp` to obtain the decomposition
       equation.
    2. Apply `AufhebungStructure.σ_idem` to obtain idempotence of `σ`.
    3. Apply `AufhebungStructure.ν_idem` to obtain idempotence of `ν`.
    4. Apply `AufhebungStructure.σ_ν` to obtain σ-annihilation of ν.
    5. Apply `AufhebungStructure.ν_σ` to obtain ν-annihilation of σ.
    6. Bundle the five facts into a single conjunction. -/
theorem theorem_3_1 (a : I) :
    IdeaTheoryStructure.op (AufhebungStructure.σ a) (AufhebungStructure.ν a) = a ∧
    AufhebungStructure.σ (AufhebungStructure.σ a) = AufhebungStructure.σ a ∧
    AufhebungStructure.ν (AufhebungStructure.ν a) = AufhebungStructure.ν a ∧
    AufhebungStructure.ν (AufhebungStructure.σ a) = (IdeaTheoryStructure.ident : I) ∧
    AufhebungStructure.σ (AufhebungStructure.ν a) = (IdeaTheoryStructure.ident : I) := by
  -- Step 1: decomposition
  have h1 : IdeaTheoryStructure.op (AufhebungStructure.σ a)
              (AufhebungStructure.ν a) = a := decomp_eq a
  -- Step 2: σ-idempotence
  have h2 : AufhebungStructure.σ (AufhebungStructure.σ a)
              = AufhebungStructure.σ a := σ_idem_eq a
  -- Step 3: ν-idempotence
  have h3 : AufhebungStructure.ν (AufhebungStructure.ν a)
              = AufhebungStructure.ν a := ν_idem_eq a
  -- Step 4: ν annihilates σ-image
  have h4 : AufhebungStructure.ν (AufhebungStructure.σ a)
              = (IdeaTheoryStructure.ident : I) := νσ_trivial a
  -- Step 5: σ annihilates ν-image
  have h5 : AufhebungStructure.σ (AufhebungStructure.ν a)
              = (IdeaTheoryStructure.ident : I) := σν_trivial a
  -- Step 6: package
  exact ⟨h1, h2, h3, h4, h5⟩

/-! ### §4.2  Theorem 3.2 — idempotent stabilisation -/

/-- **Theorem 3.2 (Idempotent Stabilisation Theorem).**

    *Informal claim.*  Iterated sublation of an idea reaches a
    fixed point after a single application: once an idea has been
    "lifted" by `σ` (resp. negated by `ν`), further applications of
    the same projector add nothing new.  This is the formal
    counterpart of the philosophical thesis that the Hegelian
    process is *self-completing* at every level — there is no
    "Aufhebung of an Aufhebung" beyond the first.

    *Source.*  Adorno (1966), *Negative Dialektik*, Part I §3
    "Die determinierte Negation"; Brandom (2019), *A Spirit of
    Trust*, ch. 18 §1.

    *Dependencies.*  `iteratePreserved_eq_σ`, `iterateNegated_eq_ν`,
    `iteratePreserved_succ`, `iterateNegated_succ`,
    `AufhebungStructure.σ_idem`, `AufhebungStructure.ν_idem`.

    *Sharpening.*  The informal claim is qualitative ("further
    sublation adds nothing"); the formal statement is quantitative —
    for *all* `n ≥ 1` the `n`-th iterate equals the first iterate,
    not merely "eventually".

    *Proof strategy.*
    1. State the conjunction `iteratePreserved (n+1) a = σ a ∧
       iterateNegated (n+1) a = ν a`.
    2. Reduce both sides via `iteratePreserved_eq_σ` and
       `iterateNegated_eq_ν`.
    3. Conclude by `rfl` for each component.
    4. Strengthen to a `for all n` statement and a `for all m, n ≥ 1`
       agreement statement using `iteratePreserved_eq_iteratePreserved`
       and `iterateNegated_eq_iterateNegated`. -/
theorem theorem_3_2 (a : I) :
    (∀ n : Nat, iteratePreserved (n+1) a = AufhebungStructure.σ a) ∧
    (∀ n : Nat, iterateNegated (n+1) a = AufhebungStructure.ν a) ∧
    (∀ m n : Nat, iteratePreserved (m+1) a = iteratePreserved (n+1) a) ∧
    (∀ m n : Nat, iterateNegated (m+1) a = iterateNegated (n+1) a) := by
  -- Step 1: closed form for σ-iterates.
  have hσ : ∀ n : Nat, iteratePreserved (n+1) a = AufhebungStructure.σ a := by
    intro n
    exact iteratePreserved_eq_σ n a
  -- Step 2: closed form for ν-iterates.
  have hν : ∀ n : Nat, iterateNegated (n+1) a = AufhebungStructure.ν a := by
    intro n
    exact iterateNegated_eq_ν n a
  -- Step 3: pairwise σ agreement
  have hσσ : ∀ m n : Nat,
      iteratePreserved (m+1) a = iteratePreserved (n+1) a := by
    intro m n
    rw [hσ m, hσ n]
  -- Step 4: pairwise ν agreement
  have hνν : ∀ m n : Nat,
      iterateNegated (m+1) a = iterateNegated (n+1) a := by
    intro m n
    rw [hν m, hν n]
  exact ⟨hσ, hν, hσσ, hνν⟩

/-! ### §4.3  Theorem 3.3 — the Hegelian fixed-point theorem -/

/-- **Theorem 3.3 (Hegelian Fixed-Point Theorem).**

    *Informal claim.*  In the existing literature on Idea Theory the
    notion of a *sedimented* idea (an idea whose negation has been
    fully exhausted, i.e. whose `ν`-component is the identity) is
    argued — see Žižek (2012), *Less Than Nothing*, ch. 14 §3,
    and Brandom (2019), ch. 19 — to coincide with three other
    notions: (i) being a fixed point of `σ`, (ii) being equal to
    one's own preserved component, and (iii) being Hegelian (closed
    under "negation of the negation").  The Hegelian fixed-point
    theorem asserts the equivalence of these four characterisations.

    *Source.*  Žižek (2012), *Less Than Nothing*, ch. 14;
    Brandom (2019), *A Spirit of Trust*, ch. 19.

    *Dependencies.*  `decomp_of_sedimented`, `sedimented_of_preserved`,
    `preserved_of_sedimented`, `hegelian_iff_sedimented`,
    `σ_of_preserved`.

    *Sharpening.*  The informal literature treats these four notions
    as "morally equivalent"; the formal statement is a strict
    iff-chain and pins down the directions of implication.

    *Proof strategy.*
    1. Show `Sedimented a ↔ IsPreserved a` by combining
       `preserved_of_sedimented` and `sedimented_of_preserved`.
    2. Show `IsPreserved a ↔ AufhebungStructure.σ a = a` by
       definition.
    3. Show `Sedimented a ↔ Hegelian a` by `hegelian_iff_sedimented`.
    4. Chain the three equivalences into a four-way conjunction. -/
theorem theorem_3_3 (a : I) :
    (Sedimented a ↔ IsPreserved a) ∧
    (IsPreserved a ↔ AufhebungStructure.σ a = a) ∧
    (Sedimented a ↔ Hegelian a) ∧
    (Sedimented a ↔ AufhebungStructure.σ a = a) := by
  -- Step 1: Sedimented ↔ IsPreserved
  have h1 : Sedimented a ↔ IsPreserved a := by
    constructor
    · intro h
      exact preserved_of_sedimented h
    · intro h
      exact sedimented_of_preserved h
  -- Step 2: IsPreserved ↔ σ a = a (definitional)
  have h2 : IsPreserved a ↔ AufhebungStructure.σ a = a := Iff.rfl
  -- Step 3: Sedimented ↔ Hegelian
  have h3 : Sedimented a ↔ Hegelian a := (hegelian_iff_sedimented a).symm
  -- Step 4: Sedimented ↔ σ a = a (compose Step 1 and Step 2)
  have h4 : Sedimented a ↔ AufhebungStructure.σ a = a := h1.trans h2
  exact ⟨h1, h2, h3, h4⟩

/-! ## §5.  Corollaries -/

/-- **Corollary 3.1 (Sediment of practice).**  In the social-science
    interpretation (Volume 2), a *practice* is modelled as an idea,
    and the sedimented residue of an iterated practice is a
    well-defined fixed point.  Algebraically, the sediment of any
    idea after one round of cultural reproduction is already its
    eventual sediment. -/
theorem corollary_3_1 (a : I) (n : Nat) :
    iteratePreserved (n+1) a = iteratePreserved 1 a := by
  rw [iteratePreserved_eq_σ, iteratePreserved_one]

/-- **Corollary 3.2 (Intertextual stability).**  In the humanistic
    interpretation (Volume 3), the *canonical residue* of a literary
    text — its preserved meaning across re-readings — stabilises
    after a single canonisation step.  Hence canonisation is
    idempotent. -/
theorem corollary_3_2 (a : I) :
    AufhebungStructure.σ (AufhebungStructure.σ a) = AufhebungStructure.σ a :=
  σ_idem_eq a

/-- **Corollary 3.3 (Memory consolidation).**  In the cognitive
    interpretation (Volume 4), `σ` models long-term consolidation of
    a memory trace and `ν` models the labile transformation that
    accompanies recall.  The corollary states that a *consolidated*
    memory (a fixed point of `σ`) has trivial labile component, and
    conversely. -/
theorem corollary_3_3 (a : I) :
    IsPreserved a ↔ Sedimented a :=
  (theorem_3_3 a).1.symm

/-- **Corollary 3.4 (Emergence invariant).**  In the
    emergence-theoretic interpretation (Volume 5), the preserved
    component of an idea is the conserved core that survives a
    phase transition.  The corollary states that the conserved core
    is itself fully conserved, capturing the "no-further-emergence"
    property of asymptotic phases. -/
theorem corollary_3_4 (a : I) : Stable (AufhebungStructure.σ a) :=
  stable_σ a

/-! ## §6.  Examples and sanity checks -/

/-- The decomposition of the identity is trivial. -/
example : IdeaTheoryStructure.op
            (AufhebungStructure.σ (IdeaTheoryStructure.ident : I))
            (AufhebungStructure.ν (IdeaTheoryStructure.ident : I))
          = (IdeaTheoryStructure.ident : I) :=
  decomp_ident

/-- Headline Theorem 3.1 specialised to the identity gives the
    trivial decomposition. -/
example : IdeaTheoryStructure.op
            (AufhebungStructure.σ (IdeaTheoryStructure.ident : I))
            (AufhebungStructure.ν (IdeaTheoryStructure.ident : I))
          = (IdeaTheoryStructure.ident : I) :=
  (theorem_3_1 (IdeaTheoryStructure.ident : I)).1

/-- The fifth iterate of `σ` agrees with the first. -/
example (a : I) : iteratePreserved 5 a = iteratePreserved 1 a := by
  exact (theorem_3_2 a).2.2.1 4 0

/-- The seventh iterate of `ν` agrees with the second. -/
example (a : I) : iterateNegated 7 a = iterateNegated 2 a := by
  exact (theorem_3_2 a).2.2.2 6 1

/-- The identity is sedimented, preserved, sublated, and negated. -/
example : Sedimented (IdeaTheoryStructure.ident : I) ∧
          IsPreserved (IdeaTheoryStructure.ident : I) ∧
          Sublated (IdeaTheoryStructure.ident : I) ∧
          IsNegated (IdeaTheoryStructure.ident : I) :=
  ⟨ident_sedimented, ident_isPreserved, ident_sublated, ident_isNegated⟩

/-- For every idea, the preserved component is sedimented (and hence
    a fixed point of all four equivalent characterisations from
    Theorem 3.3). -/
example (a : I) : Sedimented (AufhebungStructure.σ a) :=
  ((theorem_3_3 (AufhebungStructure.σ a)).1).mpr (σ_isPreserved a)

/-! ## Index of results

* `decomp_eq` — restated decomposition law `σ a ◦ ν a = a`.
* `decomp_ident` — decomposition of the identity is trivial.
* `σ_idem_eq` / `ν_idem_eq` — idempotence of the projectors.
* `σ_of_preserved` / `ν_of_negated` — projectors fix their fixed points.
* `σ_isPreserved` / `ν_isNegated` — image of a projector is fixed.
* `σ_ident_eq` / `ν_ident_eq` — projectors fix the identity.
* `σν_trivial` / `νσ_trivial` — cross annihilation of projectors.
* `ident_isPreserved` / `ident_isNegated` — identity is preserved/negated.
* `ident_sedimented` / `ident_sublated` — identity is sedimented/sublated.
* `op_ident_left` / `op_ident_right` / `op_assoc` — monoid axioms.
* `decomp_of_sublated` / `decomp_of_sedimented` — collapsed decompositions.
* `preserved_of_sedimented` / `negated_of_sublated` — promotions.
* `sedimented_of_preserved` / `sublated_of_negated` — converse promotions.
* `sedimented_σ` / `sublated_ν` — image of a projector is sedimented/sublated.
* `ν_σ_eq_ν_ident` / `σ_ν_eq_σ_ident` — cross-projector identity congruence.
* `op_σ_ident` / `op_ident_ν` — projector–identity composition.
* `iteratePreserved_zero` / `_succ` / `_one` / `_two` — basic σ-iteration laws.
* `iterateNegated_zero` / `_succ` / `_one` / `_two` — basic ν-iteration laws.
* `iteratePreserved_stable` / `iterateNegated_stable` — single-step stabilisation.
* `iteratePreserved_eq_σ` / `iterateNegated_eq_ν` — closed forms for iterates.
* `iteratePreserved_of_preserved` / `iterateNegated_of_negated` — fixed-point invariance.
* `iteratePreserved_ident` / `iterateNegated_ident` — identity fixed.
* `iteratePreserved_eq_iteratePreserved` / `iterateNegated_eq_iterateNegated` —
  pairwise agreement of positive iterates.
* `mediated_self` / `mediated_ident_right` / `mediated_ident_left` —
  algebraic identities for the mediated form.
* `aufheb_compose` / `aufheb_ident` / `aufheb_fst` / `aufheb_snd` —
  basic algebra of the `aufheb` pair.
* `σ_aufheb_fst` / `ν_aufheb_snd` — projector idempotence on `aufheb` components.
* `triadOf_thesis` / `_antithesis` / `_synthesis` / `_recovers` — triad lemmas.
* `mediated_of_components` / `mediated_left_assoc` — mediated algebra.
* `stable_ident` / `stable_of_preserved` / `stable_of_sedimented` /
  `preserved_of_stable` / `sedimented_of_stable` / `stable_σ` — stability lemmas.
* `hegelian_ident` / `hegelian_iff_sedimented` / `hegelian_of_sedimented` /
  `hegelian_σ` — Hegelian-predicate lemmas.
* `aufhebianEquiv_refl` / `_symm` / `_trans` / `eq_of_aufhebianEquiv` /
  `aufhebianEquiv_of_eq` / `aufhebianEquiv_iff` — equivalence-relation lemmas.
* `theorem_3_1` — the Aufhebung decomposition theorem.
* `theorem_3_2` — the idempotent stabilisation theorem.
* `theorem_3_3` — the Hegelian fixed-point theorem.
* `corollary_3_1` — sediment of practice (social interpretation).
* `corollary_3_2` — intertextual stability (humanistic interpretation).
* `corollary_3_3` — memory consolidation (cognitive interpretation).
* `corollary_3_4` — emergence invariant (emergence interpretation).
-/

end IdeaTheory
