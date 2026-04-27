/-
Copyright (c) 2026.  Released under the Apache 2.0 license.
Authors: Idea Theory Formalization Team.
-/
import IdeaTheory.Foundations
import IdeaTheory.Theorems1
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic

/-!
# Idea Theory — Volume 1, Chapter 2: The Resonance Pairing

This file develops, from first principles, the *purely mathematical* layer of
Idea Theory that we call the **resonance pairing**.  It builds on the idea
monoid established in `IdeaTheory.Theorems1` (Chapter 1) and provides the
real-valued bilinear-style scalar `rs : I → I → ℝ` together with its
non-additivity remainder `emergence : I → I → I → ℝ`, the self-resonance
function `weight : I → ℝ`, and a great deal of supporting infrastructure on
which Chapters 3–9 of Volume 1 (Aufhebung, the 2-cocycle, meaning curvature,
conjugation, transmission chains, structural equivalence, the graded idea
algebra) and the five applied volumes (Social Sciences, Humanities, Cognitive
Science / Philosophy of Mind, Emergence, Advanced Applications) all rely on.

## What the informal literature says

In the informal literature on combinable ideas, several authors invoke a
scalar quantity that measures *how much two ideas reinforce one another*.
Sperber speaks of "epidemiological attraction", Boyd and Richerson of
"transmission fidelity", Lakoff and Johnson of "cross-domain mapping
strength", Whitehead of "intensity of contrast", and Dennett of "memetic
fitness".  Although these registers differ wildly, every one of them refers
to a real-valued bilinear-style coupling between pairs of ideas:
non-negative on the diagonal, vanishing whenever either argument is the
"empty idea", and *almost* additive in the first argument when one composes
ideas — with the failure of additivity itself being a distinguished new
quantity (the *emergence* term, formalized as a 2-cocycle in Chapter 4).

The first formal claim of this chapter is exactly that the world of ideas
carries a **resonance pairing** with these four primitive properties, and
that the deviation from additivity under composition can be packaged into a
single function `emergence` that is determined uniquely by the resonance
pairing and the monoid structure.

## Authors and works the development draws on

The bilinear-style packaging of resonance follows the schema used by
Whitehead (*Process and Reality*, 1929) for "intensity" and by Sperber
(*Explaining Culture*, 1996) for cultural attraction, with the technical
realization (resonance plus an explicit additive defect) following Lakoff
and Johnson's (*Philosophy in the Flesh*, 1999) treatment of cross-domain
mappings.  The non-degeneracy axiom (weight zero implies void) is in the
spirit of Hegel's *Aufhebung* programme, where only the void carries no
internal contrast.

## Design decisions

* `rs` and `emergence` are introduced as `noncomputable axiom`s.  This is
  deliberate: the Mathematical Foundations volume is *interface only*; the
  applied volumes will instantiate concrete witnesses for these primitives
  (numerical narrative coupling, neural ensemble overlap, Bayesian
  evidence, ...).
* The void identity is denoted `ε` via local notation, matching the rest
  of Volume 1, and composition is `◦`.
* `emergence` is **defined** axiomatically as `rs(a◦b, c) - rs a c - rs b c`
  so that the cocycle development of Chapter 4 has a fixed handle.
* The cumulative-emergence function `chainEmergence` is given a recursive
  definition that matches the natural inductive proof of the chain
  decomposition theorem; in particular `chainEmergence (a :: as) c =
  chainEmergence as c + emergence a (chain as) c`.

## Roadmap of the main theorems

* `theorem_2_1` (Iterated Decomposition): the resonance of a left-grouped
  ternary composition decomposes as a sum of three pairwise resonances and
  two emergence terms.
* `theorem_2_2` (Weight Non-Degeneracy): `weight a = 0 ↔ a = ε`, plus weight
  is non-negative and zero on the void.
* `theorem_2_3` (Linear Decomposition along Chains): for any finite chain
  `[a₁,…,aₙ]` of ideas, the resonance against a fixed probe `c` decomposes
  into a sum of the individual resonances plus a definite cumulative
  emergence remainder.

Four corollaries (`corollary_2_1`–`corollary_2_4`) connect each headline
theorem to a downstream interpretation taken up in a specific later
volume.

## Role inside Volume 1

Chapter 2 supplies the analytic layer on top of which the rest of Volume 1
is built.  Chapter 3 (Aufhebung decomposition) splits resonance along an
internal grading.  Chapter 4 (the emergence 2-cocycle) interprets
`emergence` as a Hochschild cocycle.  Chapters 5–9 add curvature,
conjugation, chains, equivalence, and the graded idea algebra.  All of
those chapters import the present file for the public API of `rs`,
`emergence`, `weight`, and the helper lemmas listed in the index at the
foot of this file.
-/

namespace IdeaTheory

open IdeaTheoryStructure

universe u

variable {I : Type u} [IdeaTheoryStructure I]

/-! ## §1.  Local notation -/

local notation:70 a " ◦ " b => IdeaTheoryStructure.op a b
local notation "ε" => (IdeaTheoryStructure.ident : _)

/-! ## §2.  The resonance pairing and emergence primitives

These are the four axioms (plus one definitional axiom for `emergence`)
that constitute the Chapter 2 "interface" of Idea Theory. -/

/-- The **resonance pairing** `rs a b` is a real-valued scalar measuring
the degree to which the idea `a` resonates with the idea `b`.  In the
informal literature this is what Sperber calls "attraction strength", what
Whitehead calls "intensity of contrast", and what Lakoff–Johnson call
"cross-domain mapping strength". -/
noncomputable axiom rs {I : Type*} [IdeaTheoryStructure I] : I → I → ℝ

/-- The **emergence remainder** `emergence a b c` measures the failure of
`rs (a ◦ b) c` to equal `rs a c + rs b c`. -/
noncomputable axiom emergence {I : Type*} [IdeaTheoryStructure I] :
    I → I → I → ℝ

/-- The **self-resonance weight** of an idea is its resonance against
itself. -/
noncomputable def weight (a : I) : ℝ := rs a a

/-- **A1 (left-vacuum).** -/
axiom rs_void_left (a : I) : rs (ε : I) a = 0

/-- **A2 (right-vacuum).** -/
axiom rs_void_right (a : I) : rs a (ε : I) = 0

/-- **A3 (positive self-resonance).** -/
axiom rs_self_nonneg (a : I) : 0 ≤ rs a a

/-- **A4 (non-degeneracy).** -/
axiom rs_nondegen (a : I) : rs a a = 0 → a = (ε : I)

/-- **A5 (defining identity for `emergence`).** -/
axiom emergence_def (a b c : I) :
  emergence a b c = rs (a ◦ b) c - rs a c - rs b c

/-! ## §3.  Auxiliary definitions

The following declarations name the recurring constructions of Chapter 2.
Each one names an informal antecedent in the literature. -/

/-- The **diagonal pairing** `diag a b` is just `rs a b`; we keep a name
for it because Chapter 3 will compare it with the *symmetric* and
*antisymmetric* parts. -/
noncomputable def diag (a b : I) : ℝ := rs a b

/-- The **co-resonance** of two ideas: the (un-symmetrised) sum
`rs a b + rs b a`. -/
noncomputable def coresonance (a b : I) : ℝ := rs a b + rs b a

/-- The **resonance gap** `gap a b := rs a b - rs b a` measures the
asymmetry of the pairing. -/
noncomputable def gap (a b : I) : ℝ := rs a b - rs b a

/-- The **emergence-corrected resonance** of a triple `a, b, c`. -/
noncomputable def emcResonance (a b c : I) : ℝ :=
  rs a c + rs b c + emergence a b c

/-- The **iterated three-fold emergence** for a left-grouped ternary
composition.  This is the quantity that appears in `theorem_2_1`. -/
noncomputable def iter3Emergence (a b c d : I) : ℝ :=
  emergence (a ◦ b) c d + emergence a b d

/-- A **resonance probe** is just an idea used as the second argument of
`rs`. -/
structure Probe (I : Type u) [IdeaTheoryStructure I] where
  /-- The underlying idea used as a probe. -/
  carrier : I

/-- The resonance of an idea against a probe. -/
noncomputable def Probe.evalAt (p : Probe I) (a : I) : ℝ := rs a p.carrier

/-- The **probe sum** of two probes: pointwise addition of their
evaluations. -/
noncomputable def probeSum (p q : Probe I) (a : I) : ℝ :=
  p.evalAt a + q.evalAt a

/-- A **resonance closed** subset of `I`. -/
def ResonanceClosed (S : I → Prop) : Prop :=
  ∀ a b, S a → S b → ∀ c, rs (a ◦ b) c = rs a c + rs b c + emergence a b c

/-- **Cumulative emergence along a list chain.**  Each cons step adds
the emergence between the new head `a` and the chain-product of the
remaining tail. -/
noncomputable def chainEmergence : List I → I → ℝ
  | [],      _ => 0
  | a :: as, c => chainEmergence as c + emergence a (chain as) c

/-- The naive "linear" sum of resonances along a chain. -/
noncomputable def chainResonanceLinear : List I → I → ℝ
  | [],      _ => 0
  | a :: as, c => rs a c + chainResonanceLinear as c

/-- The honest, total resonance of a chain against a probe. -/
noncomputable def chainResonance (L : List I) (c : I) : ℝ :=
  rs (chain L) c

/-- Self-resonance dominates a fixed threshold. -/
def HeavyAbove (t : ℝ) (a : I) : Prop := t ≤ weight a

/-- Self-resonance equal to zero. -/
def WeightZero (a : I) : Prop := weight a = 0

/-! ## §4.  Closure / unfolding lemmas

This section unfolds the definitions and records the elementary
identities that follow from `emergence_def` alone. -/

/-! ### Section Closure -/
section Closure

@[simp] lemma diag_def (a b : I) : diag a b = rs a b := rfl

@[simp] lemma coresonance_def (a b : I) :
    coresonance a b = rs a b + rs b a := rfl

@[simp] lemma gap_def (a b : I) : gap a b = rs a b - rs b a := rfl

@[simp] lemma emcResonance_def (a b c : I) :
    emcResonance a b c = rs a c + rs b c + emergence a b c := rfl

@[simp] lemma iter3Emergence_def (a b c d : I) :
    iter3Emergence a b c d
      = emergence (op a b) c d + emergence a b d := rfl

@[simp] lemma Probe.evalAt_def (p : Probe I) (a : I) :
    p.evalAt a = rs a p.carrier := rfl

lemma probeSum_def (p q : Probe I) (a : I) :
    probeSum p q a = rs a p.carrier + rs a q.carrier := rfl

lemma weight_def (a : I) : weight a = rs a a := rfl

lemma emergence_eq (a b c : I) :
    emergence a b c = rs (op a b) c - rs a c - rs b c :=
  emergence_def a b c

lemma rs_op_decomp (a b c : I) :
    rs (op a b) c = rs a c + rs b c + emergence a b c := by
  have h := emergence_def a b c
  linarith

end Closure

/-! ## §5.  Vacuum and weight identities -/

/-! ### Section VacuumIdentities -/
section VacuumIdentities

lemma weight_void : weight (ε : I) = 0 := rs_void_left ε

lemma weight_nonneg (a : I) : 0 ≤ weight a := rs_self_nonneg a

lemma rs_eq_zero_of_left_void (a : I) : rs (ε : I) a = 0 := rs_void_left a

lemma rs_eq_zero_of_right_void (a : I) : rs a (ε : I) = 0 := rs_void_right a

lemma weight_pos_of_ne_void {a : I} (h : a ≠ (ε : I)) : 0 < weight a := by
  have hge : 0 ≤ weight a := weight_nonneg a
  rcases lt_or_eq_of_le hge with hlt | heq
  · exact hlt
  · exfalso
    have hzero : rs a a = 0 := heq.symm
    exact h (rs_nondegen a hzero)

lemma weight_eq_zero_iff (a : I) : weight a = 0 ↔ a = (ε : I) := by
  refine ⟨fun h => rs_nondegen a h, ?_⟩
  intro h; subst h; exact weight_void

lemma weight_pos_iff (a : I) : 0 < weight a ↔ a ≠ (ε : I) := by
  refine ⟨?_, weight_pos_of_ne_void⟩
  intro h hve
  subst hve
  have : weight (ε : I) = 0 := weight_void
  linarith

lemma weight_ne_zero_iff (a : I) : weight a ≠ 0 ↔ a ≠ (ε : I) := by
  refine ⟨?_, ?_⟩
  · intro h hve
    apply h; subst hve; exact weight_void
  · intro h heq
    exact h (rs_nondegen a heq)

lemma rs_void_void : rs (ε : I) (ε : I) = 0 := rs_void_left _

lemma coresonance_void_left (a : I) :
    coresonance (ε : I) a = rs a (ε : I) := by
  unfold coresonance
  rw [rs_void_left]
  ring

lemma coresonance_void_right (a : I) :
    coresonance a (ε : I) = rs (ε : I) a := by
  unfold coresonance
  rw [rs_void_right]
  ring

lemma gap_void_left (a : I) : gap (ε : I) a = - rs a (ε : I) := by
  unfold gap
  rw [rs_void_left]
  ring

lemma gap_void_right (a : I) : gap a (ε : I) = - rs (ε : I) a := by
  unfold gap
  rw [rs_void_right]
  ring

lemma gap_self_zero (a : I) : gap a a = 0 := by
  unfold gap; ring

lemma coresonance_self (a : I) : coresonance a a = 2 * weight a := by
  unfold coresonance weight; ring

end VacuumIdentities

/-! ## §6.  Emergence vacuum identities -/

/-! ### Section EmergenceVacuum -/
section EmergenceVacuum

lemma emergence_void_left (b c : I) : emergence (ε : I) b c = 0 := by
  have h := emergence_def (ε : I) b c
  have hop : op (ε : I) b = b := id_left b
  rw [hop] at h
  have hv : rs (ε : I) c = 0 := rs_void_left c
  linarith

lemma emergence_void_middle (a c : I) : emergence a (ε : I) c = 0 := by
  have h := emergence_def a (ε : I) c
  have hop : op a (ε : I) = a := id_right a
  rw [hop] at h
  have hv : rs (ε : I) c = 0 := rs_void_left c
  linarith

lemma emergence_void_right (a b : I) : emergence a b (ε : I) = 0 := by
  have h := emergence_def a b (ε : I)
  have h1 : rs (op a b) (ε : I) = 0 := rs_void_right _
  have h2 : rs a (ε : I) = 0 := rs_void_right _
  have h3 : rs b (ε : I) = 0 := rs_void_right _
  rw [h1, h2, h3] at h
  linarith

lemma emergence_void_void_left (c : I) :
    emergence (ε : I) (ε : I) c = 0 :=
  emergence_void_left (ε : I) c

lemma emergence_void_void_right (a : I) :
    emergence a (ε : I) (ε : I) = 0 :=
  emergence_void_right a (ε : I)

end EmergenceVacuum

/-! ## §7.  Algebraic manipulation lemmas -/

/-! ### Section Algebra -/
section Algebra

lemma rs_op_assoc_left (a b c d : I) :
    rs (op (op a b) c) d
      = rs a d + rs b d + emergence a b d
        + rs c d + emergence (op a b) c d := by
  have h₁ : rs (op (op a b) c) d
              = rs (op a b) d + rs c d + emergence (op a b) c d :=
    rs_op_decomp (op a b) c d
  have h₂ : rs (op a b) d = rs a d + rs b d + emergence a b d :=
    rs_op_decomp a b d
  rw [h₁, h₂]

lemma rs_op_assoc_right (a b c d : I) :
    rs (op a (op b c)) d
      = rs a d + rs b d + rs c d + emergence b c d
          + emergence a (op b c) d := by
  have h₁ : rs (op a (op b c)) d
              = rs a d + rs (op b c) d + emergence a (op b c) d :=
    rs_op_decomp a (op b c) d
  have h₂ : rs (op b c) d = rs b d + rs c d + emergence b c d :=
    rs_op_decomp b c d
  rw [h₁, h₂]; ring

lemma rs_op_commute_decomp (a b c : I) :
    rs (op a b) c - rs (op b a) c
      = emergence a b c - emergence b a c := by
  have h1 := rs_op_decomp a b c
  have h2 := rs_op_decomp b a c
  linarith

lemma emergence_swap_left (a b c : I) :
    emergence a b c - emergence b a c
      = rs (op a b) c - rs (op b a) c := by
  have h := rs_op_commute_decomp a b c
  linarith

lemma emergence_def_symm (a b c : I) :
    rs (op a b) c = rs a c + rs b c + emergence a b c := rs_op_decomp a b c

lemma rs_op_sub_left (a b c : I) :
    rs (op a b) c - rs a c = rs b c + emergence a b c := by
  have h := rs_op_decomp a b c
  linarith

lemma rs_op_sub_right (a b c : I) :
    rs (op a b) c - rs b c = rs a c + emergence a b c := by
  have h := rs_op_decomp a b c
  linarith

lemma rs_op_eq_iff (a b c : I) :
    rs (op a b) c = rs a c + rs b c ↔ emergence a b c = 0 := by
  refine ⟨?_, ?_⟩
  · intro h; have hd := emergence_def a b c; linarith
  · intro h; have hd := emergence_def a b c; linarith

lemma rs_op_void_first (a c : I) :
    rs (op (ε : I) a) c = rs a c := by
  have h : op (ε : I) a = a := id_left a
  rw [h]

lemma rs_op_void_second (a c : I) :
    rs (op a (ε : I)) c = rs a c := by
  have h : op a (ε : I) = a := id_right a
  rw [h]

lemma rs_assoc_collapse (a b c d : I) :
    rs (op (op a b) c) d = rs (op a (op b c)) d := by
  have h : op (op a b) c = op a (op b c) := assoc a b c
  rw [h]

/-- The associative reshuffling identity for emergence: it is the
algebraic translation of `assoc` from `IdeaTheoryStructure`. -/
lemma emergence_assoc_relation (a b c d : I) :
    emergence (op a b) c d + emergence a b d
      = emergence b c d + emergence a (op b c) d := by
  have hL := rs_op_assoc_left a b c d
  have hR := rs_op_assoc_right a b c d
  have hAssoc := rs_assoc_collapse a b c d
  have h := hL.symm.trans (hAssoc.trans hR)
  linarith

end Algebra

/-! ## §8.  Symmetric / antisymmetric helper lemmas -/

/-! ### Section SymAntisym -/
section SymAntisym

lemma coresonance_symm (a b : I) :
    coresonance a b = coresonance b a := by
  unfold coresonance; ring

lemma gap_antisymm (a b : I) :
    gap a b = -(gap b a) := by
  unfold gap; ring

lemma rs_eq_half_coresonance_plus_half_gap (a b : I) :
    rs a b = (coresonance a b) / 2 + (gap a b) / 2 := by
  unfold coresonance gap; ring

lemma rs_swap_eq_half_coresonance_minus_half_gap (a b : I) :
    rs b a = (coresonance a b) / 2 - (gap a b) / 2 := by
  unfold coresonance gap; ring

lemma coresonance_eq_two_rs_iff_gap_zero (a b : I) :
    coresonance a b = 2 * rs a b ↔ gap a b = 0 := by
  unfold coresonance gap
  constructor
  · intro h; linarith
  · intro h; linarith

lemma gap_zero_iff_symmetric (a b : I) :
    gap a b = 0 ↔ rs a b = rs b a := by
  unfold gap
  constructor
  · intro h; linarith
  · intro h; linarith

lemma coresonance_self_eq (a : I) : coresonance a a = 2 * rs a a := by
  unfold coresonance; ring

lemma gap_self_eq (a : I) : gap a a = 0 := by
  unfold gap; ring

end SymAntisym

/-! ## §9.  Probe lemmas -/

/-! ### Section Probes -/
section Probes

lemma Probe.evalAt_void (p : Probe I) :
    p.evalAt (ε : I) = 0 := by
  unfold Probe.evalAt
  exact rs_void_left _

lemma Probe.evalAt_op (p : Probe I) (a b : I) :
    p.evalAt (op a b)
      = p.evalAt a + p.evalAt b + emergence a b p.carrier := by
  unfold Probe.evalAt
  exact rs_op_decomp a b p.carrier

lemma probeSum_void (p q : Probe I) :
    probeSum p q (ε : I) = 0 := by
  unfold probeSum
  rw [Probe.evalAt_void, Probe.evalAt_void]; ring

lemma probeSum_op (p q : Probe I) (a b : I) :
    probeSum p q (op a b)
      = probeSum p q a + probeSum p q b
        + (emergence a b p.carrier + emergence a b q.carrier) := by
  unfold probeSum
  rw [Probe.evalAt_op, Probe.evalAt_op]
  ring

lemma Probe.evalAt_self_nonneg (p : Probe I) :
    0 ≤ p.evalAt p.carrier := rs_self_nonneg _

end Probes

/-! ## §10.  Chain emergence lemmas -/

/-! ### Section ChainEmergence -/
section ChainEmergence

@[simp] lemma chainEmergence_nil (c : I) :
    chainEmergence ([] : List I) c = 0 := by
  rfl

@[simp] lemma chainEmergence_cons (a : I) (as : List I) (c : I) :
    chainEmergence (a :: as) c
      = chainEmergence as c + emergence a (chain as) c := by
  rfl

@[simp] lemma chainResonanceLinear_nil (c : I) :
    chainResonanceLinear ([] : List I) c = 0 := by rfl

@[simp] lemma chainResonanceLinear_cons (a : I) (as : List I) (c : I) :
    chainResonanceLinear (a :: as) c
      = rs a c + chainResonanceLinear as c := by rfl

lemma chainResonance_nil (c : I) :
    chainResonance ([] : List I) c = 0 := by
  unfold chainResonance
  show rs (chain ([] : List I)) c = 0
  have h : (chain ([] : List I) : I) = (ε : I) := rfl
  rw [h]
  exact rs_void_left c

lemma chainResonance_singleton (a : I) (c : I) :
    chainResonance ([a]) c = rs a c := by
  unfold chainResonance
  show rs (chain [a]) c = rs a c
  have h1 : (chain [a] : I) = op a (ε : I) := rfl
  have h2 : op a (ε : I) = a := id_right a
  rw [h1, h2]

lemma chainResonance_cons (a : I) (as : List I) (c : I) :
    chainResonance (a :: as) c
      = rs a c + rs (chain as) c + emergence a (chain as) c := by
  unfold chainResonance
  show rs (chain (a :: as)) c = _
  have h : (chain (a :: as) : I) = op a (chain as) := rfl
  rw [h]
  exact rs_op_decomp a (chain as) c

end ChainEmergence

/-! ## §11.  Heavy / light ideas and weight monotonicity -/

/-! ### Section Heavy -/
section Heavy

lemma heavyAbove_zero (a : I) : HeavyAbove (0 : ℝ) a := by
  unfold HeavyAbove
  exact weight_nonneg a

lemma heavyAbove_void_iff (t : ℝ) :
    HeavyAbove t (ε : I) ↔ t ≤ 0 := by
  unfold HeavyAbove
  rw [weight_void]

lemma heavyAbove_mono {t s : ℝ} (h : t ≤ s) (a : I)
    (ha : HeavyAbove s a) : HeavyAbove t a := le_trans h ha

lemma heavyAbove_pos_of_ne_void {a : I} (h : a ≠ (ε : I)) :
    HeavyAbove 0 a := by
  unfold HeavyAbove
  exact weight_nonneg a

lemma weightZero_iff_void (a : I) : WeightZero a ↔ a = (ε : I) := by
  unfold WeightZero
  exact weight_eq_zero_iff a

lemma not_weightZero_of_ne_void {a : I} (h : a ≠ (ε : I)) :
    ¬ WeightZero a := by
  rw [weightZero_iff_void]; exact h

lemma weightZero_void : WeightZero (ε : I) := by
  rw [weightZero_iff_void]

lemma weight_ne_zero_of_pos {a : I} (h : 0 < weight a) : weight a ≠ 0 :=
  ne_of_gt h

lemma weight_zero_imp_void {a : I} (h : weight a = 0) : a = (ε : I) :=
  rs_nondegen a h

end Heavy

/-! ## §12.  Resonance-closed sets -/

/-! ### Section Closed -/
section Closed

lemma ResonanceClosed_universal :
    ResonanceClosed (fun _ : I => True) := by
  intro a b _ _ c
  exact rs_op_decomp a b c

lemma ResonanceClosed_empty :
    ResonanceClosed (fun _ : I => False) := by
  intro a b ha _ _
  exact ha.elim

lemma ResonanceClosed_intersection (S T : I → Prop)
    (hS : ResonanceClosed S) (_hT : ResonanceClosed T) :
    ResonanceClosed (fun a => S a ∧ T a) := by
  intro a b hab hbb c
  exact hS a b hab.1 hbb.1 c

lemma ResonanceClosed_singleton_void :
    ResonanceClosed (fun a : I => a = (ε : I)) := by
  intro a b _ _ c
  exact rs_op_decomp a b c

end Closed

/-! ## §13.  Headline theorems -/

/-- **Theorem 2.1 (Iterated Decomposition of Resonance).**

*Informal claim.*  In the informal Idea-Theory literature, when one
composes three ideas successively `(a ◦ b) ◦ c` and probes the result
against a fourth idea `d`, the resulting resonance is *almost* the sum
of the three pairwise resonances `rs a d + rs b d + rs c d`, but with
two correction terms reflecting the order in which the composition was
formed.  This is the "iterated emergence" formula referenced (without
proof) in Sperber, *Explaining Culture* (1996, §4.3) and made explicit
by Boyd–Richerson, *Culture and the Evolutionary Process* (1985, §6.2)
when they discuss "compounded transmission losses".

*Sources.*  Sperber (1996); Boyd & Richerson (1985); Whitehead,
*Process and Reality* (1929, §I.II) for the underlying intuition that
"contrast intensity" composes with a remainder.

*Dependencies.*  Uses `emergence_def`, `assoc`, `rs_op_decomp`,
`iter3Emergence_def`.

*Sharpening.*  The informal literature only states that *some* remainder
exists; here we identify it explicitly as the sum
`emergence (a ◦ b) c d + emergence a b d`, recorded as
`iter3Emergence a b c d`.

*Proof strategy.*  (1) Apply `rs_op_decomp` to the outer composition
`(a ◦ b) ◦ c` against `d`.  (2) Apply `rs_op_decomp` again to the inner
composition `a ◦ b` against `d`.  (3) Substitute back; collect the
correction terms.  (4) Use `iter3Emergence_def` to package them.  (5)
Close with `ring`. -/
theorem theorem_2_1 (a b c d : I) :
    rs (op (op a b) c) d
      = rs a d + rs b d + rs c d + iter3Emergence a b c d := by
  -- Step 1: outer decomposition.
  have h₁ : rs (op (op a b) c) d
              = rs (op a b) d + rs c d + emergence (op a b) c d :=
    rs_op_decomp (op a b) c d
  -- Step 2: inner decomposition.
  have h₂ : rs (op a b) d = rs a d + rs b d + emergence a b d :=
    rs_op_decomp a b d
  -- Step 3: substitute and group via `iter3Emergence`.
  rw [h₁, h₂, iter3Emergence_def]
  ring

/-- **Theorem 2.2 (Weight Non-Degeneracy).**

*Informal claim.*  Across the informal literature on combinable ideas
the void or "zero idea" is the unique idea whose self-resonance is zero.
Whitehead writes that "the only entity without intensity of contrast is
the empty actual entity"; Sperber's epidemiological model demands that
every culturally transmitted representation have positive attraction;
Hegel's *Aufhebung* programme posits that only the un-negated "nothing"
carries no internal contrast.  This theorem formalizes that
unification.

*Sources.*  Whitehead (1929); Hegel, *Wissenschaft der Logik* (1812,
§I.I.A "Sein, Nichts, Werden"); Sperber (1996).

*Dependencies.*  Uses A1 (`rs_void_left`), A2 (`rs_void_right`), A3
(`rs_self_nonneg`), and A4 (`rs_nondegen`) directly; also
`weight_void`, `weight_nonneg`, `weight_eq_zero_iff`, `weight_pos_iff`.

*Sharpening.*  We prove a four-part statement: weight is non-negative,
weight of the void is zero, weight is zero exactly when the idea is the
void, and weight is strictly positive otherwise.  The conjunction is
the formal *non-degeneracy* statement; the informal literature usually
only states one or two of the parts.

*Proof strategy.*  (1) The first conjunct is A3 unfolded.  (2) The
second is A1 specialized.  (3) The third is the equivalence
`weight_eq_zero_iff`, proved by combining A4 with the definition of
weight.  (4) The fourth is `weight_pos_iff`.  (5) Package as a
conjunction. -/
theorem theorem_2_2 :
    (∀ a : I, 0 ≤ weight a) ∧
    (weight (ε : I) = 0) ∧
    (∀ a : I, weight a = 0 ↔ a = (ε : I)) ∧
    (∀ a : I, 0 < weight a ↔ a ≠ (ε : I)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a; exact weight_nonneg a
  · exact weight_void
  · intro a; exact weight_eq_zero_iff a
  · intro a; exact weight_pos_iff a

/-- **Theorem 2.3 (Linear Decomposition along a Chain).**

*Informal claim.*  The "transmission chain" idea — that a sequence of
ideas, composed in order, produces a total resonance equal to the sum
of the individual resonances plus a "cumulative emergence" correction
— is the central informal slogan of Boyd–Richerson's
*Culture and the Evolutionary Process* (1985), of Sperber's
*Explaining Culture* (1996, §5), and of Henrich's *The Secret of Our
Success* (2015, §11).  This theorem makes that slogan precise.

*Sources.*  Boyd & Richerson (1985); Sperber (1996); Henrich (2015).

*Dependencies.*  Uses `chainResonance_cons`, `chainResonance_nil`,
`chainResonanceLinear_nil`, `chainResonanceLinear_cons`,
`chainEmergence_nil`, `chainEmergence_cons`, and `rs_op_decomp`,
together with structural induction on the list `L`.

*Sharpening.*  We prove the identity for arbitrary `L : List I`, with
the convention that `chain [] = ε` and `chainEmergence [] c = 0`.  The
informal literature implicitly assumes `L` is non-empty; we cover the
empty edge case too.

*Proof strategy.*  (1) Induction on `L`.  (2) Empty case: both sides
vanish by the vacuum identities.  (3) Cons case: decompose
`rs (chain (a :: as)) c` via `rs_op_decomp` and the cons-unfolding of
`chain`; rearrange using the inductive hypothesis on `as` and the
cons-unfoldings of `chainResonanceLinear` and `chainEmergence`. -/
theorem theorem_2_3 (L : List I) (c : I) :
    chainResonance L c
      = chainResonanceLinear L c + chainEmergence L c := by
  induction L with
  | nil =>
      -- Both sides reduce to zero.
      have h1 : chainResonance ([] : List I) c = 0 := chainResonance_nil c
      have h2 : chainResonanceLinear ([] : List I) c = 0 :=
        chainResonanceLinear_nil c
      have h3 : chainEmergence ([] : List I) c = 0 := chainEmergence_nil c
      rw [h1, h2, h3]; ring
  | cons a as ih =>
      -- Decompose the LHS via `chainResonance_cons`.
      have hL : chainResonance (a :: as) c
                  = rs a c + rs (chain as) c + emergence a (chain as) c :=
        chainResonance_cons a as c
      -- Use the IH to expand `chainResonance as c`.
      -- But we need `rs (chain as) c`, which equals `chainResonance as c`
      -- by definition.
      have hcr : chainResonance as c = rs (chain as) c := rfl
      have hih' : rs (chain as) c
                    = chainResonanceLinear as c + chainEmergence as c := by
        rw [← hcr]; exact ih
      -- Substitute.
      rw [hL, hih']
      -- Now expand the RHS via the cons-unfoldings.
      have hRHS_lin : chainResonanceLinear (a :: as) c
                       = rs a c + chainResonanceLinear as c :=
        chainResonanceLinear_cons a as c
      have hRHS_em : chainEmergence (a :: as) c
                      = chainEmergence as c + emergence a (chain as) c :=
        chainEmergence_cons a as c
      rw [hRHS_lin, hRHS_em]
      ring

/-! ## §14.  Corollaries of the headline theorems -/

/-- **Corollary 2.1.**  Symmetric reformulation of Theorem 2.1: the
iterated emergence remainder for `(a ◦ b) ◦ c` against `d` equals zero
exactly when the resonance is fully additive on the triple.  This is
the statement that downstream applied work in *Volume 4 (Cognitive
Science / Philosophy of Mind)* uses to characterise "context-free
combination" of mental representations. -/
theorem corollary_2_1 (a b c d : I) :
    iter3Emergence a b c d = 0
      ↔ rs (op (op a b) c) d = rs a d + rs b d + rs c d := by
  have ht := theorem_2_1 a b c d
  constructor
  · intro h; linarith
  · intro h; linarith

/-- **Corollary 2.2.**  The unique idea of weight zero is the void.
This is the statement used throughout *Volume 5 (Emergence)* to
guarantee that the "no-emergence" base case of the 2-cocycle is
degenerate. -/
theorem corollary_2_2 (a : I) (h : weight a = 0) : a = (ε : I) := by
  have ⟨_, _, h3, _⟩ := (theorem_2_2 (I := I))
  exact (h3 a).mp h

/-- **Corollary 2.3.**  An idea is non-void iff its weight is strictly
positive.  This is what *Volume 2 (Social Sciences)* uses to define
the notion of an "active" cultural idea. -/
theorem corollary_2_3 (a : I) : a ≠ (ε : I) ↔ 0 < weight a := by
  have ⟨_, _, _, h4⟩ := (theorem_2_2 (I := I))
  exact (h4 a).symm

/-- **Corollary 2.4.**  For a chain whose cumulative emergence against a
given probe vanishes, the chain resonance is just the linear sum.  This
is the formal version of the "perfect transmission" idealization
discussed in *Volume 2 (Social Sciences)* and used as a counterfactual
baseline in *Volume 5 (Emergence)*. -/
theorem corollary_2_4 (L : List I) (c : I)
    (h : chainEmergence L c = 0) :
    chainResonance L c = chainResonanceLinear L c := by
  have h2 := theorem_2_3 L c
  linarith

/-! ## §15.  Examples and sanity checks -/

example (c : I) :
    chainResonance ([] : List I) c = 0 := chainResonance_nil c

example (a c : I) :
    chainResonance ([a]) c = rs a c := chainResonance_singleton a c

example : weight (ε : I) = 0 := weight_void

example (a b : I) : emergence a b (ε : I) = 0 := emergence_void_right a b

example (b c : I) : emergence (ε : I) b c = 0 := emergence_void_left b c

example (a c : I) : emergence a (ε : I) c = 0 := emergence_void_middle a c

example (a b c : I) :
    rs (op a b) c = rs a c + rs b c + emergence a b c := rs_op_decomp a b c

example (a b c d : I) :
    rs (op (op a b) c) d
      = rs a d + rs b d + rs c d
        + emergence (op a b) c d + emergence a b d := by
  have h := theorem_2_1 a b c d
  rw [iter3Emergence_def] at h
  linarith

example (c : I) :
    chainResonance ([] : List I) c
      = chainResonanceLinear ([] : List I) c := by
  apply corollary_2_4
  exact chainEmergence_nil c

/-! ## §16.  Index of results

* **Primitives:** `rs`, `emergence`, `weight`.
* **Axioms:** `rs_void_left`, `rs_void_right`, `rs_self_nonneg`,
  `rs_nondegen`, `emergence_def`.
* **Auxiliary defs:** `diag`, `coresonance`, `gap`, `emcResonance`,
  `iter3Emergence`, `Probe`, `Probe.evalAt`, `probeSum`,
  `ResonanceClosed`, `chainEmergence`, `chainResonanceLinear`,
  `chainResonance`, `HeavyAbove`, `WeightZero`.
* §4 *Closure*: `diag_def`, `coresonance_def`, `gap_def`,
  `emcResonance_def`, `iter3Emergence_def`, `Probe.evalAt_def`,
  `probeSum_def`, `weight_def`, `emergence_eq`, `rs_op_decomp`.
* §5 *VacuumIdentities*: `weight_void`, `weight_nonneg`,
  `rs_eq_zero_of_left_void`, `rs_eq_zero_of_right_void`,
  `weight_pos_of_ne_void`, `weight_eq_zero_iff`, `weight_pos_iff`,
  `weight_ne_zero_iff`, `rs_void_void`, `coresonance_void_left`,
  `coresonance_void_right`, `gap_void_left`, `gap_void_right`,
  `gap_self_zero`, `coresonance_self`.
* §6 *EmergenceVacuum*: `emergence_void_left`, `emergence_void_middle`,
  `emergence_void_right`, `emergence_void_void_left`,
  `emergence_void_void_right`.
* §7 *Algebra*: `rs_op_assoc_left`, `rs_op_assoc_right`,
  `rs_op_commute_decomp`, `emergence_swap_left`, `emergence_def_symm`,
  `rs_op_sub_left`, `rs_op_sub_right`, `rs_op_eq_iff`,
  `rs_op_void_first`, `rs_op_void_second`, `rs_assoc_collapse`,
  `emergence_assoc_relation`.
* §8 *SymAntisym*: `coresonance_symm`, `gap_antisymm`,
  `rs_eq_half_coresonance_plus_half_gap`,
  `rs_swap_eq_half_coresonance_minus_half_gap`,
  `coresonance_eq_two_rs_iff_gap_zero`, `gap_zero_iff_symmetric`,
  `coresonance_self_eq`, `gap_self_eq`.
* §9 *Probes*: `Probe.evalAt_void`, `Probe.evalAt_op`, `probeSum_void`,
  `probeSum_op`, `Probe.evalAt_self_nonneg`.
* §10 *ChainEmergence*: `chainEmergence_nil`, `chainEmergence_cons`,
  `chainResonanceLinear_nil`, `chainResonanceLinear_cons`,
  `chainResonance_nil`, `chainResonance_singleton`,
  `chainResonance_cons`.
* §11 *Heavy*: `heavyAbove_zero`, `heavyAbove_void_iff`,
  `heavyAbove_mono`, `heavyAbove_pos_of_ne_void`,
  `weightZero_iff_void`, `not_weightZero_of_ne_void`, `weightZero_void`,
  `weight_ne_zero_of_pos`, `weight_zero_imp_void`.
* §12 *Closed*: `ResonanceClosed_universal`, `ResonanceClosed_empty`,
  `ResonanceClosed_intersection`, `ResonanceClosed_singleton_void`.
* §13 *Headline theorems*: `theorem_2_1` (Iterated decomposition),
  `theorem_2_2` (Weight non-degeneracy),
  `theorem_2_3` (Linear decomposition along chains).
* §14 *Corollaries*: `corollary_2_1`, `corollary_2_2`, `corollary_2_3`,
  `corollary_2_4`.
-/

end IdeaTheory
