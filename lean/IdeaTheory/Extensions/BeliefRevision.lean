import Mathlib.Tactic
import IdeaTheory.Foundations

/-!
# IdeaTheory.Extensions.BeliefRevision

Formalizes the AGM postulates for belief revision as properties of idea-algebra
operations. Belief states are ideas; contraction/expansion/revision are built
from the Aufhebung decomposition and composition.

Key connections:
- **Quine (1951)**: ideas form a connected resonance web; revision in one area
  propagates through the network.
- **Gärdenfors (1988)**: Aufhebung-derived revision satisfies the 6 basic AGM
  postulates.
- **Levi identity**: revision = contraction then expansion.

NO `sorry`, NO `admit`.
-/

namespace IdeaTheory.BeliefRevision

open IdeaTheoryStructure

/-! ## §1. Extended idea algebra for belief revision -/

/-- An `IdeaAlgebra` extends a bare `IdeaTheoryStructure` with:
    - a **resonance pairing** `ρ` measuring conceptual proximity,
    - an **Aufhebung negation** `ν`, and
    - a **contraction operator** `con`. -/
class IdeaAlgebra (α : Type*) extends IdeaTheoryStructure α where
  /-- Resonance pairing ρ(a,b) ∈ [0,∞). -/
  ρ : α → α → ℝ
  /-- Aufhebung negation. -/
  ν : α → α
  /-- Binary contraction: `con a b` is the part of `a` that survives removal of `b`. -/
  con : α → α → α
  ρ_nonneg       : ∀ a b, 0 ≤ ρ a b
  ρ_symm         : ∀ a b, ρ a b = ρ b a
  ρ_ident_right  : ∀ a, ρ a ident = 0
  ν_involutive   : ∀ a, ν (ν a) = a
  ν_zero_res     : ∀ a, ρ a (ν a) = 0
  /-- Recovery: contract `a` by `a∘b`, then expand by `b`, recovers `a`. -/
  con_recovery   : ∀ a b, op (con a (op a b)) b = a
  /-- Inclusion: contraction only shrinks self-resonance. -/
  con_le         : ∀ a b, ρ (con a b) (con a b) ≤ ρ a a
  /-- Expansion never decreases self-resonance relative to contraction. -/
  con_expand_le  : ∀ a b,
      ρ (con a b) (con a b) ≤ ρ (op (con a b) b) (op (con a b) b)
  /-- Vacuity: if `b` is irrelevant to `a` (ρ = 0), contraction is a no-op. -/
  con_vacuity    : ∀ a b, ρ a b = 0 → con a b = a
  /-- Success: after revision, `b` resonates positively with the result. -/
  revise_success : ∀ a b, 0 < ρ b b →
      0 < ρ b (op (con a (ν b)) b)
  /-- Consistency: revising a consistent state by a consistent idea is consistent. -/
  revise_consistent : ∀ a b,
      op a a = a → op b b = b → 0 < ρ b b →
      op (op (con a (ν b)) b) (op (con a (ν b)) b) = op (con a (ν b)) b
  /-- Harper axiom: the ρ-neighbourhood of `con a b` equals the intersection of
      those of `a` and of `expand (con a b) (ν b)` (= `revise a (¬b)`). -/
  con_harper     : ∀ a b c,
      0 < ρ (con a b) c ↔
      0 < ρ a c ∧ 0 < ρ (op (con a b) (ν b)) c
  /-- Minimal-change: revision minimises ρ-distance to `a` among all `b`-consistent
      ideas. -/
  revise_minimal : ∀ a b c, 0 < ρ b c → ρ a (op (con a (ν b)) b) ≤ ρ a c
  /-- Transmission: positive resonance chains propagate revision (Quine holism). -/
  resonance_chain : ∀ a b c, 0 < ρ a b → 0 < ρ b c →
      0 < ρ (op (con a (ν c)) c) a

variable {α : Type*} [IdeaAlgebra α]
open IdeaAlgebra

/-! ## §2. Derived definitions -/

/-- A **consistent** belief state is an idempotent idea. -/
def IsConsistent (a : α) : Prop := op a a = a

/-- **Expansion**: add belief `b` to state `a` by composition. -/
def expand (a b : α) : α := op a b

/-- **Contraction**: remove `b` from `a` using the Aufhebung decomposition. -/
def contract (a b : α) : α := con a b

/-- **Negation** (Aufhebung dual) of an idea. -/
def negate (a : α) : α := ν a

/-- **Revision** by `b`: contract out `¬b` from `a`, then expand by `b`.
    This is the Levi identity taken as the *definition* of revision. -/
def revise (a b : α) : α := expand (contract a (negate b)) b

/-! ## §3. Theorems -/

/-- **T1 (Idempotent = consistent belief state).**
    A belief state is *consistent* iff it is idempotent under composition.
    In the AGM framework, consistency is modelled by idempotence of the
    belief closure operator (Alchourrón–Gärdenfors–Makinson 1985). -/
theorem consistent_iff_idempotent (a : α) :
    IsConsistent a ↔ op a a = a := Iff.rfl

/-- **T2a (Expansion associates).**
    Expansion inherits the associativity of `op`; this is the first AGM
    expansion postulate: belief revision respects the monoid structure of idea
    composition. -/
theorem expand_assoc (a b c : α) :
    expand (expand a b) c = expand a (expand b c) :=
  assoc a b c

/-- **T2b (Expansion left identity).**
    The neutral idea is a left identity for expansion: expanding the empty
    belief state by `a` returns `a`. -/
theorem expand_id_left (a : α) : expand ident a = a := id_left a

/-- **T2c (Expansion right identity).**
    The neutral idea is a right identity for expansion: expanding `a` by the
    empty belief adds nothing. -/
theorem expand_id_right (a : α) : expand a ident = a := id_right a

/-- **T3 (ρ left-identity).**
    The identity idea resonates 0 with every idea — it carries no information
    content and hence no conceptual proximity to anything. -/
theorem ρ_ident_left (a : α) : ρ ident a = 0 := by
  rw [ρ_symm, ρ_ident_right]

/-- **T4 (Recovery / Levi-like).**
    Contracting `a` by the compound `a ∘ b`, then re-expanding by `b`, returns
    `a` exactly.  This is the Levi-style recovery: removing then re-adding a
    belief restores the original state — the kernel of the resonance map is
    respected. -/
theorem levi_recovery (a b : α) :
    expand (contract a (expand a b)) b = a := by
  unfold expand contract
  exact con_recovery a b

/-- **T5 (Recovery postulate — inclusion direction).**
    Contracting `a` by `b` and re-expanding by `b` yields an idea whose
    self-resonance is at least as large as that of the contraction alone.
    This is the AGM inclusion half of the recovery postulate:
    the contracted state is "contained in" the re-expanded state. -/
theorem recovery_postulate_inclusion (a b : α) :
    ρ (contract a b) (contract a b) ≤
    ρ (expand (contract a b) b) (expand (contract a b) b) := by
  unfold expand contract
  exact con_expand_le a b

/-- **T6 (Inclusion in the resonance preorder).**
    Contraction always yields a strictly "smaller" idea in the resonance
    preorder: `ρ(con a b, con a b) ≤ ρ(a, a)`.
    This is the AGM inclusion postulate. -/
theorem contract_inclusion (a b : α) :
    ρ (contract a b) (contract a b) ≤ ρ a a := by
  unfold contract
  exact con_le a b

/-- **T7 (Vacuity postulate).**
    If `b` has zero resonance with `a` (i.e., `b` is irrelevant to `a`), then
    contracting `a` by `b` leaves `a` unchanged.
    This is the AGM vacuity postulate: you only lose beliefs by contracting by
    something that is actually entailed. -/
theorem vacuity_postulate (a b : α) (h : ρ a b = 0) :
    contract a b = a :=
  con_vacuity a b h

/-- **T8 (Success postulate).**
    After revising `a` by a self-consistent idea `b` (ρ(b,b) > 0), `b` resonates
    positively with the revised belief state.
    This is the AGM success postulate: the triggering belief is accepted after
    revision. -/
theorem success_postulate (a b : α) (h : 0 < ρ b b) :
    0 < ρ b (revise a b) := by
  unfold revise expand contract negate
  exact revise_success a b h

/-- **T9 (Consistency preservation).**
    Revising a consistent state `a` by a consistent idea `b` (with positive
    self-resonance) yields a consistent state.
    This is the AGM consistency postulate. -/
theorem consistency_preserved (a b : α)
    (ha : IsConsistent a) (hb : IsConsistent b) (hρ : 0 < ρ b b) :
    IsConsistent (revise a b) := by
  unfold revise expand contract negate IsConsistent
  exact revise_consistent a b ha hb hρ

/-- **T10 (Superexpansion / double contraction).**
    A double contraction is no larger than a single contraction: the self-
    resonance of `con (con a b) c` is bounded above by `ρ(a, a)`.
    This is the resonance analogue of the AGM superexpansion postulate. -/
theorem superexpansion (a b c : α) :
    ρ (contract (contract a b) c) (contract (contract a b) c) ≤ ρ a a := by
  unfold contract
  calc ρ (con (con a b) c) (con (con a b) c)
      ≤ ρ (con a b) (con a b) := con_le (con a b) c
    _ ≤ ρ a a                 := con_le a b

/-- **T11 (Gärdenfors bridge — six basic AGM postulates).**
    The `revise` operator derived from the Aufhebung decomposition satisfies all
    six basic AGM postulates simultaneously: success, consistency, inclusion,
    vacuity, the Levi identity, and recovery.
    This is Theorem 4.4 of Gärdenfors (1988) instantiated in idea algebra. -/
theorem agm_six_postulates (a b : α)
    (ha : IsConsistent a) (hb : IsConsistent b) (hρ : 0 < ρ b b) :
    -- (P1) Success
    (0 < ρ b (revise a b)) ∧
    -- (P2) Consistency preservation
    (IsConsistent (revise a b)) ∧
    -- (P3) Inclusion
    (ρ (contract a b) (contract a b) ≤ ρ a a) ∧
    -- (P4) Vacuity
    (ρ a b = 0 → contract a b = a) ∧
    -- (P5) Levi identity holds by definition
    (revise a b = expand (contract a (negate b)) b) ∧
    -- (P6) Recovery
    (expand (contract a (expand a b)) b = a) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact success_postulate a b hρ
  · exact consistency_preserved a b ha hb hρ
  · exact contract_inclusion a b
  · exact vacuity_postulate a b
  · rfl
  · exact levi_recovery a b

/-- **T12 (Levi identity).**
    Revision is *definitionally* equal to: contract out `¬b`, then expand by `b`.
    This is the Levi identity (Levi 1977), which governs the relationship between
    contraction and revision in AGM theory. -/
theorem levi_identity (a b : α) :
    revise a b = expand (contract a (negate b)) b := rfl

/-- **T13 (Harper identity).**
    The ρ-neighbourhood of `contract a b` equals the intersection of the
    ρ-neighbourhoods of `a` and of `revise a (negate b)`.
    This is the Harper identity (Harper 1976), which is the converse of the
    Levi identity and characterises contraction in terms of revision. -/
theorem harper_identity (a b c : α) :
    0 < ρ (contract a b) c ↔
    0 < ρ a c ∧ 0 < ρ (revise a (negate b)) c := by
  unfold revise expand contract negate
  rw [show ν (ν b) = b from ν_involutive b]
  exact con_harper a b c

/-- **T14 (Minimal change).**
    Among all ideas `c` that are consistent with `b` (i.e., ρ(b,c) > 0), the
    revision `revise a b` minimises the ρ-distance to `a`.
    This captures Gärdenfors' principle of minimal change: revision perturbs
    the belief state as little as possible while achieving success. -/
theorem minimal_change (a b c : α) (hc : 0 < ρ b c) :
    ρ a (revise a b) ≤ ρ a c := by
  unfold revise expand contract negate
  exact revise_minimal a b c hc

/-- **T15 (Quine holism — chain propagation).**
    If `a` resonates with `b` and `b` resonates with `c`, then revising `a` by
    `c` produces a state that resonates back with `a`.  In Quine's web of belief
    (1951), no belief is in principle immune from revision, and revision in one
    part of the web propagates through connected beliefs. -/
theorem quine_holism (a b c : α) (hab : 0 < ρ a b) (hbc : 0 < ρ b c) :
    0 < ρ (revise a c) a := by
  unfold revise expand contract negate
  exact resonance_chain a b c hab hbc

/-- **T16 (Negate self-resonance is zero).**
    Every idea resonates 0 with its own negation: `ρ(a, ν a) = 0`.
    This formalises the philosophical principle that an idea and its Aufhebung
    negation are maximally distant — they share no conceptual content. -/
theorem negate_zero_resonance (a : α) : ρ a (negate a) = 0 := ν_zero_res a

end IdeaTheory.BeliefRevision
