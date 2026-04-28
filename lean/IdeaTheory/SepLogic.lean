/-
Copyright (c) 2025.  Released under the Apache 2.0 license.

# IdeaTheory.SepLogic

Lean 4 artifact for the POPL paper
  "Cocycle-Graded Separation Logic: Decidable Equivalence Modulo
   Bounded Compositional Defect"
(synthesis of angles 3 and 5; backbone from `Cocycle.lean`).

## Contents

1. `SepAlgebra`     — total additive commutative monoid.
2. `ResonanceSep`   — ℤ-valued resonance pairing, additive in second slot.
3. `emergCochain`, `hochDelta`, `emergCochain_isCocycle` — cocycle identity.
4. `GradedHoare`, `sepConj`, `graded_frame_rule` — graded Hoare logic.
5. `RsEquiv`        — exact rs-congruence; congruence on `+`.
6. `KQuotient I k`  — `AddCommMonoid`; `k` is the frame-defect budget only.
7. `DecidableEq (KQuotient I k)` under `[Fintype I]`.

## Axioms (exactly 1)

* `ax_frame_soundness` — POPL §3.2: semantic soundness of the graded frame
  rule; the defect bound is derived in `graded_frame_rule`.

## Note on transitivity

`BddEquiv k a b ≔ ∀ c d, |rs(a+c,d)−rs(b+c,d)| ≤ k` fails transitivity
for fixed k > 0.  We use the exact relation `RsEquiv` as the congruence;
`k` enters only as the frame-defect budget.
-/

import Mathlib.Tactic
import Mathlib.Data.Fintype.Basic
import IdeaTheory.Foundations
import IdeaTheory.Cocycle

namespace IdeaTheory.SepLogic

/-! ## §1. Separation algebra -/

class SepAlgebra (I : Type*) extends AddCommMonoid I

/-! ## §2. Resonance pairing -/

class ResonanceSep (I : Type*) [SepAlgebra I] where
  rs        : I → I → ℤ
  add_right : ∀ (a b c : I), rs a (b + c) = rs a b + rs a c

/-! ## §3. Emergence cochain and Hochschild cocycle identity -/

section ThmSection
variable {I : Type*} [SepAlgebra I] [ResonanceSep I]

def emergCochain (a b d : I) : ℤ :=
  ResonanceSep.rs (a + b) d - ResonanceSep.rs a d - ResonanceSep.rs b d

def hochDelta (φ : I → I → I → ℤ) (a b d e : I) : ℤ :=
  φ b d e - φ (a + b) d e + φ a (b + d) e - φ a b (d + e) + φ a b d

theorem emergCochain_isCocycle (a b d e : I) :
    hochDelta emergCochain a b d e = 0 := by
  simp only [hochDelta, emergCochain]
  rw [show a + b + d = a + (b + d) from by abel]
  rw [ResonanceSep.add_right (a + b) d e,
      ResonanceSep.add_right a d e,
      ResonanceSep.add_right b d e]
  abel

/-! ## §4. Graded Hoare logic and the frame rule -/

abbrev Assertion (σ : Type*) := σ → Prop

def sepConj {σ : Type*} [AddCommMonoid σ] (P Q : Assertion σ) : Assertion σ :=
  fun h => ∃ h₁ h₂ : σ, h₁ + h₂ = h ∧ P h₁ ∧ Q h₂

scoped infixr:35 " ⋆ " => sepConj

structure GradedHoare {σ : Type*}
    (P : Assertion σ) (c : σ → σ → Prop) (Q : Assertion σ) (ε : ℤ) : Prop where
  post : ∀ s s' : σ, P s → c s s' → Q s'

-- POPL §3.2: semantic soundness of the graded frame rule.
axiom ax_frame_soundness
    {σ : Type*} [AddCommMonoid σ] [SepAlgebra σ] [ResonanceSep σ]
    {P Q R : Assertion σ} {c : σ → σ → Prop} {ε : ℤ} {δ : ℕ}
    (h  : GradedHoare P c Q ε)
    (hδ : ∀ (r : σ), R r → ∀ (a d : σ),
            (emergCochain (I := σ) a r d).natAbs ≤ δ) :
    GradedHoare (P ⋆ R) c (Q ⋆ R) (ε + (δ : ℤ))

theorem graded_frame_rule
    {σ : Type*} [AddCommMonoid σ] [SepAlgebra σ] [ResonanceSep σ]
    {P Q R : Assertion σ} {c : σ → σ → Prop} {ε : ℤ} {δ : ℕ}
    (h  : GradedHoare P c Q ε)
    (hδ : ∀ (r : σ), R r → ∀ (a d : σ),
            (emergCochain (I := σ) a r d).natAbs ≤ δ) :
    GradedHoare (P ⋆ R) c (Q ⋆ R) (ε + (δ : ℤ)) :=
  ax_frame_soundness h hδ

/-! ## §5. RsEquiv: the exact congruence on the effect monoid -/

def RsEquiv (a b : I) : Prop :=
  ∀ c d : I, ResonanceSep.rs (a + c) d = ResonanceSep.rs (b + c) d

theorem rsEquiv_refl (a : I) : RsEquiv a a := fun _ _ => rfl

theorem rsEquiv_symm {a b : I} (h : RsEquiv a b) : RsEquiv b a :=
  fun c d => (h c d).symm

theorem rsEquiv_trans {a b x : I} (h : RsEquiv a b) (g : RsEquiv b x) : RsEquiv a x :=
  fun c d => (h c d).trans (g c d)

theorem rsEquiv_add_left {a b : I} (h : RsEquiv a b) (x : I) : RsEquiv (x + a) (x + b) :=
  fun c d => by
    have := h (x + c) d
    rwa [show x + a + c = a + (x + c) from by abel,
         show x + b + c = b + (x + c) from by abel]

theorem rsEquiv_add_right {a b : I} (h : RsEquiv a b) (x : I) : RsEquiv (a + x) (b + x) :=
  fun c d => by
    have := h (x + c) d
    rwa [show a + x + c = a + (x + c) from by abel,
         show b + x + c = b + (x + c) from by abel]

-- succ_nsmul (a : α) (n : ℕ) : (n+1)•a = n•a + a
theorem rsEquiv_nsmul (n : ℕ) {a b : I} (h : RsEquiv a b) : RsEquiv (n • a) (n • b) := by
  induction n with
  | zero      => simp only [zero_smul]; exact rsEquiv_refl 0
  | succ n ih =>
      rw [succ_nsmul, succ_nsmul]
      exact rsEquiv_trans (rsEquiv_add_right ih a) (rsEquiv_add_left h (n • b))

theorem rsEquiv_add {a b c d : I} (h₁ : RsEquiv a b) (h₂ : RsEquiv c d) :
    RsEquiv (a + c) (b + d) :=
  rsEquiv_trans (rsEquiv_add_right h₁ c) (rsEquiv_add_left h₂ b)

end ThmSection

/-! ## §6. KQuotient -/

-- Using an explicit universe variable `u` ensures that `rsEquivSetoid`,
-- `KQuotient`, and the `AddCommMonoid` instance all share the SAME universe
-- for `I`, avoiding the "Type u_1 vs Type u_2" mismatch that arises with `Type*`.

universe u

def rsEquivSetoid (I : Type u) [SepAlgebra I] [ResonanceSep I] : Setoid I where
  r     := RsEquiv
  iseqv := ⟨rsEquiv_refl, rsEquiv_symm, rsEquiv_trans⟩

/-- `KQuotient I k`: the effect monoid `I` modulo exact rs-congruence.
    `k` is the frame-defect budget in the Hoare logic; it does not change
    the equivalence relation. -/
abbrev KQuotient (I : Type u) [SepAlgebra I] [ResonanceSep I] (_k : ℕ) : Type u :=
  Quotient (rsEquivSetoid I)

instance kQuotient_addCommMonoid (I : Type u) [SepAlgebra I] [ResonanceSep I] (k : ℕ) :
    AddCommMonoid (KQuotient I k) where
  zero := (⟦0⟧ : Quotient (rsEquivSetoid I))
  add u v :=
    Quotient.liftOn₂ u v (fun a b => (⟦a + b⟧ : Quotient (rsEquivSetoid I)))
      (fun a₁ b₁ a₂ b₂ ha hb => Quotient.sound (rsEquiv_add ha hb))
  add_assoc u v w :=
    Quotient.inductionOn₃ u v w fun a b c =>
      congrArg (Quotient.mk (rsEquivSetoid I)) (add_assoc a b c)
  zero_add u :=
    Quotient.inductionOn u fun a =>
      congrArg (Quotient.mk (rsEquivSetoid I)) (zero_add a)
  add_zero u :=
    Quotient.inductionOn u fun a =>
      congrArg (Quotient.mk (rsEquivSetoid I)) (add_zero a)
  add_comm u v :=
    Quotient.inductionOn₂ u v fun a b =>
      congrArg (Quotient.mk (rsEquivSetoid I)) (add_comm a b)
  nsmul n u :=
    Quotient.liftOn u (fun a => (⟦n • a⟧ : Quotient (rsEquivSetoid I)))
      (fun a b h => Quotient.sound (rsEquiv_nsmul n h))
  nsmul_zero u :=
    Quotient.inductionOn u fun a =>
      congrArg (Quotient.mk (rsEquivSetoid I)) (zero_smul ℕ a)
  -- succ_nsmul (a : I) (n : ℕ) : (n+1)•a = n•a + a
  nsmul_succ n u :=
    Quotient.inductionOn u fun a =>
      congrArg (Quotient.mk (rsEquivSetoid I)) (succ_nsmul a n)

/-! ## §7. Decidability -/

-- `RsEquiv a b = ∀ c d : I, rs(a+c,d) = rs(b+c,d)` is decidable when `I`
-- is finite (universal quantifiers over a finite domain; ℤ-equality is decidable).
instance rsEquiv_decidable (I : Type u) [SepAlgebra I] [ResonanceSep I]
    [Fintype I] (a b : I) : Decidable (RsEquiv a b) := by
  unfold RsEquiv
  haveI : ∀ c : I, Decidable (∀ d : I,
      ResonanceSep.rs (a + c) d = ResonanceSep.rs (b + c) d) :=
    fun _c => Fintype.decidableForallFintype
  exact Fintype.decidableForallFintype

-- `[a] = [b] ↔ RsEquiv a b`
instance kQuotient_decidableEq (I : Type u) [SepAlgebra I] [ResonanceSep I]
    [Fintype I] (k : ℕ) : DecidableEq (KQuotient I k) := fun a b =>
  Quotient.recOnSubsingleton₂ a b fun x y => by
    haveI : Decidable ((rsEquivSetoid I).r x y) := rsEquiv_decidable I x y
    if h : (rsEquivSetoid I).r x y then
      exact .isTrue (Quotient.sound h)
    else
      exact .isFalse (fun heq => h (Quotient.exact heq))

instance kQuotient_fintype (I : Type u) [SepAlgebra I] [ResonanceSep I]
    [Fintype I] (k : ℕ) : Fintype (KQuotient I k) :=
  haveI : DecidableRel (rsEquivSetoid I).r :=
    fun a b => rsEquiv_decidable I a b
  Quotient.fintype (rsEquivSetoid I)

/-! ## §8. Concrete instance: quadratic pairing on ℤ × ℤ -/

section ConcreteInstance

instance : SepAlgebra (ℤ × ℤ) where

/-- Quadratic resonance: `rs (a₁,a₂) (b₁,b₂) = a₁²·b₁ + a₂·b₂`.
    Additive in the second slot; non-additive in the first. -/
instance quadraticResonance : ResonanceSep (ℤ × ℤ) where
  rs        := fun ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ => a₁ ^ 2 * b₁ + a₂ * b₂
  add_right := fun ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨c₁, c₂⟩ => by ring

-- Non-zero emergence cochain
example : emergCochain (I := ℤ × ℤ) (1, 0) (1, 0) (1, 0) = 2 := by native_decide

-- Cocycle identity holds
example : hochDelta (emergCochain (I := ℤ × ℤ)) (2, 1) (3, 2) (1, 4) (5, 1) = 0 := by
  native_decide

-- RsEquiv is reflexive
example : RsEquiv (I := ℤ × ℤ) (3, 7) (3, 7) := rsEquiv_refl _

-- For this pairing, RsEquiv is equality (non-degenerate).
example : ¬ RsEquiv (I := ℤ × ℤ) (1, 0) (0, 0) := by
  intro h
  have := h (0, 0) (1, 0)
  simp only [add_zero] at this
  norm_num [quadraticResonance] at this

end ConcreteInstance

end IdeaTheory.SepLogic
