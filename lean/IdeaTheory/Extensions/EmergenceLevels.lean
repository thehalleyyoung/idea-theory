import Mathlib.Tactic
import IdeaTheory.Foundations

/-!
# IdeaTheory.Extensions.EmergenceLevels

Emergence levels for an `IdeaTheoryStructure α`: weak vs. strong emergence
formalized via the cocycle `ω(a,b) = v(a∘b) - v(a) - v(b)` of a real-valued
valuation `v : α → ℝ`.

We follow the Bedau ("weak emergence = `ω`-bounded") / Chalmers ("strong
emergence = cohomological obstruction") slogan from the SHARED_BRIEF: a
valuation is *additive* when its cocycle vanishes, *weakly emergent* when its
cocycle is uniformly bounded, and *strongly emergent* when no additive
valuation coincides with it pointwise.

NO sorries, NO admits.
-/

namespace IdeaTheory
namespace EmergenceLevels

open IdeaTheoryStructure

variable {α : Type*} [IdeaTheoryStructure α]

/-! ## §1. Valuations and the emergence cocycle -/

/-- A real-valued valuation on the carrier of an idea-theory structure. -/
abbrev Valuation (α : Type*) := α → ℝ

/-- The emergence 2-cocycle of a valuation `v`:
`ω(a,b) := v(a ∘ b) − v(a) − v(b)`. -/
def omega (v : Valuation α) (a b : α) : ℝ :=
  v (op a b) - v a - v b

/-- A valuation is *additive* when its cocycle vanishes everywhere. -/
def IsAdditive (v : Valuation α) : Prop := ∀ a b : α, omega v a b = 0

/-- A valuation is *weakly emergent* (Bedau) with bound `M ≥ 0` when its
cocycle is uniformly bounded by `M` in absolute value. -/
def IsBoundedEmergent (M : ℝ) (v : Valuation α) : Prop :=
  ∀ a b : α, |omega v a b| ≤ M

/-- A valuation is *strongly emergent* (Chalmers) when no additive valuation
agrees with it pointwise. -/
def IsStronglyEmergent (v : Valuation α) : Prop :=
  ¬ ∃ v' : Valuation α, IsAdditive v' ∧ ∀ a, v' a = v a

/-! ## §2. Normalization and the cocycle identity -/

/-- Left normalization: `ω(ident, a) = - v(ident)`. -/
theorem omega_ident_left (v : Valuation α) (a : α) :
    omega v ident a = - v ident := by
  unfold omega
  rw [id_left]
  ring

/-- Right normalization: `ω(a, ident) = - v(ident)`. -/
theorem omega_ident_right (v : Valuation α) (a : α) :
    omega v a ident = - v ident := by
  unfold omega
  rw [id_right]
  ring

/-- If `v(ident) = 0`, then `ω` is normalized on the left. -/
theorem omega_ident_left_of_zero {v : Valuation α} (h : v ident = 0) (a : α) :
    omega v ident a = 0 := by
  rw [omega_ident_left, h, neg_zero]

/-- If `v(ident) = 0`, then `ω` is normalized on the right. -/
theorem omega_ident_right_of_zero {v : Valuation α} (h : v ident = 0) (a : α) :
    omega v a ident = 0 := by
  rw [omega_ident_right, h, neg_zero]

/-- The 2-cocycle identity for `ω`: `δω = 0`. This is the standard sign
convention `ω(b,c) − ω(a∘b, c) + ω(a, b∘c) − ω(a,b) = 0`, derived from the
associativity of `op`. -/
theorem cocycle_identity (v : Valuation α) (a b c : α) :
    omega v b c - omega v (op a b) c + omega v a (op b c) - omega v a b = 0 := by
  unfold omega
  have hassoc : op (op a b) c = op a (op b c) := assoc a b c
  rw [hassoc]
  ring

/-! ## §3. Homomorphisms and additivity -/

/-- A valuation that is a monoid homomorphism into `(ℝ, +, 0)` is additive. -/
theorem isAdditive_of_hom (v : Valuation α)
    (hhom : ∀ a b : α, v (op a b) = v a + v b) : IsAdditive v := by
  intro a b
  unfold omega
  rw [hhom]
  ring

/-- The constant zero valuation is additive. -/
theorem isAdditive_zero : IsAdditive (fun _ : α => (0 : ℝ)) := by
  intro a b
  unfold omega
  ring

/-- Any constant valuation `v ≡ c` has cocycle `ω(a,b) = -c`. -/
theorem omega_const (c : ℝ) (a b : α) :
    omega (fun _ : α => c) a b = -c := by
  unfold omega; ring

/-- A constant valuation is additive iff the constant is zero. -/
theorem isAdditive_const_iff (c : ℝ) [Nonempty α] :
    IsAdditive (fun _ : α => c) ↔ c = 0 := by
  refine ⟨?_, ?_⟩
  · intro h
    obtain ⟨a⟩ := (inferInstance : Nonempty α)
    have := h a a
    rw [omega_const] at this
    linarith
  · intro hc
    subst hc
    exact isAdditive_zero

/-! ## §4. Weak emergence -/

/-- Additive valuations are weakly emergent with bound `0`. -/
theorem isBoundedEmergent_zero_of_additive {v : Valuation α}
    (h : IsAdditive v) : IsBoundedEmergent 0 v := by
  intro a b
  rw [h a b, abs_zero]

/-- The bound in weak emergence is monotone: a tighter bound implies a looser
bound. -/
theorem isBoundedEmergent_mono {v : Valuation α} {M N : ℝ}
    (hMN : M ≤ N) (h : IsBoundedEmergent M v) : IsBoundedEmergent N v := by
  intro a b
  exact (h a b).trans hMN

/-- A bounded valuation has nonneg bound. -/
theorem isBoundedEmergent_nonneg {v : Valuation α} {M : ℝ} [Nonempty α]
    (h : IsBoundedEmergent M v) : 0 ≤ M := by
  obtain ⟨a⟩ := (inferInstance : Nonempty α)
  exact (abs_nonneg _).trans (h a a)

/-! ## §5. Coboundary lemma -/

/-- The coboundary of a 1-cochain `f : α → ℝ`:
`(δf)(a,b) := f(a∘b) − f(a) − f(b)`. -/
def delta (f : α → ℝ) (a b : α) : ℝ :=
  f (op a b) - f a - f b

/-- Coboundary lemma: shifting a valuation `v` by a 1-cochain `f` shifts the
cocycle by the coboundary `δf`. Equivalently, `ω(v + f) = ω(v) + δf`. -/
theorem omega_add (v : Valuation α) (f : α → ℝ) (a b : α) :
    omega (fun a => v a + f a) a b = omega v a b + delta f a b := by
  unfold omega delta
  ring

/-- Adding any coboundary `δf` to an additive valuation produces a valuation
whose cocycle is exactly `δf`. -/
theorem omega_additive_plus_coboundary {v : Valuation α} (hv : IsAdditive v)
    (f : α → ℝ) (a b : α) :
    omega (fun a => v a + f a) a b = delta f a b := by
  rw [omega_add, hv a b, zero_add]

/-- Two valuations agreeing pointwise have the same cocycle. -/
theorem omega_congr {v w : Valuation α} (h : ∀ a, v a = w a) (a b : α) :
    omega v a b = omega w a b := by
  unfold omega; rw [h, h, h]

/-! ## §6. Linearity in the valuation -/

/-- Cocycle of a sum of valuations. -/
theorem omega_sum (v w : Valuation α) (a b : α) :
    omega (fun a => v a + w a) a b = omega v a b + omega w a b := by
  unfold omega; ring

/-- Cocycle of a scalar multiple of a valuation. -/
theorem omega_smul (c : ℝ) (v : Valuation α) (a b : α) :
    omega (fun a => c * v a) a b = c * omega v a b := by
  unfold omega; ring

/-- Bounded emergence is preserved by non-negative scaling. -/
theorem isBoundedEmergent_smul {c M : ℝ} (hc : 0 ≤ c) {v : Valuation α}
    (h : IsBoundedEmergent M v) :
    IsBoundedEmergent (c * M) (fun a => c * v a) := by
  intro a b
  rw [omega_smul, abs_mul, abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left (h a b) hc

/-- "Truncation"/superposition: the sum of an `M`-bounded and an `N`-bounded
valuation is `(M + N)`-bounded. In particular two `M`-bounded valuations
combine to a `2M`-bounded one. -/
theorem isBoundedEmergent_add {v w : Valuation α} {M N : ℝ}
    (hv : IsBoundedEmergent M v) (hw : IsBoundedEmergent N w) :
    IsBoundedEmergent (M + N) (fun a => v a + w a) := by
  intro a b
  rw [omega_sum]
  calc |omega v a b + omega w a b|
      ≤ |omega v a b| + |omega w a b| := abs_add _ _
    _ ≤ M + N := add_le_add (hv a b) (hw a b)

/-- Specialization: superposing two `M`-bounded valuations yields a
`2M`-bounded valuation. -/
theorem isBoundedEmergent_add_self {v w : Valuation α} {M : ℝ}
    (hv : IsBoundedEmergent M v) (hw : IsBoundedEmergent M w) :
    IsBoundedEmergent (2 * M) (fun a => v a + w a) := by
  have := isBoundedEmergent_add hv hw
  simpa [two_mul] using this

/-! ## §7. Strong emergence: equivalence with non-additivity -/

/-- A valuation is strongly emergent iff it is not itself additive. (The
existential definition collapses because the witness is forced to equal `v`
pointwise.) -/
theorem stronglyEmergent_iff_not_additive (v : Valuation α) :
    IsStronglyEmergent v ↔ ¬ IsAdditive v := by
  unfold IsStronglyEmergent
  refine ⟨?_, ?_⟩
  · intro hne hadd
    exact hne ⟨v, hadd, fun _ => rfl⟩
  · intro hna ⟨v', hadd', hagree⟩
    apply hna
    intro a b
    have h1 : v' (op a b) = v (op a b) := hagree _
    have h2 : v' a = v a := hagree _
    have h3 : v' b = v b := hagree _
    have hv'ab : omega v' a b = 0 := hadd' a b
    unfold omega at hv'ab ⊢
    linarith

/-! ## §8. A concrete strongly-emergent example on `Bool` -/

/-- `Bool` becomes an `IdeaTheoryStructure` under disjunction with `false` as
the identity. -/
instance : IdeaTheoryStructure Bool where
  op := fun a b => a || b
  ident := false
  assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  id_left := by intro a; cases a <;> rfl
  id_right := by intro a; cases a <;> rfl

/-- The "indicator" valuation `v(false)=0`, `v(true)=1` on `Bool`. -/
def boolIndicator : Valuation Bool := fun b => if b then (1 : ℝ) else 0

/-- `boolIndicator` has nonzero cocycle at `(true, true)`: `ω = -1`. -/
theorem omega_boolIndicator_true_true :
    omega boolIndicator true true = -1 := by
  unfold omega boolIndicator
  show (if (true || true) then (1:ℝ) else 0)
        - (if true then (1:ℝ) else 0)
        - (if true then (1:ℝ) else 0) = -1
  norm_num

/-- The indicator valuation on `Bool` is not additive. -/
theorem boolIndicator_not_additive : ¬ IsAdditive boolIndicator := by
  intro h
  have := h true true
  rw [omega_boolIndicator_true_true] at this
  linarith

/-- The indicator valuation on `Bool` is strongly emergent: there is no
additive valuation that agrees with it pointwise. -/
theorem boolIndicator_stronglyEmergent : IsStronglyEmergent boolIndicator :=
  (stronglyEmergent_iff_not_additive _).mpr boolIndicator_not_additive

/-- The indicator valuation is nonetheless weakly (`1`-bounded) emergent. -/
theorem boolIndicator_boundedEmergent : IsBoundedEmergent 1 boolIndicator := by
  intro a b
  unfold omega boolIndicator
  show |(if (a || b) then (1:ℝ) else 0) - (if a then (1:ℝ) else 0)
        - (if b then (1:ℝ) else 0)| ≤ 1
  cases a <;> cases b <;> norm_num

end EmergenceLevels
end IdeaTheory
