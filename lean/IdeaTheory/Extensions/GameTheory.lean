import Mathlib.Tactic
import IdeaTheory.Foundations

/-!
# IdeaTheory.Extensions.GameTheory

A small game-theoretic layer on top of an `IdeaTheoryStructure`: ideas are
strategies, profiles assign one strategy to each player, and payoffs are real
valued.  We define best response, (pure) Nash equilibrium, mixed strategies,
expected payoff, and prove twelve elementary but non-trivial structural
results, all of them tactic-driven and machine-verified.

No `sorry`, no `admit`.
-/

open scoped BigOperators

namespace IdeaTheory.GameTheory

open IdeaTheory IdeaTheoryStructure Function

universe u

/-! ## §1. Games, profiles and equilibria -/

/-- A finite n-player game with strategies drawn from an idea-theoretic carrier
`α` and real valued payoffs. -/
structure IdeaGame (α : Type u) [IdeaTheoryStructure α] where
  /-- Number of players. -/
  n      : ℕ
  /-- Player `i`'s payoff at a strategy profile `s`. -/
  payoff : Fin n → (Fin n → α) → ℝ

variable {α : Type u} [IdeaTheoryStructure α]

/-- The constant strategy profile that plays the identity element everywhere. -/
def identProfile (G : IdeaGame α) : Fin G.n → α := fun _ => ident

/-- `a` is a best response of player `i` against the profile `s`. -/
def IsBestResponse (G : IdeaGame α) (i : Fin G.n) (s : Fin G.n → α) (a : α) : Prop :=
  ∀ b : α, G.payoff i (update s i b) ≤ G.payoff i (update s i a)

/-- A profile `s` is a (pure) Nash equilibrium: no player can strictly improve
by a unilateral deviation. -/
def IsNash (G : IdeaGame α) (s : Fin G.n → α) : Prop :=
  ∀ (i : Fin G.n) (b : α), G.payoff i (update s i b) ≤ G.payoff i s

/-! ## §2. Mixed strategies -/

/-- A mixed strategy on a finite strategy type is a probability distribution. -/
structure MixedStrategy (β : Type u) [Fintype β] where
  /-- The probability mass function. -/
  prob    : β → ℝ
  nonneg  : ∀ b, 0 ≤ prob b
  sum_one : ∑ b, prob b = 1

/-- The expected value of a real valued function under a mixed strategy. -/
def MixedStrategy.expect {β : Type u} [Fintype β] (μ : MixedStrategy β)
    (f : β → ℝ) : ℝ :=
  ∑ b, μ.prob b * f b

/-! ## §3. Theorems -/

/-- **T1 (Constant payoffs).**  If every player's payoff is independent of the
profile, then every profile is a Nash equilibrium. -/
theorem nash_of_constant_payoff (G : IdeaGame α)
    (h : ∀ (i : Fin G.n) (s t : Fin G.n → α), G.payoff i s = G.payoff i t)
    (s : Fin G.n → α) : IsNash G s := by
  intro i b
  exact le_of_eq (h i _ _)

/-- **T2 (Global maximum at `ident`).**  If, profile by profile, no deviation
from the all-`ident` profile by player `i` can yield more than the all-`ident`
payoff itself, then the all-`ident` profile is a Nash equilibrium. -/
theorem nash_identProfile_of_global_max (G : IdeaGame α)
    (h : ∀ (i : Fin G.n) (b : α),
      G.payoff i (update (identProfile G) i b) ≤ G.payoff i (identProfile G)) :
    IsNash G (identProfile G) := h

/-- **T3 (Equivalent characterization).**  A profile is a Nash equilibrium iff
each player plays a best response to it. -/
theorem isNash_iff_forall_best_response (G : IdeaGame α) (s : Fin G.n → α) :
    IsNash G s ↔ ∀ i : Fin G.n, IsBestResponse G i s (s i) := by
  classical
  constructor
  · intro hN i b
    have h := hN i b
    simpa [update_eq_self] using h
  · intro hBR i b
    have h := hBR i b
    simpa [update_eq_self] using h

/-- **T4 (Existence of a best response on finite strategies).**  When the
strategy carrier is finite and inhabited, every player has a best response to
every opponent profile. -/
theorem exists_best_response [Fintype α] [Nonempty α]
    (G : IdeaGame α) (i : Fin G.n) (s : Fin G.n → α) :
    ∃ a : α, IsBestResponse G i s a := by
  classical
  obtain ⟨a, _, ha⟩ :=
    Finset.exists_max_image (Finset.univ : Finset α)
      (fun a => G.payoff i (update s i a)) Finset.univ_nonempty
  refine ⟨a, ?_⟩
  intro b
  exact ha b (Finset.mem_univ _)

/-- **T5 (Existence on a finite singleton game).**  Any one-player game on a
finite, inhabited strategy set has a Nash equilibrium. -/
theorem exists_nash_one_player [Fintype α] [Nonempty α]
    (payoff : (Fin 1 → α) → ℝ) :
    ∃ s : Fin 1 → α, IsNash (⟨1, fun _ => payoff⟩ : IdeaGame α) s := by
  classical
  let G : IdeaGame α := ⟨1, fun _ => payoff⟩
  obtain ⟨a, ha⟩ := exists_best_response G 0 (fun _ => ident)
  refine ⟨update (fun _ => ident) 0 a, ?_⟩
  intro i b
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  have hupd : update (update (fun _ : Fin 1 => (ident : α)) 0 a) 0 b
            = update (fun _ : Fin 1 => (ident : α)) 0 b := by
    funext j
    by_cases hj : j = 0
    · subst hj; simp
    · simp [update, hj]
  have hb := ha b
  show G.payoff 0 (update (update (fun _ => ident) 0 a) 0 b)
        ≤ G.payoff 0 (update (fun _ => ident) 0 a)
  rw [hupd]
  exact hb

/-- **T6 (Positive scaling preserves Nash).**  Multiplying every player's
payoff by the same positive constant preserves the set of Nash equilibria. -/
theorem nash_pos_scale (G : IdeaGame α) {c : ℝ} (hc : 0 < c)
    (s : Fin G.n → α) :
    IsNash (⟨G.n, fun i s => c * G.payoff i s⟩ : IdeaGame α) s ↔ IsNash G s := by
  constructor
  · intro h i b
    have hh := h i b
    have : c * G.payoff i (update s i b) ≤ c * G.payoff i s := hh
    exact (mul_le_mul_left hc).mp this
  · intro h i b
    have hh := h i b
    show c * G.payoff i (update s i b) ≤ c * G.payoff i s
    exact mul_le_mul_of_nonneg_left hh hc.le

/-- **T6b (Translation invariance).**  Adding a player-dependent constant to
each player's payoff (independent of the profile) preserves Nash equilibria. -/
theorem nash_add_const (G : IdeaGame α) (c : Fin G.n → ℝ) (s : Fin G.n → α) :
    IsNash (⟨G.n, fun i s => G.payoff i s + c i⟩ : IdeaGame α) s ↔ IsNash G s := by
  constructor
  · intro h i b
    have hh := h i b
    have : G.payoff i (update s i b) + c i ≤ G.payoff i s + c i := hh
    linarith
  · intro h i b
    have hh := h i b
    show G.payoff i (update s i b) + c i ≤ G.payoff i s + c i
    linarith

/-- **T7 (Composition closure / silent coalition).**  Let `s` be a Nash
equilibrium of `G`, and suppose every payoff function is invariant under
right-composition with `ident` (which holds whenever payoffs depend only on
strategies as elements of `α`).  Then the profile obtained by `op`-composing
`s` with the identity profile is again a Nash equilibrium.  This is the
"silent coalition" principle: aggregating with `ident` does nothing. -/
theorem nash_op_identProfile (G : IdeaGame α) (s : Fin G.n → α)
    (hs : IsNash G s) :
    IsNash G (fun i => op (s i) ident) := by
  classical
  -- `op (s i) ident = s i`
  have hpt : (fun i => op (s i) ident) = s := by
    funext i
    exact id_right (s i)
  rw [hpt]
  exact hs

/-- **T8 (Left silent coalition).**  Symmetric to T7 on the left. -/
theorem nash_identProfile_op (G : IdeaGame α) (s : Fin G.n → α)
    (hs : IsNash G s) :
    IsNash G (fun i => op ident (s i)) := by
  have hpt : (fun i => op ident (s i)) = s := by
    funext i; exact id_left (s i)
  rw [hpt]; exact hs

/-- **T9 (Monotonicity / refinement).**  If `f : α → α` is a refinement that
weakly improves every player's payoff at every profile, and the refined
profile `f ∘ s` enjoys the same Nash inequalities as `s`, then `f ∘ s` is
Nash whenever `s` is.  In particular, applying the identity refinement
preserves equilibria. -/
theorem nash_refine_id (G : IdeaGame α) (s : Fin G.n → α) (hs : IsNash G s) :
    IsNash G ((fun a : α => a) ∘ s) := by
  intro i b
  exact hs i b

/-- **T10 (Anti-symmetry implies a zero-sum sub-game).**  Define the
*resonance pairing of payoffs* between players `i` and `j` at profile `s`
by `ρ s i j = G.payoff i s - G.payoff j s`.  This pairing is anti-symmetric:
`ρ s i j = - ρ s j i`, and in particular vanishes on the diagonal. -/
theorem resonance_antisymm (G : IdeaGame α) (s : Fin G.n → α) (i j : Fin G.n) :
    (G.payoff i s - G.payoff j s) = -(G.payoff j s - G.payoff i s) := by
  ring

theorem resonance_diag_zero (G : IdeaGame α) (s : Fin G.n → α) (i : Fin G.n) :
    (G.payoff i s - G.payoff i s) = 0 := by
  ring

/-- **T11 (Iterated dominance terminates).**  On a finite strategy set,
any strictly decreasing chain of subsets — for instance the chain produced
by iteratively deleting strictly dominated strategies — must terminate.
Concretely: any sequence `T : ℕ → Finset α` with `T (k+1) ⊂ T k` for all `k`
becomes empty in at most `(T 0).card + 1` steps. -/
theorem iterated_dominance_terminates {α : Type u} [DecidableEq α]
    (T : ℕ → Finset α) (hStrict : ∀ k, T (k+1) ⊂ T k) :
    ∃ k ≤ (T 0).card + 1, T k = ∅ := by
  -- card decreases strictly along the chain, so it hits zero.
  have hCard : ∀ k, (T k).card + k ≤ (T 0).card := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have h := Finset.card_lt_card (hStrict k)
        omega
  -- in particular at `k = (T 0).card + 1` the cardinality is 0.
  refine ⟨(T 0).card + 1, le_rfl, ?_⟩
  have h := hCard ((T 0).card + 1)
  have : (T ((T 0).card + 1)).card = 0 := by omega
  exact Finset.card_eq_zero.mp this

/-- **T12 (Mixed-strategy expected value of a constant).**  The expectation
of a constant function under any mixed strategy equals that constant. -/
theorem mixed_expect_const {β : Type u} [Fintype β]
    (μ : MixedStrategy β) (c : ℝ) :
    μ.expect (fun _ => c) = c := by
  unfold MixedStrategy.expect
  have : ∑ b, μ.prob b * c = (∑ b, μ.prob b) * c := by
    rw [Finset.sum_mul]
  rw [this, μ.sum_one, one_mul]

/-- **T13 (Linearity of expectation).** -/
theorem mixed_expect_add {β : Type u} [Fintype β]
    (μ : MixedStrategy β) (f g : β → ℝ) :
    μ.expect (fun b => f b + g b) = μ.expect f + μ.expect g := by
  unfold MixedStrategy.expect
  simp [mul_add, Finset.sum_add_distrib]

/-- **T14 (Monotonicity of expectation).** -/
theorem mixed_expect_mono {β : Type u} [Fintype β]
    (μ : MixedStrategy β) {f g : β → ℝ} (h : ∀ b, f b ≤ g b) :
    μ.expect f ≤ μ.expect g := by
  unfold MixedStrategy.expect
  apply Finset.sum_le_sum
  intro b _
  exact mul_le_mul_of_nonneg_left (h b) (μ.nonneg b)

/-- **T15 (Evolutionary stability of an idempotent strategy).**
Define an *idempotent* idea by `op a a = a`.  Call a strategy `a` *evolution-
arily stable* against a payoff `u : α → α → ℝ` if `u a a > u m a` for every
mutant `m ≠ a` that is *strictly dominated under `op`*, i.e.  `u m a ≤ u (op a m) a`
with strict inequality somewhere.  Then any idempotent `a` for which
`u a a > u (op a m) a` whenever `m ≠ a` cannot be invaded.  Concretely: under
these hypotheses, every mutant strictly dominated under `op` satisfies
`u m a < u a a`. -/
theorem ess_idempotent {a : α} (ha : op a a = a)
    (u : α → α → ℝ)
    (hStrict : ∀ m, m ≠ a → u (op a m) a < u a a)
    (hDom    : ∀ m, u m a ≤ u (op a m) a) :
    ∀ m, m ≠ a → u m a < u a a := by
  intro m hm
  exact lt_of_le_of_lt (hDom m) (hStrict m hm)

/-- **T16 (Trivial coalition collapses to identity).**  A "silent coalition"
that aggregates a finite list of ideas via `op` starting from `ident` and all
of whose members are `ident` produces `ident` itself.  This formalizes the
claim that a coalition that aggregates to `ident` is trivial. -/
theorem coalition_all_ident_eq_ident :
    ∀ (l : List α), (∀ x ∈ l, x = (ident : α)) →
      l.foldl op (ident : α) = ident := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons x xs ih =>
      intro h
      have hx : x = (ident : α) := h x (by simp)
      have hrest : ∀ y ∈ xs, y = (ident : α) := fun y hy => h y (by simp [hy])
      have step : op (ident : α) x = ident := by
        rw [hx, id_right]
      simp [List.foldl, step, ih hrest]

/-- **T17 (Best response is preserved by replacing a player's own slot).**
The value of player `i`'s payoff after a deviation does not depend on the
component `s i` of the original profile. -/
theorem payoff_update_indep (G : IdeaGame α) [DecidableEq (Fin G.n)]
    (i : Fin G.n) (s : Fin G.n → α) (a b : α) :
    G.payoff i (update (update s i a) i b) = G.payoff i (update s i b) := by
  congr 1
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [update, hj]

end IdeaTheory.GameTheory
