import Mathlib.Tactic
import IdeaTheory.Foundations

/-!
# IdeaTheory.Extensions.Diffusion

A small dynamical layer on top of `IdeaTheoryStructure`: a finite
*population* of agents, each holding an idea, evolves under a local
**transmission rule** in which every agent recomposes its own idea with that
of its left neighbor, with cyclic boundary.

Twelve+ structural lemmas are proven — length preservation, identity-fixed
populations, the semigroup law for iteration, aggregate invariants, a
"strong tie" reordering lemma, an idempotent-threshold lemma, convergence on
identity populations, Rogers-style monotone adoption under non-erasing rules,
and a Granovetter weak-tie strict increase. All proofs are tactic-driven; no
`sorry`, no `admit`.
-/

namespace IdeaTheory.Diffusion

open IdeaTheory IdeaTheoryStructure

variable {α : Type*} [IdeaTheoryStructure α]

/-! ## §1. Populations and the cyclic transmission step -/

/-- A population is just a finite list of agents, each carrying an idea. -/
abbrev Population (α : Type*) := List α

/-- `lastEl x xs` returns the last element of `x :: xs`. -/
def lastEl (x : α) : List α → α
  | []      => x
  | y :: ys => lastEl y ys

@[simp] theorem lastEl_nil (x : α) : lastEl x ([] : List α) = x := rfl

@[simp] theorem lastEl_cons (x y : α) (ys : List α) :
    lastEl x (y :: ys) = lastEl y ys := rfl

/-- Walk left-to-right composing each element with the running left neighbor. -/
def stepWith (prev : α) : List α → List α
  | []      => []
  | x :: xs => op prev x :: stepWith x xs

@[simp] theorem stepWith_nil (p : α) : stepWith p ([] : List α) = [] := rfl

@[simp] theorem stepWith_cons (p x : α) (xs : List α) :
    stepWith p (x :: xs) = op p x :: stepWith x xs := rfl

/-- Cyclic transmission step: each agent composes its left neighbor's idea
with its own; agent `0` uses the last agent as left neighbor. -/
def step : List α → List α
  | []      => []
  | y :: ys => stepWith (lastEl y ys) (y :: ys)

@[simp] theorem step_nil : step ([] : List α) = [] := rfl

theorem step_cons (y : α) (ys : List α) :
    step (y :: ys) = stepWith (lastEl y ys) (y :: ys) := rfl

/-- Iterating the step `n` times starting from a constant population of size
`L` of the idea `a`. -/
def propagated (a : α) (L n : Nat) : Population α :=
  step^[n] (List.replicate L a)

/-! ## §2. Length preservation -/

/-- `stepWith` preserves length. -/
theorem stepWith_length (p : α) (xs : List α) :
    (stepWith p xs).length = xs.length := by
  induction xs generalizing p with
  | nil => rfl
  | cons x xs ih => simp [stepWith, ih]

/-- **(T1)** `step` preserves population size. -/
theorem step_length (xs : List α) : (step xs).length = xs.length := by
  cases xs with
  | nil => rfl
  | cons y ys => simp [step, stepWith_length]

/-- Iterating `step` preserves population size. -/
theorem iterate_step_length (n : Nat) (xs : List α) :
    (step^[n] xs).length = xs.length := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', step_length, ih]

/-! ## §3. The all-`ident` population is a fixed point -/

/-- Walking `stepWith ident` over a list of `ident`s reproduces the list. -/
theorem stepWith_replicate_ident (n : Nat) :
    stepWith (ident : α) (List.replicate n ident) = List.replicate n ident := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show stepWith ident (ident :: List.replicate n ident)
        = ident :: List.replicate n ident
    rw [stepWith_cons, id_left, ih]

/-- The "last element" of a constant list of `a`s is `a`. -/
theorem lastEl_replicate_self (a : α) (n : Nat) :
    lastEl a (List.replicate n a) = a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show lastEl a (a :: List.replicate n a) = a
    rw [lastEl_cons, ih]

/-- **(T2)** `step` is the identity on the all-`ident` population. -/
theorem step_replicate_ident (n : Nat) :
    step (List.replicate n (ident : α)) = List.replicate n ident := by
  cases n with
  | zero => rfl
  | succ n =>
    show step (ident :: List.replicate n ident) = ident :: List.replicate n ident
    rw [step_cons]
    have hlast : lastEl (ident : α) (List.replicate n ident) = ident :=
      lastEl_replicate_self ident n
    rw [hlast]
    exact stepWith_replicate_ident (n+1)

/-! ## §4. Iteration and the semigroup law -/

/-- **(T3)** `step^(n+m)` factors as `step^n ∘ step^m` — the semigroup law for
iterated transmission. -/
theorem iterate_step_add (n m : Nat) (xs : List α) :
    step^[n + m] xs = step^[n] (step^[m] xs) :=
  Function.iterate_add_apply step n m xs

/-- Convergence on identity populations: every iterate of the all-`ident`
population is itself. -/
theorem iterate_step_replicate_ident (L n : Nat) :
    step^[n] (List.replicate L (ident : α)) = List.replicate L ident := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, step_replicate_ident]

/-- **(T4)** Convergence in `propagated` form: starting from a constant
identity population, every time slice equals the original. -/
theorem propagated_ident (L n : Nat) :
    propagated (ident : α) L n = List.replicate L ident :=
  iterate_step_replicate_ident L n

/-! ## §5. The aggregate of a population -/

/-- The total composed product of a population, with neutral element `ident`. -/
def aggregate : List α → α := List.foldr op ident

@[simp] theorem aggregate_nil : aggregate ([] : List α) = ident := rfl

@[simp] theorem aggregate_cons (x : α) (xs : List α) :
    aggregate (x :: xs) = op x (aggregate xs) := rfl

/-- A constant `ident` list aggregates to `ident`. -/
theorem aggregate_replicate_ident (k : Nat) :
    aggregate (List.replicate k (ident : α)) = ident := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show op ident (aggregate (List.replicate k ident)) = ident
    rw [id_left, ih]

/-- **(T5)** Aggregate is invariant under appending an `ident`-suffix:
extending a population with bystanders does not change its aggregate. -/
theorem aggregate_append_ident_replicate (xs : List α) (k : Nat) :
    aggregate (xs ++ List.replicate k (ident : α)) = aggregate xs := by
  unfold aggregate
  rw [List.foldr_append]
  congr 1
  exact aggregate_replicate_ident k

/-- Aggregate is invariant under prepending an `ident`-prefix. -/
theorem aggregate_replicate_ident_append (k : Nat) (xs : List α) :
    aggregate (List.replicate k (ident : α) ++ xs) = aggregate xs := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show aggregate (ident :: (List.replicate k ident ++ xs)) = aggregate xs
    rw [aggregate_cons, id_left, ih]

/-! ## §6. Strong-tie commutativity reordering -/

/-- **(T6, strong tie)** If two adjacent ideas commute, they may be swapped
without changing the aggregate of the surrounding population. -/
theorem aggregate_swap_adjacent_commute
    (xs ys : List α) (a b : α) (h : op a b = op b a) :
    aggregate (xs ++ a :: b :: ys) = aggregate (xs ++ b :: a :: ys) := by
  induction xs with
  | nil =>
    show op a (op b (aggregate ys)) = op b (op a (aggregate ys))
    rw [← assoc, h, assoc]
  | cons x xs ih =>
    show op x (aggregate (xs ++ a :: b :: ys))
        = op x (aggregate (xs ++ b :: a :: ys))
    rw [ih]

/-! ## §7. Threshold lemma for idempotent ideas -/

/-- Walking `stepWith a` over a list of idempotent `a`s yields the same list. -/
theorem stepWith_replicate_idempotent (a : α) (ha : op a a = a) (n : Nat) :
    stepWith a (List.replicate n a) = List.replicate n a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show stepWith a (a :: List.replicate n a) = a :: List.replicate n a
    rw [stepWith_cons, ha, ih]

/-- **(T7, threshold)** If a fraction `1` (i.e. all `n` agents) hold the
idempotent idea `a`, then after one step *all* agents still hold `a` — a clean
upper-threshold instance of the general statement
"if at least `k/n` agents already hold idempotent `a`,
then ≥ `k/n` still hold an `a`-related idea afterwards", taken at `k = n`. -/
theorem step_replicate_idempotent (a : α) (ha : op a a = a) (n : Nat) :
    step (List.replicate (n+1) a) = List.replicate (n+1) a := by
  show step (a :: List.replicate n a) = a :: List.replicate n a
  rw [step_cons, lastEl_replicate_self]
  exact stepWith_replicate_idempotent a ha (n+1)

/-! ## §8. Rogers-style adoption monotonicity -/

/-- The number of *adopters* — agents holding a non-identity idea. -/
def adopters [DecidableEq α] (xs : List α) : Nat :=
  xs.countP (fun x => decide (x ≠ ident))

/-- A transmission rule is **non-erasing** if it never decreases adoption. -/
def NonErasing [DecidableEq α] (f : List α → List α) : Prop :=
  ∀ xs, adopters xs ≤ adopters (f xs)

/-- **(T8, Rogers)** Iterating a non-erasing rule yields a monotone
non-decreasing adoption count. -/
theorem rogers_monotone [DecidableEq α] {f : List α → List α}
    (hf : NonErasing f) (xs : List α) (n : Nat) :
    adopters xs ≤ adopters (f^[n] xs) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact le_trans ih (hf (f^[n] xs))

/-- The identity rule is non-erasing. -/
theorem nonErasing_id [DecidableEq α] : NonErasing (id : List α → List α) :=
  fun _ => le_refl _

/-! ## §9. The Granovetter weak-tie effect -/

/-- The "last element" of a list of `n+1` `a`s shifted by an arbitrary head. -/
theorem lastEl_replicate_succ (x a : α) (n : Nat) :
    lastEl x (List.replicate (n+1) a) = a := by
  induction n generalizing x with
  | zero =>
    show lastEl x (a :: ([] : List α)) = a
    rfl
  | succ n ih =>
    show lastEl x (a :: List.replicate (n+1) a) = a
    rw [lastEl_cons]
    exact ih a

/-- One bilateral step on a *single non-identity insertion* into an otherwise
all-`ident` population: the lone non-identity duplicates to the right. -/
theorem step_single_a_ident (a : α) (j : Nat) :
    step (a :: List.replicate (j+1) (ident : α))
        = a :: a :: List.replicate j ident := by
  show stepWith (lastEl a (List.replicate (j+1) (ident : α)))
        (a :: List.replicate (j+1) ident)
      = a :: a :: List.replicate j ident
  rw [lastEl_replicate_succ]
  show op ident a :: stepWith a (List.replicate (j+1) ident)
      = a :: a :: List.replicate j ident
  rw [id_left]
  show a :: stepWith a (ident :: List.replicate j ident)
      = a :: a :: List.replicate j ident
  congr 1
  rw [stepWith_cons, id_right]
  congr 1
  exact stepWith_replicate_ident j

/-- **(T9, Granovetter weak tie)** A single non-`ident` insertion into an
all-`ident` population (with at least one bystander) yields *strictly more*
non-`ident` agents after a single bilateral transmission step. -/
theorem granovetter_weak_tie [DecidableEq α] (a : α) (ha : a ≠ ident) (j : Nat) :
    adopters (a :: List.replicate (j+1) (ident : α))
      < adopters (step (a :: List.replicate (j+1) ident)) := by
  rw [step_single_a_ident]
  -- Compute both sides explicitly.
  have hcount : ∀ k, ((List.replicate k (ident : α)).countP
        (fun x => decide (x ≠ ident))) = 0 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      show ((ident :: List.replicate k (ident : α)).countP
              (fun x => decide (x ≠ ident))) = 0
      rw [List.countP_cons]
      simp [ih]
  unfold adopters
  show (a :: List.replicate (j+1) (ident : α)).countP
          (fun x => decide (x ≠ ident))
      < (a :: a :: List.replicate j (ident : α)).countP
          (fun x => decide (x ≠ ident))
  rw [List.countP_cons, List.countP_cons, List.countP_cons, hcount, hcount]
  simp [ha]

/-! ## §10. Further structural lemmas -/

/-- The empty population is fixed by every iterate of `step`. -/
theorem iterate_step_nil (n : Nat) : step^[n] ([] : List α) = [] := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih]; rfl

/-- A length-1 population is mapped to its self-composition. -/
theorem step_singleton (a : α) : step ([a] : List α) = [op a a] := by
  show stepWith (lastEl a ([] : List α)) [a] = [op a a]
  rfl

/-- A length-1 idempotent population is fixed. -/
theorem step_singleton_idempotent (a : α) (ha : op a a = a) :
    step ([a] : List α) = [a] := by
  rw [step_singleton, ha]

/-- The aggregate of the all-`ident` population is `ident`. -/
theorem aggregate_replicate_ident_eq (k : Nat) :
    aggregate (List.replicate k (ident : α)) = ident :=
  aggregate_replicate_ident k

/-- Aggregate is multiplicative across concatenation. -/
theorem aggregate_append (xs ys : List α) :
    aggregate (xs ++ ys) = List.foldr op (aggregate ys) xs := by
  unfold aggregate
  rw [List.foldr_append]

/-- A constant population's aggregate is the `n`-fold self-composition;
in particular, an idempotent `a` aggregates to `a` over any non-empty
constant population. -/
theorem aggregate_replicate_idempotent (a : α) (ha : op a a = a) (n : Nat) :
    aggregate (List.replicate (n+1) a) = a := by
  induction n with
  | zero =>
    show op a ident = a
    exact id_right a
  | succ n ih =>
    show op a (aggregate (List.replicate (n+1) a)) = a
    rw [ih, ha]

end IdeaTheory.Diffusion
