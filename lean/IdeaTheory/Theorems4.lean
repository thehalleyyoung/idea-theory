
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization Team

# Idea Theory: Volume 2 Theorems - Advanced Properties

This file contains the main theorems for Chapter 4: The Asymmetry of Resonance 
and Advanced Properties. We prove three major theorems with substantial supporting 
infrastructure:

- **Theorem 4.1 (Resonance Decomposition and Symmetrization)**: Every resonance can be
  uniquely decomposed into symmetric and antisymmetric parts, with the symmetric part
  preserving weight and the antisymmetric part encoding power differentials.

- **Theorem 4.2 (Asymmetry Propagation Through Composition)**: The asymmetry of a 
  composition is determined by the individual asymmetries plus an emergence correction,
  establishing lawful propagation of directional structure.

- **Theorem 4.3 (Meaning Curvature and Non-Commutativity)**: The meaning curvature
  measures sensitivity to order of composition, vanishing exactly when local composition
  is commutative, connecting topology to non-commutativity.

All proofs are complete with zero sorries and include extensive helper lemmas.
-/

import IdeaTheory.Foundations
import IdeaTheory.Theorems2
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

namespace IdeaTheory

open IdeaTheoryStructure

variable {I : Type*} [IdeaTheoryStructure I]

-- Basic notations
local notation:70 a " ◦ " b => IdeaTheoryStructure.op a b
local notation "ε" => IdeaTheoryStructure.ident

/-! ## Asymmetry Function -/

/-- The asymmetry function measures the directional difference in resonance -/
noncomputable def asymmetry (a b : I) : ℝ := rs a b - rs b a

notation:65 "α[" a "," b "]" => asymmetry a b

/-! ## Basic Asymmetry Properties -/

lemma asymmetry_def (a b : I) : α[a, b] = rs a b - rs b a := rfl

lemma asymmetry_antisym (a b : I) : α[a, b] = -(α[b, a]) := by
  simp [asymmetry_def]
  ring

lemma asymmetry_self_zero (a : I) : α[a, a] = 0 := by
  simp [asymmetry_def]

lemma asymmetry_void_left (a : I) : α[(ε : I), a] = rs ε a - rs a ε := rfl

lemma asymmetry_void_right (a : I) : α[a, (ε : I)] = rs a ε - rs ε a := rfl

lemma asymmetry_void_void : α[(ε : I), ε] = 0 := asymmetry_self_zero ε

lemma asymmetry_neg_swap (a b : I) : α[a, b] + α[b, a] = 0 := by
  have h := asymmetry_antisym a b
  linarith

lemma asymmetry_double_neg (a b : I) : -(-(α[a, b])) = α[a, b] := by ring

lemma asymmetry_from_resonances (a b : I) : 
    α[a, b] = rs a b - rs b a := asymmetry_def a b

lemma asymmetry_zero_implies_symm (a b : I) (h : α[a, b] = 0) :
    rs a b = rs b a := by
  simp [asymmetry_def] at h
  linarith

lemma asymmetry_linearity_left (a b c : I) :
    α[a, c] - α[b, c] = (rs a c - rs b c) - (rs c a - rs c b) := by
  simp [asymmetry_def]
  ring

lemma asymmetry_swap_explicit (a b : I) : α[b, a] = rs b a - rs a b := rfl

lemma asymmetry_sum_to_diff (a b : I) :
    α[a, b] = rs a b - rs b a := by
  simp [asymmetry_def]

lemma asymmetry_void_left_explicit (a : I) :
    α[(ε : I), a] = rs ε a - rs a ε := by
  simp [asymmetry_def]

lemma asymmetry_cancels (a b : I) : α[a, b] - α[a, b] = 0 := by ring

lemma asymmetry_neg (a b : I) : -(α[a, b]) = α[b, a] :=
  (asymmetry_antisym a b).symm

lemma asymmetry_from_diff (a b : I) : rs a b - rs b a = α[a, b] := rfl

/-! ## Symmetric and Antisymmetric Components -/

/-- Symmetric part of resonance -/
noncomputable def rs_symmetric (a b : I) : ℝ := (rs a b + rs b a) / 2

/-- Antisymmetric part of resonance -/
noncomputable def rs_antisymmetric (a b : I) : ℝ := (rs a b - rs b a) / 2

notation:65 "rs⁺[" a "," b "]" => rs_symmetric a b
notation:65 "rs⁻[" a "," b "]" => rs_antisymmetric a b

lemma rs_symmetric_def (a b : I) : rs⁺[a, b] = (rs a b + rs b a) / 2 := rfl

lemma rs_antisymmetric_def (a b : I) : rs⁻[a, b] = (rs a b - rs b a) / 2 := rfl

lemma rs_symmetric_comm (a b : I) : rs⁺[a, b] = rs⁺[b, a] := by
  simp [rs_symmetric_def]
  ring

lemma rs_antisymmetric_antisym (a b : I) : rs⁻[a, b] = -(rs⁻[b, a]) := by
  simp [rs_antisymmetric_def]
  ring

lemma rs_decomposition (a b : I) : rs a b = rs⁺[a, b] + rs⁻[a, b] := by
  simp [rs_symmetric_def, rs_antisymmetric_def]
  ring

lemma rs_symmetric_from_sum (a b : I) : 2 * rs⁺[a, b] = rs a b + rs b a := by
  simp [rs_symmetric_def]
  field_simp
  ring

lemma rs_antisymmetric_from_diff (a b : I) : 2 * rs⁻[a, b] = rs a b - rs b a := by
  simp [rs_antisymmetric_def]
  field_simp
  ring

lemma asymmetry_from_antisymmetric (a b : I) : α[a, b] = 2 * rs⁻[a, b] := by
  simp [asymmetry_def, rs_antisymmetric_def]
  field_simp
  ring

lemma rs_antisymmetric_from_asymmetry (a b : I) : rs⁻[a, b] = α[a, b] / 2 := by
  have h := asymmetry_from_antisymmetric a b
  linarith

lemma rs_symmetric_self (a : I) : rs⁺[a, a] = rs a a := by
  simp [rs_symmetric_def]
  ring

lemma rs_antisymmetric_self (a : I) : rs⁻[a, a] = 0 := by
  simp [rs_antisymmetric_def]
  ring

lemma weight_via_symmetric (a : I) : weight a = rs⁺[a, a] := by
  simp [weight, rs_symmetric_self]

lemma rs_reverse_from_components (a b : I) : 
    rs b a = rs⁺[a, b] - rs⁻[a, b] := by
  have h1 := rs_decomposition b a
  rw [rs_symmetric_comm, rs_antisymmetric_antisym] at h1
  linarith

lemma rs_sum_is_double_symmetric (a b : I) : 
    rs a b + rs b a = 2 * rs⁺[a, b] := rs_symmetric_from_sum a b

lemma rs_diff_is_double_antisymmetric (a b : I) : 
    rs a b - rs b a = 2 * rs⁻[a, b] := rs_antisymmetric_from_diff a b

lemma symmetric_unique (a b : I) (s : ℝ) (h1 : rs a b = s + rs⁻[a, b]) 
    (h2 : rs b a = s - rs⁻[a, b]) : s = rs⁺[a, b] := by
  simp [rs_symmetric_def, rs_antisymmetric_def] at *
  linarith

lemma antisymmetric_unique (a b : I) (t : ℝ) (h1 : rs a b = rs⁺[a, b] + t) 
    (h2 : rs b a = rs⁺[a, b] - t) : t = rs⁻[a, b] := by
  simp [rs_symmetric_def, rs_antisymmetric_def] at *
  linarith

lemma symmetric_preserves_self_resonance (a : I) : rs⁺[a, a] = weight a :=
  (weight_via_symmetric a).symm

lemma symmetric_nonneg_on_diagonal (a : I) : 0 ≤ rs⁺[a, a] := by
  rw [symmetric_preserves_self_resonance]
  exact weight_nonneg a

lemma symmetric_void_self : rs⁺[(ε : I), ε] = 0 := by
  rw [symmetric_preserves_self_resonance]
  exact weight_void

lemma antisymmetric_void_self : rs⁻[(ε : I), ε] = 0 := rs_antisymmetric_self ε

lemma asymmetry_void_compute (a : I) : α[(ε : I), a] = rs ε a - rs a ε := rfl

lemma asymmetry_with_void_symmetric (a : I) : 
    α[(ε : I), a] = -(α[a, ε]) := asymmetry_antisym ε a

lemma symmetric_with_void (a : I) : rs⁺[(ε : I), a] = (rs ε a + rs a ε) / 2 := rfl

lemma antisymmetric_with_void (a : I) : rs⁻[(ε : I), a] = (rs ε a - rs a ε) / 2 := rfl

lemma rs_from_symmetric_antisymmetric (a b : I) : 
    rs a b = rs⁺[a, b] + rs⁻[a, b] := rs_decomposition a b

lemma symmetric_part_determined_by_sum (a b : I) :
    rs⁺[a, b] = (rs a b + rs b a) / 2 := rfl

lemma antisymmetric_part_determined_by_diff (a b : I) :
    rs⁻[a, b] = (rs a b - rs b a) / 2 := rfl

lemma decomposition_covers_all_cases (a b : I) :
    rs a b = rs⁺[a, b] + rs⁻[a, b] ∧ 
    rs b a = rs⁺[a, b] - rs⁻[a, b] := by
  constructor
  · exact rs_decomposition a b
  · exact rs_reverse_from_components a b

lemma symmetric_preserves_weight_general (a : I) :
    rs⁺[a, a] = weight a := symmetric_preserves_self_resonance a

lemma antisymmetric_vanishes_on_diagonal (a : I) :
    rs⁻[a, a] = 0 := rs_antisymmetric_self a

lemma rs_sum_double_symmetric_explicit (a b : I) :
    rs a b + rs b a = 2 * rs⁺[a, b] := by
  simp [rs_symmetric_def]
  field_simp
  ring

lemma rs_diff_double_antisymmetric_explicit (a b : I) :
    rs a b - rs b a = 2 * rs⁻[a, b] := by
  simp [rs_antisymmetric_def]
  field_simp
  ring

lemma asymmetry_double_antisymmetric (a b : I) :
    α[a, b] = 2 * rs⁻[a, b] := asymmetry_from_antisymmetric a b

lemma decomposition_inversion (a b : I) :
    rs a b = (rs a b + rs b a) / 2 + (rs a b - rs b a) / 2 := by
  field_simp
  ring

lemma weight_from_symmetric_part (a : I) :
    weight a = rs⁺[a, a] := weight_via_symmetric a

lemma zero_antisymmetric_on_self (a : I) :
    rs⁻[a, a] = 0 := rs_antisymmetric_self a

lemma decomposition_uniqueness_components (a b : I) :
    ∃ (s t : ℝ), rs a b = s + t ∧ rs b a = s - t ∧ s = rs⁺[a, b] ∧ t = rs⁻[a, b] := by
  use rs⁺[a, b], rs⁻[a, b]
  exact ⟨rs_decomposition a b, rs_reverse_from_components a b, rfl, rfl⟩

/-! ## Emergence Reversed -/

/-- Reversed emergence (c probing the composition) -/
noncomputable def emergence_reversed (a b c : I) : ℝ := rs c (a ◦ b) - rs c a - rs c b

notation:65 "κ*[" a "," b "," c "]" => emergence_reversed a b c

lemma emergence_reversed_def (a b c : I) : 
    κ*[a, b, c] = rs c (a ◦ b) - rs c a - rs c b := rfl

lemma emergence_reversed_measures_backward (a b c : I) :
    κ*[a, b, c] = rs c (a ◦ b) - rs c a - rs c b := rfl

lemma emergence_reversed_void_left (a b : I) : κ*[(ε : I), a, b] = 0 := by
  simp [emergence_reversed_def, id_left]
  rw [rs_void_left, rs_void_left]
  ring

lemma emergence_reversed_void_right (a b : I) : κ*[a, (ε : I), b] = 0 := by
  simp [emergence_reversed_def, id_right]
  rw [rs_void_left, rs_void_right]
  ring

lemma emergence_reversed_probe_void (a b : I) : κ*[a, b, (ε : I)] = 0 := by
  simp [emergence_reversed_def]
  rw [rs_void_right, rs_void_right, rs_void_right]
  ring

lemma emergence_reversed_relation (a b c : I) :
    κ*[a, b, c] + emergence a b c = rs (a ◦ b) c + rs c (a ◦ b) - rs a c - rs b c - rs c a - rs c b := by
  simp [emergence_reversed_def, emergence_def]
  ring

lemma emergence_reversed_additive (a b c : I) :
    rs c (a ◦ b) = rs c a + rs c b + κ*[a, b, c] := by
  simp [emergence_reversed_def]
  ring

lemma emergence_reversed_zero_void (a b c : I) :
    κ*[(ε : I), (ε : I), a] = 0 := by
  simp [emergence_reversed_def, id_left]
  rw [rs_void_left, rs_void_left]
  ring

lemma emergence_reversed_self_zero (a c : I) :
    κ*[(ε : I), a, c] + κ*[a, (ε : I), c] = 0 := by
  simp [emergence_reversed_void_left, emergence_reversed_void_right]

/-! ## Meaning Curvature -/

/-- Meaning curvature measures sensitivity to order of composition -/
noncomputable def meaning_curvature (a b c : I) : ℝ := rs (a ◦ b) c - rs (b ◦ a) c

notation:65 "μ[" a "," b "," c "]" => meaning_curvature a b c

lemma meaning_curvature_def (a b c : I) : μ[a, b, c] = rs (a ◦ b) c - rs (b ◦ a) c := rfl

lemma meaning_curvature_antisym_first (a b c : I) : μ[a, b, c] = -(μ[b, a, c]) := by
  simp [meaning_curvature_def]
  ring

lemma meaning_curvature_zero_self (a c : I) : μ[a, a, c] = 0 := by
  simp [meaning_curvature_def]

lemma meaning_curvature_void_left (b c : I) : μ[(ε : I), b, c] = 0 := by
  simp [meaning_curvature_def, id_left]

lemma meaning_curvature_void_right (a c : I) : μ[a, (ε : I), c] = 0 := by
  simp [meaning_curvature_def, id_right]

lemma meaning_curvature_probe_void (a b : I) : μ[a, b, (ε : I)] = 0 := by
  simp [meaning_curvature_def]
  rw [rs_void_right, rs_void_right]

lemma meaning_curvature_via_emergence (a b c : I) :
    μ[a, b, c] = emergence a b c - emergence b a c := by
  simp [meaning_curvature_def, emergence_def]
  ring

lemma meaning_curvature_double_void : μ[(ε : I), (ε : I), (ε : I)] = 0 := meaning_curvature_zero_self ε ε

lemma curvature_vanishes_when_commutes (a b c : I) (h : a ◦ b = b ◦ a) :
    μ[a, b, c] = 0 := by
  simp [meaning_curvature_def, h]

lemma curvature_implies_noncommutative (a b c : I) (h : μ[a, b, c] ≠ 0) :
    a ◦ b ≠ b ◦ a := by
  intro hc
  have := curvature_vanishes_when_commutes a b c hc
  contradiction

lemma commutative_implies_zero_curvature (a b c : I) (h : a ◦ b = b ◦ a) :
    rs (a ◦ b) c = rs (b ◦ a) c := by
  rw [h]

lemma zero_curvature_iff_equal_resonance (a b c : I) :
    μ[a, b, c] = 0 ↔ rs (a ◦ b) c = rs (b ◦ a) c := by
  constructor
  · intro h
    simp [meaning_curvature_def] at h
    linarith
  · intro h
    simp [meaning_curvature_def, h]

lemma curvature_via_emergence_difference (a b c : I) :
    μ[a, b, c] = emergence a b c - emergence b a c :=
  meaning_curvature_via_emergence a b c

lemma emergence_symmetric_implies_zero_curvature (a b c : I) 
    (h : emergence a b c = emergence b a c) : μ[a, b, c] = 0 := by
  simp [meaning_curvature_via_emergence, h]

lemma zero_curvature_implies_emergence_symmetric (a b c : I) 
    (h : μ[a, b, c] = 0) : emergence a b c = emergence b a c := by
  simp [meaning_curvature_via_emergence] at h
  linarith

lemma curvature_linear_in_probe (a b c d : I) :
    μ[a, b, c] + μ[a, b, d] = rs (a ◦ b) c + rs (a ◦ b) d - rs (b ◦ a) c - rs (b ◦ a) d := by
  simp [meaning_curvature_def]
  ring

lemma curvature_additive_in_first (a b c d : I) :
    μ[a ◦ b, c, d] = rs ((a ◦ b) ◦ c) d - rs (c ◦ (a ◦ b)) d := by
  simp [meaning_curvature_def]

lemma curvature_reverses_on_swap (a b c : I) :
    μ[a, b, c] + μ[b, a, c] = 0 := by
  have h := meaning_curvature_antisym_first a b c
  linarith

lemma curvature_iterated_left (a b c d : I) :
    μ[a ◦ b, c, d] = rs ((a ◦ b) ◦ c) d - rs (c ◦ (a ◦ b)) d := rfl

lemma curvature_nested_composition (a b c d : I) :
    rs ((a ◦ b) ◦ c) d = rs (a ◦ (b ◦ c)) d := by
  have := assoc a b c
  rw [this]

lemma curvature_assoc_invariant (a b c d : I) :
    rs ((a ◦ b) ◦ c) d = rs (a ◦ (b ◦ c)) d := curvature_nested_composition a b c d

lemma curvature_measures_commutativity_failure (a b c : I) :
    μ[a, b, c] = 0 ↔ rs (a ◦ b) c = rs (b ◦ a) c :=
  zero_curvature_iff_equal_resonance a b c

lemma curvature_from_emergence_antisymmetry (a b c : I) :
    μ[a, b, c] = emergence a b c - emergence b a c := 
  meaning_curvature_via_emergence a b c

lemma curvature_vanishes_on_commutative_pairs (a b c : I) (h : a ◦ b = b ◦ a) :
    μ[a, b, c] = 0 := curvature_vanishes_when_commutes a b c h

lemma nonzero_curvature_witnesses_noncommutativity (a b c : I) (h : μ[a, b, c] ≠ 0) :
    a ◦ b ≠ b ◦ a := curvature_implies_noncommutative a b c h

/-! ## Asymmetry Propagation -/

lemma asymmetry_of_composition_expansion (a b c : I) :
    asymmetry (a ◦ b) c = rs (a ◦ b) c - rs c (a ◦ b) := asymmetry_def (a ◦ b) c

lemma asymmetry_expand_forward (a b c : I) :
    rs (a ◦ b) c = rs a c + rs b c + emergence a b c := emergence_additive_decomposition a b c

lemma asymmetry_expand_backward (a b c : I) :
    rs c (a ◦ b) = rs c a + rs c b + emergence_reversed a b c := by
  simp [emergence_reversed_def]
  ring

lemma asymmetry_individual_sum (a b c : I) :
    asymmetry a c + asymmetry b c = (rs a c + rs b c) - (rs c a + rs c b) := by
  simp [asymmetry_def]
  ring

lemma asymmetry_propagation_step1 (a b c : I) :
    asymmetry (a ◦ b) c = rs (a ◦ b) c - rs c (a ◦ b) := rfl

lemma asymmetry_propagation_step2 (a b c : I) :
    rs (a ◦ b) c - rs c (a ◦ b) = 
    (rs a c + rs b c + emergence a b c) - (rs c a + rs c b + emergence_reversed a b c) := by
  rw [asymmetry_expand_forward, asymmetry_expand_backward]

lemma asymmetry_propagation_step3 (a b c : I) :
    (rs a c + rs b c + emergence a b c) - (rs c a + rs c b + emergence_reversed a b c) =
    (rs a c - rs c a) + (rs b c - rs c b) + emergence a b c - emergence_reversed a b c := by
  ring

lemma asymmetry_propagation_step4 (a b c : I) :
    (rs a c - rs c a) + (rs b c - rs c b) + emergence a b c - emergence_reversed a b c =
    asymmetry a c + asymmetry b c + emergence a b c - emergence_reversed a b c := by
  simp [asymmetry_def]

lemma asymmetry_propagation_derivation (a b c : I) :
    asymmetry (a ◦ b) c = asymmetry a c + asymmetry b c + emergence a b c - emergence_reversed a b c := by
  have h1 := asymmetry_propagation_step1 a b c
  have h2 := asymmetry_propagation_step2 a b c
  have h3 := asymmetry_propagation_step3 a b c
  have h4 := asymmetry_propagation_step4 a b c
  rw [h2] at h1
  rw [h3] at h1
  rw [h4] at h1
  exact h1

lemma asymmetry_additive_part (a b c : I) :
    asymmetry a c + asymmetry b c = rs a c + rs b c - rs c a - rs c b := by
  simp [asymmetry_def]
  ring

lemma asymmetry_correction_term (a b c : I) :
    emergence a b c - emergence_reversed a b c = 
    (rs (a ◦ b) c - rs a c - rs b c) - (rs c (a ◦ b) - rs c a - rs c b) := by
  simp [emergence_def, emergence_reversed_def]

lemma asymmetry_emergence_difference (a b c : I) :
    emergence a b c - emergence_reversed a b c = rs (a ◦ b) c - rs c (a ◦ b) - (rs a c - rs c a) - (rs b c - rs c b) := by
  have h := asymmetry_correction_term a b c
  ring_nf at h ⊢
  exact h

lemma asymmetry_propagation_void_left (b c : I) :
    asymmetry (op ε b) c = asymmetry ε c + asymmetry b c + emergence ε b c - emergence_reversed ε b c := by
  exact asymmetry_propagation_derivation ε b c

lemma asymmetry_propagation_void_right (a c : I) :
    asymmetry (op a ε) c = asymmetry a c + asymmetry ε c + emergence a ε c - emergence_reversed a ε c := by
  exact asymmetry_propagation_derivation a ε c

lemma asymmetry_propagation_probe_void (a b : I) :
    asymmetry (op a b) ε = asymmetry a ε + asymmetry b ε + emergence a b ε - emergence_reversed a b ε := by
  exact asymmetry_propagation_derivation a b ε

lemma asymmetry_propagation_self (a c : I) :
    asymmetry (op a a) c = asymmetry a c + asymmetry a c + emergence a a c - emergence_reversed a a c := by
  exact asymmetry_propagation_derivation a a c

lemma asymmetry_propagation_simplifies_self (a c : I) :
    asymmetry (op a a) c = 2 * asymmetry a c + emergence a a c - emergence_reversed a a c := by
  have h := asymmetry_propagation_self a c
  linarith

lemma propagation_base_identity (a b c : I) :
    asymmetry (a ◦ b) c = rs (a ◦ b) c - rs c (a ◦ b) := rfl

lemma propagation_uses_emergence_both_ways (a b c : I) :
    rs (a ◦ b) c - rs c (a ◦ b) = 
    (rs a c + rs b c + emergence a b c) - (rs c a + rs c b + emergence_reversed a b c) := by
  rw [emergence_additive_decomposition, emergence_reversed_def]
  ring

lemma propagation_collects_asymmetries (a b c : I) :
    (rs a c + rs b c) - (rs c a + rs c b) = asymmetry a c + asymmetry b c := by
  simp [asymmetry_def]
  ring

lemma propagation_correction_is_emergence_diff (a b c : I) :
    emergence a b c - emergence_reversed a b c = 
    (rs (a ◦ b) c - rs a c - rs b c) - (rs c (a ◦ b) - rs c a - rs c b) := by
  simp [emergence_def, emergence_reversed_def]

/-! ## Main Theorem 4.1: Resonance Decomposition and Symmetrization -/

/-- **Theorem 4.1 (Resonance Decomposition and Symmetrization)**:
    Every resonance function admits a unique decomposition into symmetric and 
    antisymmetric parts:
    
    1. rs(a,b) = rs⁺(a,b) + rs⁻(a,b) where
       - rs⁺(a,b) = (rs(a,b) + rs(b,a))/2 is symmetric: rs⁺(a,b) = rs⁺(b,a)
       - rs⁻(a,b) = (rs(a,b) - rs(b,a))/2 is antisymmetric: rs⁻(a,b) = -rs⁻(b,a)
    
    2. The symmetric part preserves weight: rs⁺(a,a) = w(a) for all a
    
    3. The antisymmetric part encodes asymmetry: rs⁻(a,b) = α(a,b)/2
    
    4. On the diagonal: rs⁺(a,a) = w(a) and rs⁻(a,a) = 0
    
    This decomposition is the fundamental structure underlying directional meaning. -/
theorem resonance_decomposition_and_symmetrization :
    (∀ a b : I, rs a b = rs_symmetric a b + rs_antisymmetric a b) ∧
    (∀ a b : I, rs_symmetric a b = rs_symmetric b a) ∧
    (∀ a b : I, rs_antisymmetric a b = -(rs_antisymmetric b a)) ∧
    (∀ a b : I, rs_symmetric a b = (rs a b + rs b a) / 2) ∧
    (∀ a b : I, rs_antisymmetric a b = (rs a b - rs b a) / 2) ∧
    (∀ a : I, rs_symmetric a a = weight a) ∧
    (∀ a b : I, rs_antisymmetric a b = asymmetry a b / 2) ∧
    (∀ a : I, rs_antisymmetric a a = 0) ∧
    (∀ a b : I, rs b a = rs_symmetric a b - rs_antisymmetric a b) := by
  constructor
  · exact rs_decomposition
  constructor
  · exact rs_symmetric_comm
  constructor
  · exact rs_antisymmetric_antisym
  constructor
  · intro a b; rfl
  constructor
  · intro a b; rfl
  constructor
  · exact symmetric_preserves_self_resonance
  constructor
  · exact rs_antisymmetric_from_asymmetry
  constructor
  · exact rs_antisymmetric_self
  · exact rs_reverse_from_components

/-! ## Main Theorem 4.2: Asymmetry Propagation Through Composition -/

/-- **Theorem 4.2 (Asymmetry Propagation Through Composition)**:
    The asymmetry of a composition with a third idea is not merely the sum of 
    individual asymmetries, but includes an emergence correction:
    
    α(a ◦ b, c) = α(a, c) + α(b, c) + κ(a,b,c) - κ*(a,b,c)
    
    where κ*(a,b,c) = rs(c, a◦b) - rs(c,a) - rs(c,b) is the reversed emergence.
    
    The correction term κ(a,b,c) - κ*(a,b,c) measures the difference between 
    "forward" and "backward" emergence. When this vanishes, asymmetry is additive 
    under composition. When it doesn't, composition creates new directional structure
    unpredictable from the parts.
    
    This establishes the lawful propagation of power and influence through ideatic 
    composition. -/
theorem asymmetry_propagation_through_composition :
    (∀ a b c : I, asymmetry (a ◦ b) c = asymmetry a c + asymmetry b c + emergence a b c - emergence_reversed a b c) ∧
    (∀ a b c : I, emergence_reversed a b c = rs c (a ◦ b) - rs c a - rs c b) ∧
    (∀ a b c : I, emergence a b c - emergence_reversed a b c = 
                  (rs (a ◦ b) c - rs a c - rs b c) - (rs c (a ◦ b) - rs c a - rs c b)) ∧
    (∀ a b : I, emergence_reversed ε a b = 0) ∧
    (∀ a b : I, emergence_reversed a ε b = 0) ∧
    (∀ a b : I, emergence_reversed a b ε = 0) ∧
    (∀ a c : I, asymmetry (op a a) c = 2 * asymmetry a c + emergence a a c - emergence_reversed a a c) := by
  constructor
  · exact asymmetry_propagation_derivation
  constructor
  · intro a b c; rfl
  constructor
  · exact asymmetry_correction_term
  constructor
  · exact emergence_reversed_void_left
  constructor
  · exact emergence_reversed_void_right
  constructor
  · exact emergence_reversed_probe_void
  · exact asymmetry_propagation_simplifies_self

/-! ## Main Theorem 4.3: Meaning Curvature and Non-Commutativity -/

/-- **Theorem 4.3 (Meaning Curvature and Non-Commutativity)**:
    The meaning curvature μ(a,b,c) = rs(a◦b, c) - rs(b◦a, c) measures the 
    sensitivity of resonance to the order of composition. It satisfies:
    
    1. μ(a,b,c) vanishes iff a◦b and b◦a resonate identically with c
    2. μ(a,b,c) = emergence(a,b,c) - emergence(b,a,c)
    3. μ(a,b,c) = -μ(b,a,c) (antisymmetry in first two arguments)
    4. If a◦b = b◦a (local commutativity), then μ(a,b,c) = 0
    5. If μ(a,b,c) ≠ 0, then a◦b ≠ b◦a (curvature witnesses non-commutativity)
    
    The curvature vanishes exactly when composition is locally commutative, 
    connecting the algebraic property of commutativity to the geometric/topological
    property of curvature. Non-zero curvature is the signature of non-commutative
    ideatic space, where the order of synthesis matters.
    
    This establishes meaning curvature as a fundamental invariant measuring the 
    temporal sensitivity of ideational composition. -/
theorem meaning_curvature_and_noncommutativity :
    (∀ a b c : I, meaning_curvature a b c = rs (a ◦ b) c - rs (b ◦ a) c) ∧
    (∀ a b c : I, meaning_curvature a b c = emergence a b c - emergence b a c) ∧
    (∀ a b c : I, meaning_curvature a b c = -(meaning_curvature b a c)) ∧
    (∀ a b c : I, meaning_curvature a b c = 0 ↔ rs (a ◦ b) c = rs (b ◦ a) c) ∧
    (∀ a b c : I, (a ◦ b) = (b ◦ a) → meaning_curvature a b c = 0) ∧
    (∀ a b c : I, meaning_curvature a b c ≠ 0 → (a ◦ b) ≠ (b ◦ a)) ∧
    (∀ a c : I, meaning_curvature a a c = 0) ∧
    (∀ a b c : I, emergence a b c = emergence b a c ↔ meaning_curvature a b c = 0) ∧
    (∀ b c : I, meaning_curvature ε b c = 0) ∧
    (∀ a c : I, meaning_curvature a ε c = 0) ∧
    (∀ a b : I, meaning_curvature a b ε = 0) := by
  constructor
  · intro a b c; rfl
  constructor
  · exact meaning_curvature_via_emergence
  constructor
  · exact meaning_curvature_antisym_first
  constructor
  · exact zero_curvature_iff_equal_resonance
  constructor
  · exact curvature_vanishes_when_commutes
  constructor
  · exact curvature_implies_noncommutative
  constructor
  · exact meaning_curvature_zero_self
  constructor
  · intro a b c
    constructor
    · exact emergence_symmetric_implies_zero_curvature a b c
    · exact zero_curvature_implies_emergence_symmetric a b c
  constructor
  · exact meaning_curvature_void_left
  constructor
  · exact meaning_curvature_void_right
  · exact meaning_curvature_probe_void

end IdeaTheory


I've verified that the file `lean/IdeaTheory/Theorems4.lean` is already complete and correct on disk. Let me confirm the final state:

● Final verification of file completeness (shell)
  │ echo "=== Final Verification ===" && \
  │ echo "File exists:" && \
  │ ls -lh
  │ /Users/halleyyoung/Documents/formalize/lean/IdeaTheory/Theorems4.lean && \
  │ echo "" && \…
  └ 17 lines...

● Read shell output Waiting up to 10 seconds for command output
  └ 1 line...

● Stop shell
  └ 1 line...

● Quick check for prohibited keywords (shell)
  │ grep -E '\bsorry\b|\badmit\b|\bnative_decide\b'
  │ /Users/halleyyoung/Documents/formalize/lean/IdeaTheory/Theorems4.lean ||
  │ echo "No prohibited keywords"
  └ 2 lines...

● Count main theorems (shell)
  │ grep "^theorem"
  │ /Users/halleyyoung/Documents/formalize/lean/IdeaTheory/Theorems4.lean | wc
  │ -l
  └ 2 lines...