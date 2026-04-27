
import IdeaTheory.Foundations

/-!
# IdeaTheory: Theorems 8 — Advanced Properties (Volume 4)

This file establishes advanced structural properties of the IdeaTheory
algebraic skeleton. All proofs are complete; no `sorry`, `admit`, or
custom axioms are used.

The three headline theorems (8.1, 8.2, 8.3) are stated in terms of the
foundational `IdeaTheoryStructure` type class, and are derived through a
sequence of helper lemmas.
-/

namespace IdeaTheory

open IdeaTheoryStructure

variable {α : Type*} [inst : IdeaTheoryStructure α]

/-! ## §8.0 Helper lemmas -/

lemma op_ident_ident : op (ident : α) ident = ident := id_left ident

lemma op_self_ident (a : α) : op a ident = a := id_right a

lemma op_ident_self (a : α) : op ident a = a := id_left a

lemma op_assoc' (a b c : α) : op (op a b) c = op a (op b c) := assoc a b c

lemma op_assoc_symm (a b c : α) : op a (op b c) = op (op a b) c :=
  (assoc a b c).symm

lemma op_insert_ident_right (a b : α) :
    op a b = op a (op ident b) := by rw [id_left]

lemma op_insert_ident_left (a b : α) :
    op a b = op (op a ident) b := by rw [id_right]

lemma op_sandwich_ident (a : α) :
    op ident (op a ident) = a := by rw [id_right, id_left]

lemma op_triple_ident : op (op (ident : α) ident) ident = ident := by
  rw [id_left, id_left]

lemma op_quad_ident :
    op (op (op (ident : α) ident) ident) ident = ident := by
  rw [id_left, id_left, id_left]

lemma left_ident_eq_ident (e : α) (h : ∀ a, op e a = a) : e = ident :=
  ident_unique e h

lemma right_ident_eq_ident (e : α) (h : ∀ a, op a e = a) : e = ident := by
  have := h ident
  rw [id_left] at this
  exact this

lemma idem_left_ident (e : α) (_hidem : op e e = e)
    (h : ∀ a, op e a = a) : e = ident := ident_unique e h

lemma op_ident_repeat (a : α) (n : Nat) :
    Nat.rec (motive := fun _ => α) a (fun _ x => op x ident) n = a := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show op (Nat.rec (motive := fun _ => α) a (fun _ x => op x ident) k) ident = a
      rw [id_right]; exact ih

lemma op_ident_left_repeat (a : α) (n : Nat) :
    Nat.rec (motive := fun _ => α) a (fun _ x => op ident x) n = a := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show op ident (Nat.rec (motive := fun _ => α) a (fun _ x => op ident x) k) = a
      rw [id_left]; exact ih

lemma op_ident_lr (a : α) : op ident (op a ident) = a := by
  rw [id_right, id_left]

lemma op_ident_rl (a : α) : op (op ident a) ident = a := by
  rw [id_left, id_right]

lemma op_four_left (a b c d : α) :
    op (op (op a b) c) d = op a (op (op b c) d) := by
  rw [assoc, assoc, ← assoc b c d]

lemma op_four_right (a b c d : α) :
    op a (op b (op c d)) = op (op (op a b) c) d := by
  rw [← assoc, ← assoc]

lemma op_four_mid (a b c d : α) :
    op (op a b) (op c d) = op a (op (op b c) d) := by
  rw [assoc a b (op c d)]
  congr 1
  rw [← assoc b c d]

lemma op_five_left (a b c d e : α) :
    op (op (op (op a b) c) d) e = op a (op b (op c (op d e))) := by
  rw [assoc, assoc, assoc]

lemma op_remove_mid_ident (a c : α) :
    op (op a ident) c = op a c := by rw [id_right]

lemma op_remove_left_ident (a c : α) :
    op (op ident a) c = op a c := by rw [id_left]

lemma op_remove_right_ident (a c : α) :
    op a (op c ident) = op a c := by rw [id_right]

lemma op_insert_ident_left_assoc (a b : α) :
    op (op a ident) b = op a b := by rw [id_right]

lemma op_insert_ident_right_assoc (a b : α) :
    op a (op ident b) = op a b := by rw [id_left]

lemma op_ident_left_eq {a b : α} (h : op ident a = op ident b) : a = b :=
  op_ident_left_cancel h

lemma op_ident_right_eq {a b : α} (h : op a ident = op b ident) : a = b := by
  rw [id_right, id_right] at h
  exact h

lemma op_double_sandwich (a : α) :
    op (op ident a) (op ident ident) = a := by
  rw [id_left, id_left, id_right]

lemma op_congr_left {a b c : α} (h : a = b) : op a c = op b c := by rw [h]

lemma op_congr_right {a b c : α} (h : b = c) : op a b = op a c := by rw [h]

lemma op_congr {a b c d : α} (h₁ : a = b) (h₂ : c = d) :
    op a c = op b d := by rw [h₁, h₂]

/-! ## §8.1 Theorem 8.1 — Generalized identity absorption -/

theorem theorem_8_1 (a b : α) :
    op (op ident (op a ident)) (op ident (op b ident)) = op a b := by
  rw [id_right, id_left, id_right, id_left]

/-! ## §8.2 Theorem 8.2 — Associative regrouping invariance -/

theorem theorem_8_2 (a b c d : α) :
    op (op (op a b) c) d = op a (op b (op c d))
      ∧ op (op a b) (op c d) = op a (op b (op c d))
      ∧ op (op (op a b) c) d = op (op a b) (op c d) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [assoc, assoc]
  · rw [assoc]
  · rw [assoc]

/-! ## §8.3 Theorem 8.3 — Identity uniqueness, two-sided -/

theorem theorem_8_3 (e : α)
    (hL : ∀ a, op e a = a) (_hR : ∀ a, op a e = a) :
    e = ident
      ∧ (∀ e' : α, (∀ a : α, op e' a = a) → e' = ident)
      ∧ (∀ e' : α, (∀ a : α, op a e' = a) → e' = ident) := by
  refine ⟨?_, ?_, ?_⟩
  · exact left_ident_eq_ident e hL
  · intro e' h; exact left_ident_eq_ident e' h
  · intro e' h; exact right_ident_eq_ident e' h

/-! ## §8.4 Further corollaries -/

lemma ident_unique_two_sided (e : α)
    (h : ∀ a : α, op e a = a ∧ op a e = a) : e = ident :=
  left_ident_eq_ident e (fun a => (h a).1)

lemma right_neutral_unique (x : α) (h : ∀ a, op a x = a) : x = ident :=
  right_ident_eq_ident x h

lemma left_neutral_unique (x : α) (h : ∀ a, op x a = a) : x = ident :=
  left_ident_eq_ident x h

end IdeaTheory