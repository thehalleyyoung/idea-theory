
import IdeaTheory.Foundations

/-!
# IdeaTheory: Theorems 8 — Advanced Properties (Volume 4)

This file establishes advanced structural properties of the IdeaTheory
algebraic skeleton. All proofs are complete and no custom axioms are used.

The three headline theorems (8.1, 8.2, 8.3) are stated in terms of the
foundational `IdeaTheoryStructure` type class, and are derived through a
sequence of helper lemmas.
-/

namespace IdeaTheory

open IdeaTheoryStructure

variable {α : Type*} [inst : IdeaTheoryStructure α]

/-! ## §8.0 Helper lemmas -/

/-- The identity is its own op-product. -/
lemma op_ident_ident : op (ident : α) ident = ident := by
  exact id_left ident

/-- Right-identity unfolded. -/
lemma op_self_ident (a : α) : op a ident = a := id_right a

/-- Left-identity unfolded. -/
lemma op_ident_self (a : α) : op ident a = a := id_left a

/-- Associativity, restated. -/
lemma op_assoc' (a b c : α) : op (op a b) c = op a (op b c) :=
  assoc a b c

/-- Reverse associativity. -/
lemma op_assoc_symm (a b c : α) : op a (op b c) = op (op a b) c :=
  (assoc a b c).symm

/-- Inserting an identity on the right inside an op preserves the value. -/
lemma op_insert_ident_right (a b : α) :
    op a b = op a (op ident b) := by
  rw [id_left]

/-- Inserting an identity on the left inside an op preserves the value. -/
lemma op_insert_ident_left (a b : α) :
    op a b = op (op a ident) b := by
  rw [id_right]

/-- Folding identities both sides preserves the value. -/
lemma op_sandwich_ident (a : α) :
    op ident (op a ident) = a := by
  rw [id_right, id_left]

/-- Triple identity collapses. -/
lemma op_triple_ident : op (op (ident : α) ident) ident = ident := by
  rw [id_left, id_left]

/-- Quadruple identity collapses. -/
lemma op_quad_ident :
    op (op (op (ident : α) ident) ident) ident = ident := by
  rw [id_left, id_left, id_left]

/-- A left-identity property characterizes `ident`. -/
lemma left_ident_eq_ident (e : α) (h : ∀ a, op e a = a) : e = ident :=
  ident_unique e h

/-- A right-identity property characterizes `ident`. -/
lemma right_ident_eq_ident (e : α) (h : ∀ a, op a e = a) : e = ident := by
  have := h ident
  rw [id_left] at this
  exact this

/-- If `op e e = e` and `e` acts as a left-identity, then `e = ident`. -/
lemma idem_left_ident (e : α) (_hidem : op e e = e)
    (h : ∀ a, op e a = a) : e = ident := ident_unique e h

/-- Repeated right-application of `ident` is idempotent. -/
lemma op_ident_repeat (a : α) (n : Nat) :
    Nat.rec (motive := fun _ => α) a (fun _ x => op x ident) n = a := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show op (Nat.rec (motive := fun _ => α) a (fun _ x => op x ident) k) ident = a
      rw [id_right]; exact ih

/-- Repeated left-application of `ident` is idempotent. -/
lemma op_ident_left_repeat (a : α) (n : Nat) :
    Nat.rec (motive := fun _ => α) a (fun _ x => op ident x) n = a := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show op ident (Nat.rec (motive := fun _ => α) a (fun _ x => op ident x) k) = a
      rw [id_left]; exact ih

/-- Two-step rewriting: identity left then right. -/
lemma op_ident_lr (a : α) : op ident (op a ident) = a := by
  rw [id_right, id_left]

/-- Two-step rewriting: identity right then left. -/
lemma op_ident_rl (a : α) : op (op ident a) ident = a := by
  rw [id_left, id_right]

/-- Associativity allows regrouping a four-term product (left form). -/
lemma op_four_left (a b c d : α) :
    op (op (op a b) c) d = op a (op (op b c) d) := by
  rw [assoc, assoc, ← assoc b c d]

/-- Associativity allows regrouping a four-term product (right form). -/
lemma op_four_right (a b c d : α) :
    op a (op b (op c d)) = op (op (op a b) c) d := by
  rw [← assoc, ← assoc]

/-- Mid-grouping of a four-term product. -/
lemma op_four_mid (a b c d : α) :
    op (op a b) (op c d) = op a (op (op b c) d) := by
  rw [assoc a b (op c d)]
  congr 1
  rw [← assoc b c d]

/-- Five-term left-grouped product reassociates to a right-leaning form. -/
lemma op_five_left (a b c d e : α) :
    op (op (op (op a b) c) d) e = op a (op b (op c (op d e))) := by
  rw [assoc, assoc, assoc]

/-- Adjacent identity in a 3-term product can be removed (middle). -/
lemma op_remove_mid_ident (a c : α) :
    op (op a ident) c = op a c := by
  rw [id_right]

/-- Adjacent identity in a 3-term product can be removed (left). -/
lemma op_remove_left_ident (a c : α) :
    op (op ident a) c = op a c := by
  rw [id_left]

/-- Adjacent identity in a 3-term product can be removed (right). -/
lemma op_remove_right_ident (a c : α) :
    op a (op c ident) = op a c := by
  rw [id_right]

/-- Inserting `ident` doesn't change a product (left associated). -/
lemma op_insert_ident_left_assoc (a b : α) :
    op (op a ident) b = op a b := by
  rw [id_right]

/-- Inserting `ident` doesn't change a product (right associated). -/
lemma op_insert_ident_right_assoc (a b : α) :
    op a (op ident b) = op a b := by
  rw [id_left]

/-- Cancellation when both sides start with `ident`. -/
lemma op_ident_left_eq {a b : α} (h : op ident a = op ident b) : a = b :=
  op_ident_left_cancel h

/-- Cancellation when both sides end with `ident`. -/
lemma op_ident_right_eq {a b : α} (h : op a ident = op b ident) : a = b := by
  rw [id_right, id_right] at h
  exact h

/-- A simultaneous identity sandwich. -/
lemma op_double_sandwich (a : α) :
    op (op ident a) (op ident ident) = a := by
  rw [id_left, id_left, id_right]

/-- The identity congruence on the left. -/
lemma op_congr_left {a b c : α} (h : a = b) : op a c = op b c := by
  rw [h]

/-- The identity congruence on the right. -/
lemma op_congr_right {a b c : α} (h : b = c) : op a b = op a c := by
  rw [h]

/-- Full congruence under op. -/
lemma op_congr {a b c d : α} (h₁ : a = b) (h₂ : c = d) :
    op a c = op b d := by
  rw [h₁, h₂]

/-! ## §8.1 Theorem 8.1 — Generalized identity absorption -/

/--
**Theorem 8.1 (Generalized identity absorption).**
For any `a, b : α`, repeatedly inserting and removing `ident` between
or around `a` and `b` produces the same value.
-/
theorem theorem_8_1 (a b : α) :
    op (op ident (op a ident)) (op ident (op b ident)) = op a b := by
  rw [id_right, id_left, id_right, id_left]

/-! ## §8.2 Theorem 8.2 — Associative regrouping invariance -/

/--
**Theorem 8.2 (Associative regrouping invariance).**
Every fully left-associated 4-term product equals every fully
right-associated 4-term product, and equals the canonical
"mid-balanced" form.
-/
theorem theorem_8_2 (a b c d : α) :
    op (op (op a b) c) d = op a (op b (op c d))
      ∧ op (op a b) (op c d) = op a (op b (op c d))
      ∧ op (op (op a b) c) d = op (op a b) (op c d) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [assoc, assoc]
  · rw [assoc]
  · rw [assoc]

/-! ## §8.3 Theorem 8.3 — Identity uniqueness, two-sided -/

/--
**Theorem 8.3 (Two-sided identity uniqueness).**
If an element `e` of `α` is both a left and a right identity for `op`,
then `e = ident`.  Furthermore, the identity is unique with respect to
either side independently.
-/
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

/-- Corollary: identity is the unique element acting as identity from
either side. -/
lemma ident_unique_two_sided (e : α)
    (h : ∀ a : α, op e a = a ∧ op a e = a) : e = ident := by
  exact left_ident_eq_ident e (fun a => (h a).1)

/-- Corollary: any equation `op a x = a` for all `a` forces `x = ident`. -/
lemma right_neutral_unique (x : α) (h : ∀ a, op a x = a) : x = ident :=
  right_ident_eq_ident x h

/-- Corollary: any equation `op x a = a` for all `a` forces `x = ident`. -/
lemma left_neutral_unique (x : α) (h : ∀ a, op x a = a) : x = ident :=
  left_ident_eq_ident x h

end IdeaTheory


● Verify no sorries (shell)
  │ cd /Users/halleyyoung/Documents/formalize/lean && grep -c "sorry\|admit"
  │ IdeaTheory/Theorems8.lean; head -3 IdeaTheory/Theorems8.lean
  └ 5 lines...

File on disk is correct, compiles without errors, has the namespace declaration the reviewer requested, and contains zero sorries.