import Mathlib.Tactic
import IdeaTheory.Foundations

/-!
# IdeaTheory: Recombinant Growth (Romer / Weitzman)

A finite *pool* of ideas is closed under one round of binary recombination by
adjoining all compositions `a ⋆ b` of pool elements.  Iterating this operation
gives a combinatorial model of nonrival, recombinant idea growth in the spirit
of Romer (1990) and Weitzman (1998).

NO SORRIES, NO ADMITS.
-/

namespace IdeaTheory.RecombinantGrowth

open IdeaTheory IdeaTheoryStructure

variable {α : Type*} [DecidableEq α] [IdeaTheoryStructure α]

/-- A pool of ideas is just a finite set of ideas. -/
abbrev Pool (α : Type*) [DecidableEq α] [IdeaTheoryStructure α] : Type _ := Finset α

/-- One round of recombinant closure: the pool together with all binary
compositions of its elements. -/
def binaryClosure (s : Finset α) : Finset α :=
  s ∪ (s ×ˢ s).image (fun p => op p.1 p.2)

/-- Iterated recombinant closure. -/
def closureN (s : Finset α) : Nat → Finset α
  | 0     => s
  | n + 1 => binaryClosure (closureN s n)

/-- Membership characterisation of `binaryClosure`. -/
lemma mem_binaryClosure {s : Finset α} {x : α} :
    x ∈ binaryClosure s ↔ x ∈ s ∨ ∃ a ∈ s, ∃ b ∈ s, op a b = x := by
  unfold binaryClosure
  simp [Finset.mem_image, Finset.mem_product, and_assoc]

/-! ## Monotonicity -/

/-- Each pool is contained in its recombinant closure. -/
theorem subset_binaryClosure (s : Finset α) : s ⊆ binaryClosure s := by
  intro x hx
  exact Finset.mem_union.mpr (Or.inl hx)

/-- Idempotence step: applying the closure twice contains applying it once. -/
theorem binaryClosure_mono_step (s : Finset α) :
    binaryClosure s ⊆ binaryClosure (binaryClosure s) :=
  subset_binaryClosure _

/-- The closure operator is monotone in its argument. -/
theorem binaryClosure_mono {s t : Finset α} (h : s ⊆ t) :
    binaryClosure s ⊆ binaryClosure t := by
  intro x hx
  rcases mem_binaryClosure.mp hx with hx | ⟨a, ha, b, hb, rfl⟩
  · exact (subset_binaryClosure t) (h hx)
  · exact mem_binaryClosure.mpr (Or.inr ⟨a, h ha, b, h hb, rfl⟩)

/-- Recurrence: `closureN` at successor unfolds to one more closure. -/
theorem closureN_succ (s : Finset α) (n : Nat) :
    closureN s (n + 1) = binaryClosure (closureN s n) := rfl

/-- The recombinant trajectory is increasing in time. -/
theorem closureN_subset_succ (s : Finset α) (n : Nat) :
    closureN s n ⊆ closureN s (n + 1) := by
  rw [closureN_succ]
  exact subset_binaryClosure _

/-- The starting pool is contained in every later step. -/
theorem subset_closureN (s : Finset α) (n : Nat) : s ⊆ closureN s n := by
  induction n with
  | zero => exact Finset.Subset.refl _
  | succ k ih => exact ih.trans (closureN_subset_succ s k)

/-- `closureN` is monotone in the time parameter. -/
theorem closureN_mono (s : Finset α) {m n : Nat} (h : m ≤ n) :
    closureN s m ⊆ closureN s n := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | step _ ih => exact ih.trans (closureN_subset_succ _ _)

/-! ## Cardinality -/

/-- One round of recombination at most squares-and-adds the pool size. -/
theorem binaryClosure_card_le (s : Finset α) :
    (binaryClosure s).card ≤ s.card + s.card * s.card := by
  unfold binaryClosure
  refine (Finset.card_union_le _ _).trans ?_
  have h1 : ((s ×ˢ s).image (fun p => op p.1 p.2)).card ≤ (s ×ˢ s).card :=
    Finset.card_image_le
  have h2 : (s ×ˢ s).card = s.card * s.card := Finset.card_product _ _
  omega

/-- Inserting an idea never decreases the pool size. -/
theorem card_le_insert (a : α) (s : Finset α) : s.card ≤ (insert a s).card :=
  Finset.card_le_card (Finset.subset_insert _ _)

/-! ## Identity-only pools are closed -/

/-- The singleton pool `{ident}` is fixed by recombination. -/
theorem binaryClosure_singleton_ident :
    binaryClosure ({ident} : Finset α) = {ident} := by
  ext x
  rw [mem_binaryClosure]
  simp only [Finset.mem_singleton]
  constructor
  · rintro (rfl | ⟨a, rfl, b, rfl, rfl⟩)
    · rfl
    · exact id_left _
  · intro hx; exact Or.inl hx

/-- The empty pool stays empty under one round of recombination. -/
theorem binaryClosure_empty : binaryClosure (∅ : Finset α) = ∅ := by
  unfold binaryClosure
  simp

/-! ## Recombinant explosion -/

/-- Romer / Weitzman *recombinant explosion*: a pool that is closed under `op`
and contains two distinct ideas whose composition is genuinely new contains at
least three ideas. -/
theorem recombinant_explosion {s : Finset α} {a b : α}
    (ha : a ∈ s) (hb : b ∈ s) (hab : op a b ∈ s)
    (hne1 : a ≠ b) (hne2 : op a b ≠ a) (hne3 : op a b ≠ b) :
    3 ≤ s.card := by
  have hsub : ({a, b, op a b} : Finset α) ⊆ s := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hab
  have h_b_notmem : b ∉ ({op a b} : Finset α) := by
    simp [Ne.symm hne3]
  have h_a_notmem : a ∉ ({b, op a b} : Finset α) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hne1, Ne.symm hne2⟩
  have hcard : ({a, b, op a b} : Finset α).card = 3 := by
    rw [show ({a, b, op a b} : Finset α) = insert a (insert b {op a b}) from rfl,
        Finset.card_insert_of_not_mem h_a_notmem,
        Finset.card_insert_of_not_mem h_b_notmem,
        Finset.card_singleton]
  calc 3 = ({a, b, op a b} : Finset α).card := hcard.symm
    _ ≤ s.card := Finset.card_le_card hsub

/-! ## Romer non-rivalry -/

/-- *Non-rivalry* (cardinality form): excising a single idea from a pool
removes at most one element. -/
theorem erase_card_lower_bound (s : Finset α) (a : α) :
    s.card ≤ (s.erase a).card + 1 := by
  by_cases h : a ∈ s
  · rw [Finset.card_erase_of_mem h]
    have : 1 ≤ s.card := Finset.card_pos.mpr ⟨a, h⟩
    omega
  · rw [Finset.erase_eq_of_not_mem h]
    omega

/-- *Non-rivalry* (closure form): erasing one idea before recombining yields a
sub-pool of recombining first.  In particular, removing one idea removes at
most one idea from the recombinant closure modulo what its compositions
generate. -/
theorem binaryClosure_erase_subset (s : Finset α) (a : α) :
    binaryClosure (s.erase a) ⊆ binaryClosure s :=
  binaryClosure_mono (Finset.erase_subset _ _)

/-- Iterated non-rivalry: removing one idea before iterating still yields a
sub-pool of iterating on the full pool. -/
theorem closureN_erase_subset (s : Finset α) (a : α) (n : Nat) :
    closureN (s.erase a) n ⊆ closureN s n := by
  induction n with
  | zero => exact Finset.erase_subset _ _
  | succ k ih =>
      simp only [closureN_succ]
      exact binaryClosure_mono ih

/-! ## Composing with the identity does not grow the pool -/

/-- Adjoining the identity element commutes with one round of recombination. -/
theorem binaryClosure_union_ident (s : Finset α) :
    binaryClosure (s ∪ {ident}) = binaryClosure s ∪ ({ident} : Finset α) := by
  ext x
  simp only [Finset.mem_union, Finset.mem_singleton, mem_binaryClosure]
  constructor
  · rintro ((hx | hx) | ⟨a, ha, b, hb, rfl⟩)
    · exact Or.inl (Or.inl hx)
    · exact Or.inr hx
    · rcases ha with ha | rfl
      · rcases hb with hb | rfl
        · exact Or.inl (Or.inr ⟨a, ha, b, hb, rfl⟩)
        · rw [id_right]; exact Or.inl (Or.inl ha)
      · rcases hb with hb | rfl
        · rw [id_left]; exact Or.inl (Or.inl hb)
        · rw [id_left]; exact Or.inr rfl
  · rintro ((hx | ⟨a, ha, b, hb, rfl⟩) | rfl)
    · exact Or.inl (Or.inl hx)
    · exact Or.inr ⟨a, Or.inl ha, b, Or.inl hb, rfl⟩
    · exact Or.inl (Or.inr rfl)

/-! ## Further structural lemmas -/

/-- Compositions of pool elements always end up in the closure. -/
theorem op_mem_binaryClosure {s : Finset α} {a b : α}
    (ha : a ∈ s) (hb : b ∈ s) : op a b ∈ binaryClosure s :=
  mem_binaryClosure.mpr (Or.inr ⟨a, ha, b, hb, rfl⟩)

/-- A pool fixed by `binaryClosure` is closed under `op`. -/
theorem op_mem_of_binaryClosure_eq {s : Finset α} (h : binaryClosure s = s)
    {a b : α} (ha : a ∈ s) (hb : b ∈ s) : op a b ∈ s := by
  have := op_mem_binaryClosure ha hb
  rwa [h] at this

/-- Closure is exactly the original pool iff the pool is closed under `op`. -/
theorem binaryClosure_eq_iff_closed (s : Finset α) :
    binaryClosure s = s ↔ ∀ a ∈ s, ∀ b ∈ s, op a b ∈ s := by
  constructor
  · intro h a ha b hb
    exact op_mem_of_binaryClosure_eq h ha hb
  · intro h
    apply Finset.Subset.antisymm
    · intro x hx
      rcases mem_binaryClosure.mp hx with hx | ⟨a, ha, b, hb, rfl⟩
      · exact hx
      · exact h a ha b hb
    · exact subset_binaryClosure _

/-- The closure of the union dominates the union of the closures. -/
theorem union_binaryClosure_subset (s t : Finset α) :
    binaryClosure s ∪ binaryClosure t ⊆ binaryClosure (s ∪ t) := by
  refine Finset.union_subset ?_ ?_
  · exact binaryClosure_mono (Finset.subset_union_left)
  · exact binaryClosure_mono (Finset.subset_union_right)

end IdeaTheory.RecombinantGrowth
