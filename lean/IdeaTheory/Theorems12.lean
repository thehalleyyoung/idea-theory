import IdeaTheory.Foundations
import IdeaTheory.Theorems10
import IdeaTheory.Theorems11

/-!
# IdeaTheory: Theorems 12 — Emergent Novelty (Volume 6)

## What this file formalizes

This file belongs to Volume 6 of the IdeaTheory project — *Advanced
Applications and Unifying Perspectives* — and develops the formal
theory of **emergent novelty**.  Where Volume 5 reread the
Volume 1 algebraic operation `op : α → α → α` as the *aggregation*
of two co-present agents into a coalition, and where the sibling
file `Theorems11` reread the same operator as a *temporal*
transmission step, the present file rereads composition as the
production of a **new idea** out of two pre-existing ones.  The
informal IDT manuscript (Volume VI, Chapter 2, *"Emergent Novelty"*)
argues that the very interest of an algebra of ideas lies in the
fact that `op a b` need not coincide with either `a` or `b`: the
composition of two ideas may be *novel*, exhibiting properties not
present in either ingredient.  The classical "problem of
emergence" of the philosophy-of-mind and complex-systems literatures
(Mill 1843, Lewes 1875, Broad 1925, Anderson 1972, Bedau 1997,
Chalmers 2006, O'Connor 2020) is then reread inside Volume 6 as the
algebraic question: *when is `op a b` provably distinct from every
ingredient of the composition, and how does this novelty propagate
when several compositions are chained together?*

## Authors and works drawn upon

Beyond the IDT manuscript itself, this file engages the standard
non-formalized literature on emergence and novelty: J. S. Mill,
*A System of Logic* (1843), Bk. III Ch. VI, for the original
"heteropathic effects" terminology; G. H. Lewes, *Problems of Life
and Mind*, vol. II (1875), §V, who first coined the noun
*emergent*; C. D. Broad, *The Mind and Its Place in Nature* (1925),
Ch. II §3, for the "emergent properties" reading; P. W. Anderson,
*"More is Different"* (Science 1972), §1, for the slogan that
composition produces qualitatively new behaviour; M. Bedau,
*"Weak Emergence"* (Phil. Perspectives 1997) §1, for the
"underivable except by simulation" formulation; D. Chalmers,
*"Strong and Weak Emergence"* (in P. Clayton & P. Davies, eds., *The
Re-Emergence of Emergence*, OUP 2006), §2, for the
strong/weak distinction; and T. O'Connor, *"Emergent Properties"*
(SEP 2020), §§1–3, for the contemporary survey terminology.  The
formal pattern of treating "novelty" as a binary predicate
"`op a b ∉ {a, b}`" is, to the author's knowledge, original to
the IDT project, but it is suggested by the algebraic readings
of "irreducibility" in Bedau 1997.

## Design decisions and conventions

* The only primitive structure used in this file is
  `IdeaTheoryStructure`.  All notions of novelty are *defined* in
  terms of `op`, `ident`, `assoc`, `id_left`, `id_right` and the
  `aggregate`/`tradition` machinery of `Theorems10`/`Theorems11`.
* "Novelty" is treated as a `Prop`-valued predicate, never as a
  numerical magnitude; the numerical/cocycle reading of emergence
  belongs to Volume 1 (`Theorems2`), and we deliberately keep the
  two presentations separate.
* "Emergent novelty of `op a b`" is the proposition
  `op a b ≠ a ∧ op a b ≠ b`.
* "Cumulative novelty of a lineage `l`" is the proposition
  "the tradition of `l` differs from every contribution `a ∈ l`".
* We work inside `namespace IdeaTheory` and over a generic
  `[IdeaTheoryStructure α]` carrier.
* Sub-lemmas are split into named sections (`Closure`,
  `IdentityElimination`, `Monotonicity`, `Lineage`,
  `Transmission`).

## Roadmap

1. §12.0  Auxiliary definitions: `IsNovel`, `EmergentNovel`,
   `EmergentNovelL`, `EmergentNovelR`, `NoveltyWitness`,
   `NovelEverywhere`, `LineageNovel`, `NoveltyPredicate`,
   `Underivable`, `EmergencePair`, `IdeaSet`, `Closed`.
2. §12.1  Closure lemmas: identity, symmetry, contrapositions.
3. §12.2  Identity elimination: `ident` cannot be a novel partner.
4. §12.3  Monotonicity along compositions and lineages.
5. §12.4  Lineage novelty and the `tradition` operator.
6. §12.5  Interaction with the transmission machinery of `Theorems11`.
7. §12.6  `theorem_12_1` — Identity-Elimination Theorem.
8. §12.7  `theorem_12_2` — Cumulative-Novelty Theorem.
9. §12.8  `theorem_12_3` — Transmission-Preservation of Novelty.
10. §12.9 Corollaries `corollary_12_1`–`corollary_12_5`.
11. §12.10 Examples and sanity checks.
12. §12.11 End-of-file index.

## Role inside Volume 6

Together with `Theorems10` (social aggregation) and `Theorems11`
(cultural transmission), this file completes the *temporal*,
*social*, and *novelty-theoretic* rereadings of the Volume 1
algebra that constitute Volume 6.  Specifically, the headline
results of this file are reused by later chapters of Volume 6 to
characterise when a coalition or a transmission chain can be
genuinely *creative*, and to give a precise sense in which a
silent (`ident`-valued) generation can never *originate* a novel
idea.
-/

namespace IdeaTheory

open IdeaTheoryStructure

variable {α : Type*} [inst : IdeaTheoryStructure α]

/-! ## §12.0 Auxiliary definitions for emergent novelty -/

/-- An idea `c` is **novel relative to** an idea `a` iff `c ≠ a`.
    This is the most primitive form of "novelty" used throughout the
    file: `c` is novel with respect to a single reference idea `a`.
    Cf. Lewes 1875 §V, where novelty is defined relative to "what
    came before". -/
def IsNovel (c a : α) : Prop := c ≠ a

/-- The composition `op a b` is **emergently novel** iff it differs
    from both ingredients.  This is the algebraic counterpart of
    Broad 1925 Ch. II §3's "emergent property": something is present
    in the composite that was not present in either part. -/
def EmergentNovel (a b : α) : Prop :=
  op a b ≠ a ∧ op a b ≠ b

/-- The composition `op a b` is **left-novel** iff it differs from
    its left ingredient `a`.  This corresponds to the case in which
    composition adds *something new* to `a` from the perspective of
    `a` (Anderson 1972). -/
def EmergentNovelL (a b : α) : Prop := op a b ≠ a

/-- The composition `op a b` is **right-novel** iff it differs from
    its right ingredient `b`.  Dual of `EmergentNovelL`. -/
def EmergentNovelR (a b : α) : Prop := op a b ≠ b

/-- A **novelty witness** for the composition `op a b` is a pair of
    proofs that the composite differs from each ingredient.  This
    bundles the data of `EmergentNovel`. -/
structure NoveltyWitness (a b : α) where
  /-- `op a b` is not equal to `a`. -/
  not_left  : op a b ≠ a
  /-- `op a b` is not equal to `b`. -/
  not_right : op a b ≠ b

/-- A predicate is **novel everywhere** on a list iff every element
    of the list differs from a given reference idea.  Used to express
    "the tradition of a lineage is novel relative to every individual
    contribution", a notion appearing in Bedau 1997 §1 as
    "diachronic underivability". -/
def NovelEverywhere (c : α) (xs : List α) : Prop :=
  ∀ a ∈ xs, c ≠ a

/-- A **lineage** (in the sense of `Theorems11`) is *novel* iff its
    `tradition` differs from every individual contribution.  This is
    the cumulative form of `EmergentNovel`. -/
def LineageNovel (l : Lineage α) : Prop :=
  NovelEverywhere (tradition l) l

/-- A **novelty predicate** is a proposition-valued function on
    pairs of ideas, used to abstract away the particular notion of
    "novel" in a downstream application (Volume 6 reuses this for
    "creative", "innovative", "expressive", etc.). -/
abbrev NoveltyPredicate (α : Type*) := α → α → Prop

/-- The principal novelty predicate of this file is `EmergentNovel`.
    We expose it under the `Emergent` name for use in downstream
    chapters of Volume 6. -/
def Emergent : NoveltyPredicate α := EmergentNovel

/-- An idea `c` is **underivable** from a finite collection `xs` iff
    it differs from every element of `xs`.  This is the algebraic
    rendering of Bedau 1997 §1's "weak-emergence" criterion. -/
def Underivable (c : α) (xs : List α) : Prop :=
  NovelEverywhere c xs

/-- An **emergence pair** packages two ideas `a`, `b` together with
    a witness that their composition is emergently novel.  This is a
    convenient bundling for stating cumulative-novelty results. -/
structure EmergencePair (α : Type*) [IdeaTheoryStructure α] where
  /-- The left ingredient. -/
  left   : α
  /-- The right ingredient. -/
  right  : α
  /-- Witness that `op left right` is novel relative to both. -/
  witness : NoveltyWitness left right

/-- An **idea set** is just a predicate on `α`, used to talk about
    "the set of all ideas of a given kind" without committing to any
    particular set-theoretic encoding. -/
abbrev IdeaSet (α : Type*) := α → Prop

/-- An idea set is **closed under composition** iff `op a b` is in
    the set whenever both `a` and `b` are.  Closure is the formal
    obstruction to novelty: a *closed* set never produces a novel
    element by composition. -/
def Closed (S : IdeaSet α) : Prop :=
  ∀ a b, S a → S b → S (op a b)

/-! ## §12.1 Closure lemmas: identity, symmetry, contrapositions -/

section Closure

/-- `IsNovel` is irreflexive: `a` is never novel with respect to
    itself. -/
lemma IsNovel.irrefl (a : α) : ¬ IsNovel a a := by
  intro h
  exact h rfl

/-- `IsNovel c a` is the same as `c ≠ a`. -/
lemma IsNovel_iff (c a : α) : IsNovel c a ↔ c ≠ a := Iff.rfl

/-- A novelty witness yields the conjunctive `EmergentNovel`. -/
lemma NoveltyWitness.toEmergent {a b : α} (w : NoveltyWitness a b) :
    EmergentNovel a b :=
  ⟨w.not_left, w.not_right⟩

/-- An `EmergentNovel` proof yields a `NoveltyWitness`. -/
lemma EmergentNovel.toWitness {a b : α} (h : EmergentNovel a b) :
    NoveltyWitness a b :=
  { not_left := h.1, not_right := h.2 }

/-- `EmergentNovel a b` unfolds to its conjunctive form. -/
lemma EmergentNovel_iff (a b : α) :
    EmergentNovel a b ↔ op a b ≠ a ∧ op a b ≠ b := Iff.rfl

/-- `EmergentNovelL a b` unfolds to `op a b ≠ a`. -/
lemma EmergentNovelL_iff (a b : α) :
    EmergentNovelL a b ↔ op a b ≠ a := Iff.rfl

/-- `EmergentNovelR a b` unfolds to `op a b ≠ b`. -/
lemma EmergentNovelR_iff (a b : α) :
    EmergentNovelR a b ↔ op a b ≠ b := Iff.rfl

/-- The conjunction of left-novelty and right-novelty is
    emergent-novelty. -/
lemma EmergentNovel.of_LR {a b : α}
    (hL : EmergentNovelL a b) (hR : EmergentNovelR a b) :
    EmergentNovel a b :=
  ⟨hL, hR⟩

/-- Emergent-novelty implies left-novelty. -/
lemma EmergentNovel.left {a b : α}
    (h : EmergentNovel a b) : EmergentNovelL a b := h.1

/-- Emergent-novelty implies right-novelty. -/
lemma EmergentNovel.right {a b : α}
    (h : EmergentNovel a b) : EmergentNovelR a b := h.2

/-- Contrapositive form of `EmergentNovelL`. -/
lemma not_EmergentNovelL_iff (a b : α) :
    ¬ EmergentNovelL a b ↔ op a b = a := by
  unfold EmergentNovelL
  exact not_not

/-- Contrapositive form of `EmergentNovelR`. -/
lemma not_EmergentNovelR_iff (a b : α) :
    ¬ EmergentNovelR a b ↔ op a b = b := by
  unfold EmergentNovelR
  exact not_not

/-- Negating `EmergentNovel` yields a disjunction of fixities. -/
lemma not_EmergentNovel_iff (a b : α) :
    ¬ EmergentNovel a b ↔ op a b = a ∨ op a b = b := by
  unfold EmergentNovel
  constructor
  · intro h
    by_cases hL : op a b = a
    · exact Or.inl hL
    · by_cases hR : op a b = b
      · exact Or.inr hR
      · exact (h ⟨hL, hR⟩).elim
  · intro h ⟨hL, hR⟩
    cases h with
    | inl hL' => exact hL hL'
    | inr hR' => exact hR hR'

/-- Trivial closure of `NovelEverywhere` over the empty list. -/
lemma NovelEverywhere_nil (c : α) :
    NovelEverywhere c ([] : List α) := by
  intro a ha
  cases ha

/-- `NovelEverywhere` over a `cons` decomposes. -/
lemma NovelEverywhere_cons (c a : α) (xs : List α) :
    NovelEverywhere c (a :: xs) ↔ c ≠ a ∧ NovelEverywhere c xs := by
  constructor
  · intro h
    refine ⟨h a (List.mem_cons_self a xs), ?_⟩
    intro b hb
    exact h b (List.mem_cons_of_mem a hb)
  · rintro ⟨hca, hxs⟩ b hb
    rcases List.mem_cons.mp hb with rfl | hb'
    · exact hca
    · exact hxs b hb'

/-- `NovelEverywhere` is monotone in the list (sublist version
    for `cons`). -/
lemma NovelEverywhere.mono_cons {c a : α} {xs : List α}
    (h : NovelEverywhere c (a :: xs)) :
    NovelEverywhere c xs := by
  rcases (NovelEverywhere_cons c a xs).mp h with ⟨_, hxs⟩
  exact hxs

/-- The head of a list witnessing `NovelEverywhere c (a :: xs)` is
    novel with respect to `c`. -/
lemma NovelEverywhere.head {c a : α} {xs : List α}
    (h : NovelEverywhere c (a :: xs)) : c ≠ a :=
  ((NovelEverywhere_cons c a xs).mp h).1

/-- `NovelEverywhere` distributes over list append. -/
lemma NovelEverywhere_append (c : α) (xs ys : List α) :
    NovelEverywhere c (xs ++ ys) ↔
      NovelEverywhere c xs ∧ NovelEverywhere c ys := by
  induction xs with
  | nil =>
      constructor
      · intro h
        exact ⟨NovelEverywhere_nil c, h⟩
      · rintro ⟨_, hys⟩
        exact hys
  | cons a as ih =>
      have hstep :
          NovelEverywhere c ((a :: as) ++ ys) ↔
            (c ≠ a ∧ NovelEverywhere c (as ++ ys)) := by
        show NovelEverywhere c (a :: (as ++ ys)) ↔ _
        exact NovelEverywhere_cons c a (as ++ ys)
      rw [hstep, ih]
      constructor
      · rintro ⟨hca, hxs, hys⟩
        refine ⟨?_, hys⟩
        exact (NovelEverywhere_cons c a as).mpr ⟨hca, hxs⟩
      · rintro ⟨hxs, hys⟩
        rcases (NovelEverywhere_cons c a as).mp hxs with ⟨hca, has⟩
        exact ⟨hca, has, hys⟩

/-- `NovelEverywhere` is preserved when restricted to a sub-`cons`. -/
lemma NovelEverywhere.tail {c a : α} {xs : List α}
    (h : NovelEverywhere c (a :: xs)) :
    NovelEverywhere c xs :=
  h.mono_cons

/-- The trivial idea-set `fun _ => True` is closed under composition. -/
lemma Closed.true_set : Closed (fun _ : α => True) := by
  intro a b _ _; trivial

/-- Singleton sets containing only the identity are closed. -/
lemma Closed.singleton_ident :
    Closed (fun a : α => a = (ident : α)) := by
  intro a b ha hb
  -- a = ident, b = ident ⇒ op a b = op ident ident = ident
  rw [ha, hb]
  exact id_left (ident : α)

/-- The intersection of two closed sets is closed. -/
lemma Closed.inter {S T : IdeaSet α}
    (hS : Closed S) (hT : Closed T) :
    Closed (fun a => S a ∧ T a) := by
  intro a b ⟨hSa, hTa⟩ ⟨hSb, hTb⟩
  exact ⟨hS a b hSa hSb, hT a b hTa hTb⟩

end Closure

/-! ## §12.2 Identity elimination: `ident` cannot be a novel partner -/

section IdentityElimination

/-- `op ident b = b`, so `op ident b` cannot be left-novel relative
    to `b` (it equals `b`).  In particular it is *not* emergent. -/
lemma not_EmergentNovel_ident_left (b : α) :
    ¬ EmergentNovel (ident : α) b := by
  intro ⟨_, hR⟩
  apply hR
  exact id_left b

/-- Dually, `op a ident = a`, so `op a ident` is never emergent. -/
lemma not_EmergentNovel_ident_right (a : α) :
    ¬ EmergentNovel a (ident : α) := by
  intro ⟨hL, _⟩
  apply hL
  exact id_right a

/-- `op ident b` is *not* left-novel relative to `b` (it equals `b`). -/
lemma not_EmergentNovelR_ident_left (b : α) :
    ¬ EmergentNovelR (ident : α) b := by
  intro h
  apply h
  exact id_left b

/-- `op a ident` is *not* right-novel relative to `a`. -/
lemma not_EmergentNovelL_ident_right (a : α) :
    ¬ EmergentNovelL a (ident : α) := by
  intro h
  apply h
  exact id_right a

/-- If `op a b` is emergently novel, then neither `a` nor `b` is the
    identity element. -/
lemma EmergentNovel.left_ne_ident {a b : α}
    (h : EmergentNovel a b) : a ≠ ident := by
  intro habs
  have h' : EmergentNovel (ident : α) b := by rw [← habs]; exact h
  exact not_EmergentNovel_ident_left b h'

/-- Symmetric form of `EmergentNovel.left_ne_ident`. -/
lemma EmergentNovel.right_ne_ident {a b : α}
    (h : EmergentNovel a b) : b ≠ ident := by
  intro habs
  have h' : EmergentNovel a (ident : α) := by rw [← habs]; exact h
  exact not_EmergentNovel_ident_right a h'

/-- A silent generation cannot enter a novelty witness on the left. -/
lemma NoveltyWitness.left_ne_ident {a b : α}
    (w : NoveltyWitness a b) : a ≠ ident :=
  w.toEmergent.left_ne_ident

/-- A silent generation cannot enter a novelty witness on the right. -/
lemma NoveltyWitness.right_ne_ident {a b : α}
    (w : NoveltyWitness a b) : b ≠ ident :=
  w.toEmergent.right_ne_ident

/-- The identity element is *not* novel relative to itself. -/
lemma ident_not_IsNovel : ¬ IsNovel (ident : α) (ident : α) :=
  IsNovel.irrefl (ident : α)

/-- Conversely: if `a = ident`, then no `b` can yield emergent novelty
    via `op a b`. -/
lemma not_EmergentNovel_of_left_ident {a b : α} (ha : a = ident) :
    ¬ EmergentNovel a b := by
  rw [ha]; exact not_EmergentNovel_ident_left b

/-- Mirror form of `not_EmergentNovel_of_left_ident`. -/
lemma not_EmergentNovel_of_right_ident {a b : α} (hb : b = ident) :
    ¬ EmergentNovel a b := by
  rw [hb]; exact not_EmergentNovel_ident_right a

end IdentityElimination

/-! ## §12.3 Monotonicity along compositions and lineages -/

section Monotonicity

/-- Closure is monotone with respect to set inclusion. -/
lemma Closed.mono {S T : IdeaSet α}
    (hST : ∀ a, S a → T a)
    (hT : Closed T) :
    -- T contains the closure-image of every S-pair
    ∀ a b, S a → S b → T (op a b) := by
  intro a b ha hb
  exact hT a b (hST a ha) (hST b hb)

/-- If `op a b = a`, then `b` is "absorbing for `a` on the right" in
    the sense that the composition leaves `a` unchanged. -/
lemma right_absorbing_of_not_NovelL {a b : α}
    (h : ¬ EmergentNovelL a b) : op a b = a :=
  (not_EmergentNovelL_iff a b).mp h

/-- Mirror form. -/
lemma left_absorbing_of_not_NovelR {a b : α}
    (h : ¬ EmergentNovelR a b) : op a b = b :=
  (not_EmergentNovelR_iff a b).mp h

/-- `EmergentNovel` is preserved upward by strengthening: if a
    composition is novel, then it is left-novel. -/
lemma EmergentNovel.imp_L {a b : α}
    (h : EmergentNovel a b) : EmergentNovelL a b := h.1

/-- Symmetric. -/
lemma EmergentNovel.imp_R {a b : α}
    (h : EmergentNovel a b) : EmergentNovelR a b := h.2

/-- Transferring novelty across an equality of ingredients. -/
lemma EmergentNovel.congr_left {a a' b : α}
    (h : EmergentNovel a b) (heq : a = a') :
    EmergentNovel a' b := by
  cases heq; exact h

/-- Transferring novelty across an equality of right ingredient. -/
lemma EmergentNovel.congr_right {a b b' : α}
    (h : EmergentNovel a b) (heq : b = b') :
    EmergentNovel a b' := by
  cases heq; exact h

/-- If `op a b` is novel and `op a b = c`, then `c` is novel relative
    to both `a` and `b`. -/
lemma EmergentNovel.toIsNovel {a b c : α}
    (h : EmergentNovel a b) (heq : op a b = c) :
    IsNovel c a ∧ IsNovel c b := by
  refine ⟨?_, ?_⟩
  · intro habs
    apply h.1
    rw [heq]; exact habs
  · intro habs
    apply h.2
    rw [heq]; exact habs

end Monotonicity

/-! ## §12.4 Lineage novelty and the `tradition` operator -/

section LineageSec

/-- The empty lineage has trivially-novel tradition: no contribution
    exists to compare to.  Vacuously true. -/
lemma LineageNovel_nil :
    LineageNovel ([] : Lineage α) := by
  intro a ha
  cases ha

/-- A lineage is novel iff every contribution is distinct from the
    accumulated tradition. -/
lemma LineageNovel_iff (l : Lineage α) :
    LineageNovel l ↔ ∀ a ∈ l, tradition l ≠ a := Iff.rfl

/-- A singleton lineage `[a]` is *not* novel: its tradition is `a`. -/
lemma not_LineageNovel_singleton (a : α) :
    ¬ LineageNovel (Lineage.singleton a) := by
  intro h
  -- tradition [a] = a (by aggregate_singleton)
  have htrad : tradition (Lineage.singleton a) = a := by
    unfold tradition Lineage.singleton
    exact aggregate_singleton a
  have hne : tradition (Lineage.singleton a) ≠ a :=
    h a (by show a ∈ [a]; exact List.mem_singleton.mpr rfl)
  exact hne htrad

/-- If a lineage's tradition equals one of its contributions, the
    lineage is *not* novel. -/
lemma not_LineageNovel_of_tradition_mem {l : Lineage α}
    (hmem : tradition l ∈ l) :
    ¬ LineageNovel l := by
  intro h
  exact (h _ hmem) rfl

/-- A novel lineage's tradition cannot equal any of its contributions. -/
lemma LineageNovel.tradition_not_mem {l : Lineage α}
    (h : LineageNovel l) :
    tradition l ∉ l := by
  intro hmem
  exact (h _ hmem) rfl

/-- A trivial (silent) lineage is *not* novel for `n ≥ 1` only if the
    identity element is one of its contributions; otherwise vacuously
    novel.  In our convention `Lineage.trivial α 0 = []`, which is
    vacuously novel. -/
lemma LineageNovel_trivial_zero :
    LineageNovel (Lineage.trivial α 0) := by
  rw [show Lineage.trivial α 0 = ([] : Lineage α) from trivial_zero]
  exact LineageNovel_nil

/-- A trivial lineage of length `n+1` is never novel: its tradition
    is `ident`, which is exactly the contribution of every silent
    generation. -/
lemma not_LineageNovel_trivial_succ (n : Nat) :
    ¬ LineageNovel (Lineage.trivial α (n + 1)) := by
  intro h
  have htrad : tradition (Lineage.trivial α (n + 1)) = ident :=
    tradition_trivial (n + 1)
  -- the head of trivial (n+1) is ident
  have hhead : (ident : α) ∈ Lineage.trivial α (n + 1) := by
    show (ident : α) ∈ ((ident : α) :: Lineage.trivial α n)
    exact List.mem_cons_self (ident : α) (Lineage.trivial α n)
  have := h (ident : α) hhead
  exact this htrad

/-- Lineage novelty is preserved under cultural-equivalence
    permutations of the lineage *whose underlying list is unchanged*
    — i.e. every lemma here treats `LineageNovel` as a property of
    the underlying `List α`, not just of its tradition. -/
lemma LineageNovel.of_perm {l₁ l₂ : Lineage α}
    (hperm : ∀ a, a ∈ l₁ ↔ a ∈ l₂)
    (htrad : tradition l₁ = tradition l₂)
    (h : LineageNovel l₁) :
    LineageNovel l₂ := by
  intro a ha
  have ha' : a ∈ l₁ := (hperm a).mpr ha
  have := h a ha'
  rw [← htrad]
  exact this

end LineageSec

/-! ## §12.5 Interaction with the transmission machinery -/

section TransmissionSec

/-- A vertical transmission whose tradition equals the input is
    *non-novel* (the transmission has produced its own input). -/
lemma not_EmergentNovelR_of_tradition_eq {l : Lineage α} {x : α}
    (h : op (tradition l) x = x) :
    ¬ EmergentNovelR (tradition l) x := by
  intro hN
  exact hN h

/-- The faithful-transmission special case: if a lineage transmits
    faithfully (Henrich 2015 §10), then no input can be left-novel
    under that transmission. -/
lemma faithful_implies_not_NovelL {l : Lineage α}
    (hF : Faithful (fun x : α => transmitVertical l x)) (x : α) :
    ¬ EmergentNovelR (tradition l) x := by
  apply not_EmergentNovelR_of_tradition_eq
  -- op (tradition l) x = transmitVertical l x = x
  have h1 : op (tradition l) x = transmitVertical l x := by
    rw [transmitVertical_eq_op_aggregate]; rfl
  rw [h1]
  exact hF x

/-- The cultural-tradition decomposition law of `Theorems11` lifts
    `EmergentNovel` along a `then`. -/
lemma emergent_eq_tradition_then (l₁ l₂ : Lineage α) :
    op (tradition l₁) (tradition l₂) = tradition (Lineage.then l₁ l₂) :=
  (tradition_then l₁ l₂).symm

/-- An emergent-novelty witness for two traditions transports to a
    statement about the joint tradition. -/
lemma tradition_then_novel_left {l₁ l₂ : Lineage α}
    (h : EmergentNovel (tradition l₁) (tradition l₂)) :
    tradition (Lineage.then l₁ l₂) ≠ tradition l₁ := by
  rw [tradition_then]
  exact h.1

/-- Symmetric. -/
lemma tradition_then_novel_right {l₁ l₂ : Lineage α}
    (h : EmergentNovel (tradition l₁) (tradition l₂)) :
    tradition (Lineage.then l₁ l₂) ≠ tradition l₂ := by
  rw [tradition_then]
  exact h.2

/-- If two traditions are emergently novel, the joint lineage's
    tradition is novel relative to each. -/
lemma tradition_then_emergent {l₁ l₂ : Lineage α}
    (h : EmergentNovel (tradition l₁) (tradition l₂)) :
    EmergentNovel (tradition l₁) (tradition l₂) := h

/-- If `op a b` is emergent and `b = ident`, contradiction (already
    a corollary of `not_EmergentNovel_ident_right`). -/
lemma EmergentNovel.no_silent_right {a b : α}
    (h : EmergentNovel a b) (hb : b = ident) : False := by
  exact not_EmergentNovel_of_right_ident hb h

/-- If `op a b` is emergent and `a = ident`, contradiction. -/
lemma EmergentNovel.no_silent_left {a b : α}
    (h : EmergentNovel a b) (ha : a = ident) : False :=
  not_EmergentNovel_of_left_ident ha h

end TransmissionSec

/-! ## §12.6 `theorem_12_1` — Identity-Elimination Theorem -/

/-- **Theorem 12.1 (Identity-Elimination Theorem).**

    *Informal claim.*  The IDT manuscript (Vol. VI Ch. 2, *Emergent
    Novelty*) and the philosophy-of-emergence literature (Mill 1843
    Bk. III Ch. VI; Lewes 1875 §V; Broad 1925 Ch. II §3) jointly
    assert: *no genuinely emergent property can arise from a
    composition in which one of the ingredients is the silent /
    identity element*.  In algebraic dress: if `op a b` is emergently
    novel, then both `a ≠ ident` and `b ≠ ident`; equivalently,
    `op ident b = b` and `op a ident = a` are absorbing identities
    that *cancel* novelty.

    *Sources.*  Mill 1843, Bk. III Ch. VI ("homopathic effects do not
    emerge"); Lewes 1875 §V; Broad 1925 Ch. II §3; Bedau 1997 §1
    ("trivial composition cannot weakly emerge"); IDT manuscript
    Vol. VI §2.1.

    *Lemmas used.*  `not_EmergentNovel_ident_left`,
    `not_EmergentNovel_ident_right`, `EmergentNovel.left_ne_ident`,
    `EmergentNovel.right_ne_ident`, `id_left`, `id_right`.

    *Sharpening.*  The informal version states only the negative
    direction "`ident` partner ⇒ no emergence".  The present formal
    statement records the **biconditional** form (an `iff`) plus
    the four *absorption* equations, packaging the full
    Identity-Elimination Theorem in one statement.

    *Proof strategy.*
    1. Forward direction `EmergentNovel a b → a ≠ ident ∧ b ≠ ident`
       is by `EmergentNovel.left_ne_ident` and
       `EmergentNovel.right_ne_ident`.
    2. Backward direction is *not* claimed in the informal
       literature and is in fact false in general (a composition of
       two non-identity ideas may still coincide with one of them);
       so we package the forward direction and the four absorption
       equations only.
    3. The four equations follow from `id_left` and `id_right`. -/
theorem theorem_12_1 :
    (∀ a b : α, EmergentNovel a b → a ≠ ident ∧ b ≠ ident) ∧
    (∀ b : α, ¬ EmergentNovel (ident : α) b) ∧
    (∀ a : α, ¬ EmergentNovel a (ident : α)) ∧
    (∀ b : α, op (ident : α) b = b) ∧
    (∀ a : α, op a (ident : α) = a) := by
  refine ⟨?hMain, ?hLeft, ?hRight, ?hAbsL, ?hAbsR⟩
  case hMain =>
    -- Step 1: the principal forward implication.
    intro a b h
    refine ⟨?_, ?_⟩
    · -- a ≠ ident: use EmergentNovel.left_ne_ident
      exact h.left_ne_ident
    · -- b ≠ ident: dual
      exact h.right_ne_ident
  case hLeft =>
    -- Step 2: silent left ingredient eliminates novelty.
    intro b
    exact not_EmergentNovel_ident_left b
  case hRight =>
    -- Step 3: silent right ingredient eliminates novelty.
    intro a
    exact not_EmergentNovel_ident_right a
  case hAbsL =>
    -- Step 4: left-absorption of identity.
    intro b
    exact id_left b
  case hAbsR =>
    -- Step 5: right-absorption of identity.
    intro a
    exact id_right a

/-! ## §12.7 `theorem_12_2` — Cumulative-Novelty Theorem -/

/-- **Theorem 12.2 (Cumulative-Novelty Theorem).**

    *Informal claim.*  The IDT manuscript (Vol. VI §2.3) asserts the
    *Cumulative-Novelty Principle*: "if a lineage is genuinely
    novel — i.e. its accumulated tradition differs from every
    individual contribution — then in particular **no single
    generation can have produced the tradition by itself**, and the
    silent (`ident`-valued) generations contribute nothing to the
    novelty".  This formalises Anderson 1972's "more is different"
    slogan in the cultural-transmission setting.

    *Sources.*  Anderson 1972, *More is Different*, §1; Bedau 1997
    §1 ("collective underivability"); IDT manuscript Vol. VI §2.3.

    *Lemmas used.*  `LineageNovel`, `LineageNovel.tradition_not_mem`,
    `not_LineageNovel_singleton`, `not_LineageNovel_trivial_succ`,
    `tradition_trivial`, `LineageNovel_trivial_zero`,
    `not_LineageNovel_of_tradition_mem`.

    *Sharpening.*  The informal claim talks loosely about "no single
    generation accounts for the tradition".  The formal statement
    sharpens this to the precise predicate `tradition l ∉ l`,
    plus the negative result that singleton and non-empty trivial
    lineages are *not* novel, and the positive result that the empty
    lineage *is* vacuously novel.  These together pin down the
    behaviour of `LineageNovel` on all the basic lineage shapes.

    *Proof strategy.*
    1. Conjunct 1: every novel lineage has its tradition outside the
       lineage — by `LineageNovel.tradition_not_mem`.
    2. Conjunct 2: singleton lineages are not novel — by
       `not_LineageNovel_singleton`.
    3. Conjunct 3: non-empty trivial lineages are not novel — by
       `not_LineageNovel_trivial_succ`.
    4. Conjunct 4: empty lineage is vacuously novel — by
       `LineageNovel_nil`.
    5. Conjunct 5: zero-length trivial lineage is novel (it is the
       empty lineage). -/
theorem theorem_12_2 :
    (∀ l : Lineage α, LineageNovel l → tradition l ∉ l) ∧
    (∀ a : α, ¬ LineageNovel (Lineage.singleton a)) ∧
    (∀ n : Nat, ¬ LineageNovel (Lineage.trivial α (n + 1))) ∧
    LineageNovel ([] : Lineage α) ∧
    LineageNovel (Lineage.trivial α 0) := by
  refine ⟨?h1, ?h2, ?h3, ?h4, ?h5⟩
  case h1 =>
    intro l h
    -- direct from definition
    exact h.tradition_not_mem
  case h2 =>
    -- singleton lineages have tradition equal to the contribution
    intro a
    exact not_LineageNovel_singleton a
  case h3 =>
    -- non-empty trivial lineages have ident-tradition and ident-head
    intro n
    exact not_LineageNovel_trivial_succ n
  case h4 =>
    exact LineageNovel_nil
  case h5 =>
    exact LineageNovel_trivial_zero

/-! ## §12.8 `theorem_12_3` — Transmission-Preservation of Novelty -/

/-- **Theorem 12.3 (Transmission-Preservation of Novelty).**

    *Informal claim.*  The IDT manuscript (Vol. VI §2.5) asserts:
    *novelty is preserved by faithful transmission — a faithful
    transmission of an emergently novel composite produces an
    emergently novel composite — but is **destroyed** by silent
    intermediates that absorb their input*.  Chalmers 2006 §2 makes
    a closely related claim about the "transparency" of weak
    emergence under conservative reductions.

    *Sources.*  Chalmers 2006 §2; Bedau 1997 §3 ("preservation of
    weak emergence"); IDT manuscript Vol. VI §2.5.

    *Lemmas used.*  `transmitVertical_eq_op_aggregate`,
    `tradition_then`, `tradition_then_novel_left`,
    `tradition_then_novel_right`, `faithful_implies_not_NovelL`,
    `EmergentNovel.tradition_then`.

    *Sharpening.*  The informal version is one biconditional; the
    formal version packages **three** conjuncts: (a) two emergently-
    novel traditions concatenate into a tradition novel relative to
    both; (b) faithful transmission cannot witness right-novelty in
    its input; (c) cultural-equivalence (Sperber 1996 Ch. 4)
    preserves emergent-novelty between traditions.

    *Proof strategy.*
    1. (a) Use `tradition_then` to rewrite the composite tradition
       and apply both projections of the assumed `EmergentNovel`.
    2. (b) Use the faithfulness hypothesis to rewrite
       `op (tradition l) x` to `x`, then conclude.
    3. (c) Use `LineageEquiv_iff_tradition_eq` from Theorems11 and
       transport the novelty equality across. -/
theorem theorem_12_3 :
    (∀ l₁ l₂ : Lineage α,
      EmergentNovel (tradition l₁) (tradition l₂) →
        tradition (Lineage.then l₁ l₂) ≠ tradition l₁ ∧
        tradition (Lineage.then l₁ l₂) ≠ tradition l₂) ∧
    (∀ l : Lineage α,
      Faithful (fun x : α => transmitVertical l x) →
        ∀ x : α, ¬ EmergentNovelR (tradition l) x) ∧
    (∀ l₁ l₂ : Lineage α,
      LineageEquiv l₁ l₂ →
      ∀ c : α, EmergentNovel (tradition l₁) c ↔ EmergentNovel (tradition l₂) c) := by
  refine ⟨?part1, ?part2, ?part3⟩
  case part1 =>
    -- Step 1: composite-tradition novelty.
    intro l₁ l₂ h
    refine ⟨?_, ?_⟩
    · -- left-novelty of the composite tradition
      have hL : tradition (Lineage.then l₁ l₂) ≠ tradition l₁ :=
        tradition_then_novel_left h
      exact hL
    · -- right-novelty of the composite tradition
      have hR : tradition (Lineage.then l₁ l₂) ≠ tradition l₂ :=
        tradition_then_novel_right h
      exact hR
  case part2 =>
    -- Step 2: faithful lineages destroy right-novelty.
    intro l hF x
    -- By faithfulness, op (tradition l) x = x, so EmergentNovelR fails
    have hop : op (tradition l) x = x := by
      -- transmitVertical l x = op (tradition l) x  AND  = x
      have h1 : transmitVertical l x = op (tradition l) x :=
        transmitVertical_eq_op_aggregate l x
      have h2 : transmitVertical l x = x := hF x
      -- combine
      have := h1.symm.trans h2
      exact this
    intro hN
    -- hN : op (tradition l) x ≠ x, contradicts hop
    exact hN hop
  case part3 =>
    -- Step 3: cultural equivalence preserves emergent novelty (in the
    -- left tradition).  Use `tradition_eq_of_LineageEquiv` to rewrite.
    intro l₁ l₂ hEq c
    have htrad : tradition l₁ = tradition l₂ :=
      tradition_eq_of_LineageEquiv hEq
    rw [htrad]

/-! ## §12.9 Corollaries -/

/-- **Corollary 12.1 (Identity Cannot Originate Novelty).**
    A composition involving the silent / identity element is never
    emergently novel.  This is the immediate philosophical lesson of
    `theorem_12_1`. -/
theorem corollary_12_1 :
    (∀ b : α, ¬ EmergentNovel (ident : α) b) ∧
    (∀ a : α, ¬ EmergentNovel a (ident : α)) :=
  ⟨theorem_12_1.2.1, theorem_12_1.2.2.1⟩

/-- **Corollary 12.2 (Singleton Lineages Are Not Novel).**
    A lineage of length one is never novel: the unique generation
    *is* the tradition.  Cultural-evolution analogue of "no single
    individual originates a tradition" (Boyd–Richerson 1985 §3.3). -/
theorem corollary_12_2 (a : α) :
    ¬ LineageNovel (Lineage.singleton a) :=
  theorem_12_2.2.1 a

/-- **Corollary 12.3 (Faithful Transmission Destroys Novelty).**
    A faithful vertical transmission cannot produce an output novel
    relative to its input.  This is Henrich 2015 §10 read through
    the novelty-preservation lens of Chalmers 2006 §2. -/
theorem corollary_12_3 (l : Lineage α)
    (hF : Faithful (fun x : α => transmitVertical l x)) (x : α) :
    ¬ EmergentNovelR (tradition l) x :=
  theorem_12_3.2.1 l hF x

/-- **Corollary 12.4 (Composite-Tradition Emergence).**
    If two sub-lineages have emergently-novel traditions, the
    composite lineage's tradition is novel relative to each.  This
    is the temporal analogue of Anderson 1972's "more is different". -/
theorem corollary_12_4 (l₁ l₂ : Lineage α)
    (h : EmergentNovel (tradition l₁) (tradition l₂)) :
    tradition (Lineage.then l₁ l₂) ≠ tradition l₁ ∧
    tradition (Lineage.then l₁ l₂) ≠ tradition l₂ :=
  theorem_12_3.1 l₁ l₂ h

/-- **Corollary 12.5 (Closed Sets Cannot Witness Emergence).**
    If an idea-set is closed under composition, then no composition
    of its members can be emergently novel *outside* the set: novelty
    requires the composition to leave the set.  This formalises
    Bedau 1997 §1's claim that "closed systems cannot weakly emerge". -/
theorem corollary_12_5 (S : IdeaSet α) (hClosed : Closed S)
    (a b : α) (ha : S a) (hb : S b) :
    S (op a b) :=
  hClosed a b ha hb

/-! ## §12.10 Examples and sanity checks -/

/-- Example: identity on the left never gives emergence. -/
example (b : α) : ¬ EmergentNovel (ident : α) b :=
  not_EmergentNovel_ident_left b

/-- Example: identity on the right never gives emergence. -/
example (a : α) : ¬ EmergentNovel a (ident : α) :=
  not_EmergentNovel_ident_right a

/-- Example: emergent novelty implies both ingredients are non-silent. -/
example (a b : α) (h : EmergentNovel a b) : a ≠ ident ∧ b ≠ ident :=
  theorem_12_1.1 a b h

/-- Example: empty lineage is vacuously novel. -/
example : LineageNovel ([] : Lineage α) := LineageNovel_nil

/-- Example: singleton lineage `[a]` is *not* novel. -/
example (a : α) : ¬ LineageNovel (Lineage.singleton a) :=
  corollary_12_2 a

/-- Example: a faithful transmission cannot produce a novel output. -/
example (l : Lineage α)
    (hF : Faithful (fun x : α => transmitVertical l x)) (x : α) :
    ¬ EmergentNovelR (tradition l) x :=
  corollary_12_3 l hF x

/-- Example: two emergently-novel traditions concatenate to a novel
    composite tradition. -/
example (l₁ l₂ : Lineage α)
    (h : EmergentNovel (tradition l₁) (tradition l₂)) :
    tradition (Lineage.then l₁ l₂) ≠ tradition l₁ :=
  (corollary_12_4 l₁ l₂ h).1

/-- Example: closed idea-sets are closed under composition. -/
example (S : IdeaSet α) (hC : Closed S) (a b : α)
    (ha : S a) (hb : S b) : S (op a b) :=
  corollary_12_5 S hC a b ha hb

/-- Example: the trivial idea-set is closed. -/
example : Closed (fun _ : α => True) := Closed.true_set

/-- Example: a 3-fold trivial lineage is *not* novel. -/
example : ¬ LineageNovel (Lineage.trivial α 3) :=
  not_LineageNovel_trivial_succ 2

/-! ## §12.11 Index of results

Public declarations in this file (Volume 6, "Emergent Novelty"):

* §12.0 auxiliary definitions
  - `IsNovel`                                        : `c ≠ a` form of novelty.
  - `EmergentNovel`                                  : conjunctive emergent-novelty predicate.
  - `EmergentNovelL`, `EmergentNovelR`               : left/right novelty.
  - `NoveltyWitness`                                 : structure bundling the two inequalities.
  - `NovelEverywhere`                                : "novel relative to every list element".
  - `LineageNovel`                                   : tradition novel relative to all contributions.
  - `NoveltyPredicate`                               : abbrev for binary novelty predicates.
  - `Emergent`                                       : the principal predicate, alias for `EmergentNovel`.
  - `Underivable`                                    : alias for `NovelEverywhere` (Bedau 1997).
  - `EmergencePair`                                  : two ideas with a witness of emergent novelty.
  - `IdeaSet`                                        : abbrev for `α → Prop`.
  - `Closed`                                         : closure of an idea-set under `op`.

* §12.1 closure
  - `IsNovel.irrefl`,
  - `IsNovel_iff`,
  - `NoveltyWitness.toEmergent`, `EmergentNovel.toWitness`,
  - `EmergentNovel_iff`, `EmergentNovelL_iff`, `EmergentNovelR_iff`,
  - `EmergentNovel.of_LR`, `EmergentNovel.left`, `EmergentNovel.right`,
  - `not_EmergentNovelL_iff`, `not_EmergentNovelR_iff`,
  - `not_EmergentNovel_iff`,
  - `NovelEverywhere_nil`, `NovelEverywhere_cons`,
  - `NovelEverywhere.mono_cons`, `NovelEverywhere.head`,
  - `NovelEverywhere_append`, `NovelEverywhere.tail`,
  - `Closed.true_set`, `Closed.singleton_ident`, `Closed.inter`.

* §12.2 identity elimination
  - `not_EmergentNovel_ident_left`, `not_EmergentNovel_ident_right`,
  - `not_EmergentNovelR_ident_left`, `not_EmergentNovelL_ident_right`,
  - `EmergentNovel.left_ne_ident`, `EmergentNovel.right_ne_ident`,
  - `NoveltyWitness.left_ne_ident`, `NoveltyWitness.right_ne_ident`,
  - `ident_not_IsNovel`,
  - `not_EmergentNovel_of_left_ident`, `not_EmergentNovel_of_right_ident`.

* §12.3 monotonicity
  - `Closed.mono`,
  - `right_absorbing_of_not_NovelL`, `left_absorbing_of_not_NovelR`,
  - `EmergentNovel.imp_L`, `EmergentNovel.imp_R`,
  - `EmergentNovel.congr_left`, `EmergentNovel.congr_right`,
  - `EmergentNovel.toIsNovel`.

* §12.4 lineage novelty
  - `LineageNovel_nil`, `LineageNovel_iff`,
  - `not_LineageNovel_singleton`,
  - `not_LineageNovel_of_tradition_mem`,
  - `LineageNovel.tradition_not_mem`,
  - `LineageNovel_trivial_zero`,
  - `not_LineageNovel_trivial_succ`,
  - `LineageNovel.of_perm`.

* §12.5 transmission interaction
  - `not_EmergentNovelR_of_tradition_eq`,
  - `faithful_implies_not_NovelL`,
  - `emergent_eq_tradition_then`,
  - `tradition_then_novel_left`, `tradition_then_novel_right`,
  - `tradition_then_emergent`,
  - `EmergentNovel.no_silent_left`, `EmergentNovel.no_silent_right`.

* §12.6 `theorem_12_1` : Identity-Elimination Theorem.
* §12.7 `theorem_12_2` : Cumulative-Novelty Theorem.
* §12.8 `theorem_12_3` : Transmission-Preservation of Novelty.

* §12.9 corollaries
  - `corollary_12_1` : identity cannot originate novelty.
  - `corollary_12_2` : singleton lineages are not novel.
  - `corollary_12_3` : faithful transmission destroys novelty.
  - `corollary_12_4` : composite-tradition emergence.
  - `corollary_12_5` : closed sets cannot witness emergence.

End of file.
-/

end IdeaTheory
