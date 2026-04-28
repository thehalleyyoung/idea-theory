import Mathlib.Tactic
import IdeaTheory.Foundations
import IdeaTheory.Extensions.GameTheory

/-!
# IdeaTheory.Extensions.MeaningGames

A *meaning game* is a strategic interaction in which the players are language
users, the strategies are *uses* of ideas (elements of an idea-algebra
carrier), and the payoffs reward *coordination on meaning*.  When two speakers
compose their uses and the result lies in a designated set of mutually
intelligible meanings, both gain.  This synthesises Wittgenstein's claim that
"the meaning of a word is its use in the language" (Philosophical
Investigations §43) with Lewis's analysis of conventions (Convention, 1969)
as Nash equilibria of coordination games.

The module formalises:

* uses-as-strategies and the `MeaningGame` structure;
* conventions as Nash equilibria (`IsConvention`);
* the *effective meaning* of a profile as the `op`-aggregate of the speakers'
  uses (Wittgenstein: meaning emerges from joint practice);
* family resemblance via shared idempotent "common features";
* the private-language argument as a triviality lemma on single-speaker games;
* Lewis salience / focal points;
* the rule-following paradox (Kripkenstein) as finite underdetermination of
  rules by their observed history;
* a Wittgenstein–Nash bridge: existence of a convention whenever the meaning
  set is non-empty.

No `sorry`, no `admit`.
-/

namespace IdeaTheory.MeaningGames

open IdeaTheory IdeaTheoryStructure Function

universe u

variable {α : Type u} [IdeaTheoryStructure α]

/-! ## §1. Uses, meaning games, and conventions -/

/-- A *use* of an idea is just an element of the idea algebra.  The synonym
records the Wittgensteinian reading: ideas figure in language games as uses,
not as detached entities. -/
abbrev Use (α : Type u) [IdeaTheoryStructure α] := α

/-- A meaning game: a finite roster of `Speaker`s (here `Fin n`), a predicate
`meaningSet` carving out the mutually intelligible ideas, and a real-valued
payoff for each speaker. -/
structure MeaningGame (α : Type u) [IdeaTheoryStructure α] where
  /-- Number of speakers. -/
  n : ℕ
  /-- The set of mutually intelligible meanings. -/
  meaningSet : α → Prop
  /-- Speaker `i`'s payoff at a profile `σ`. -/
  payoff : Fin n → (Fin n → α) → ℝ

/-- The *effective meaning* of a profile is the `op`-aggregate of the speakers'
uses, starting from the identity.  Wittgenstein: meaning emerges from joint
practice; here it is a single element of the carrier obtained by composition. -/
def effectiveMeaning {n : ℕ} (σ : Fin n → α) : α :=
  (List.ofFn σ).foldl op ident

/-- A *convention* is a Nash equilibrium profile: no speaker can strictly
improve by switching to a different use. -/
def IsConvention (G : MeaningGame α) (σ : Fin G.n → α) : Prop :=
  ∀ (i : Fin G.n) (b : α), G.payoff i (update σ i b) ≤ G.payoff i σ

/-- The coordination payoff: 1 if the effective meaning of the profile lies in
`M`, otherwise 0.  This is the canonical pay-off rewarding shared
intelligibility. -/
noncomputable def coordPayoff (n : ℕ) (M : α → Prop) :
    Fin n → (Fin n → α) → ℝ :=
  fun _ σ => by classical exact if M (effectiveMeaning σ) then 1 else 0

/-- The *coordination meaning game* with `n` speakers and meaning set `M`. -/
noncomputable def coordGame (n : ℕ) (M : α → Prop) : MeaningGame α :=
  { n := n, meaningSet := M, payoff := coordPayoff n M }

/-! ## §2. Foundational lemmas about effective meaning -/

private lemma foldl_op_ident_list (l : List α) (a : α)
    (hAll : ∀ x ∈ l, x = (ident : α)) : l.foldl op a = a := by
  induction l generalizing a with
  | nil => simp
  | cons x xs ih =>
      have hx : x = (ident : α) := hAll x (by simp)
      have hrest : ∀ y ∈ xs, y = (ident : α) :=
        fun y hy => hAll y (by simp [hy])
      show xs.foldl op (op a x) = a
      rw [hx, id_right]
      exact ih a hrest

private lemma foldl_op_const_of_idemp {l : List α} {c : α} (h : op c c = c)
    (hAll : ∀ x ∈ l, x = c) : l.foldl op c = c := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      have hx : x = c := hAll x (by simp)
      have hrest : ∀ y ∈ xs, y = c :=
        fun y hy => hAll y (by simp [hy])
      show xs.foldl op (op c x) = c
      rw [hx, h]
      exact ih hrest

private lemma foldl_op_in_M {M : α → Prop}
    (hOp : ∀ a b, M a → M b → M (op a b))
    {l : List α} (hAll : ∀ x ∈ l, M x) {a : α} (ha : M a) :
    M (l.foldl op a) := by
  induction l generalizing a with
  | nil => simpa using ha
  | cons x xs ih =>
      have hx : M x := hAll x (by simp)
      have hrest : ∀ y ∈ xs, M y :=
        fun y hy => hAll y (by simp [hy])
      show M (xs.foldl op (op a x))
      exact ih hrest (hOp a x ha hx)

/-- **L1 (Empty profile).**  With no speakers, no joint practice exists, and
the effective meaning collapses to the identity.  (Wittgenstein: there is no
language without language users.) -/
@[simp] theorem effectiveMeaning_zero (σ : Fin 0 → α) :
    effectiveMeaning σ = (ident : α) := by
  simp [effectiveMeaning]

/-- **L2 (Successor unfolding).**  The effective meaning of an `n+1`-speaker
profile is obtained by folding the remaining speakers' uses over the first
speaker's use.  This is the recursion underlying joint composition. -/
theorem effectiveMeaning_succ {n : ℕ} (σ : Fin (n+1) → α) :
    effectiveMeaning σ
      = (List.ofFn (fun i : Fin n => σ i.succ)).foldl op (σ 0) := by
  unfold effectiveMeaning
  rw [List.ofFn_succ]
  show ((σ 0) :: List.ofFn (fun i : Fin n => σ i.succ)).foldl op ident = _
  show (List.ofFn (fun i : Fin n => σ i.succ)).foldl op (op ident (σ 0)) = _
  rw [id_left]

/-- **L3 (One-speaker game).**  In a monologue the effective meaning is the
sole speaker's use — there is nothing for it to be composed with.  This is the
formal anchor of the private-language argument. -/
theorem effectiveMeaning_one (σ : Fin 1 → α) : effectiveMeaning σ = σ 0 := by
  rw [effectiveMeaning_succ]
  simp

/-- **L4 (Constant identity profile).**  If every speaker plays the identity,
the joint practice produces the identity — empty practice yields empty
meaning. -/
theorem effectiveMeaning_const_ident (n : ℕ) :
    effectiveMeaning (fun _ : Fin n => (ident : α)) = ident := by
  unfold effectiveMeaning
  apply foldl_op_ident_list
  intro x hx
  rw [List.mem_ofFn] at hx
  obtain ⟨_, hi⟩ := hx
  exact hi.symm

/-- **L5 (Idempotent constant profile).**  When every speaker uses the same
idempotent idea `c`, the effective meaning is `c` itself.  This is the
mathematical content of "agreement on meaning": idempotence makes joint
practice a fixed point. -/
theorem effectiveMeaning_const_idemp {n : ℕ} (c : α) (h : op c c = c)
    (hn : 1 ≤ n) :
    effectiveMeaning (fun _ : Fin n => c) = c := by
  match n, hn with
  | n+1, _ =>
      rw [effectiveMeaning_succ]
      apply foldl_op_const_of_idemp h
      intro x hx
      rw [List.mem_ofFn] at hx
      obtain ⟨_, hi⟩ := hx
      exact hi.symm

/-- The *loud-speaker* profile: speaker 0 says `a`, everyone else stays
silent (uses `ident`).  A minimal coordination scheme. -/
def loudProfile (n : ℕ) (a : α) : Fin n → α :=
  fun i => if i.val = 0 then a else ident

/-- **L6 (Loud-speaker effective meaning).**  In the loud-speaker profile, the
effective meaning is the loud speaker's use.  Silence acts as the unit; one
voice carries the meaning. -/
theorem effectiveMeaning_loudProfile {n : ℕ} (hn : 1 ≤ n) (a : α) :
    effectiveMeaning (loudProfile n a) = a := by
  match n, hn with
  | n+1, _ =>
      rw [effectiveMeaning_succ]
      have h0 : loudProfile (n+1) a 0 = a := by simp [loudProfile]
      rw [h0]
      apply foldl_op_ident_list
      intro x hx
      rw [List.mem_ofFn] at hx
      obtain ⟨i, hi⟩ := hx
      have hne : (Fin.succ i).val ≠ 0 := by
        rw [Fin.val_succ]; exact Nat.succ_ne_zero _
      have heq : x = ident := by
        rw [← hi]
        show loudProfile (n+1) a i.succ = ident
        simp [loudProfile, hne]
      exact heq

/-! ## §3. The coordination payoff -/

/-- **L7 (Coordination payoff is binary).**  The coordination payoff equals 1
exactly when the effective meaning belongs to the meaning set.  This is the
Lewis-style "all-or-nothing" coordination signal. -/
theorem coordPayoff_eq_one_iff (n : ℕ) (M : α → Prop) (i : Fin n)
    (σ : Fin n → α) :
    coordPayoff n M i σ = 1 ↔ M (effectiveMeaning σ) := by
  classical
  unfold coordPayoff
  by_cases h : M (effectiveMeaning σ)
  · simp [h]
  · simp [h]

/-- **L8 (Coordination payoff is bounded above by 1).**  No deviation can
yield more than perfect coordination — a Nash-style upper bound on the
meaning game's payoffs. -/
theorem coordPayoff_le_one (n : ℕ) (M : α → Prop) (i : Fin n)
    (σ : Fin n → α) : coordPayoff n M i σ ≤ 1 := by
  classical
  unfold coordPayoff
  split_ifs <;> norm_num

/-- **L9 (Coordination payoff is non-negative).**  Coordination never
*hurts*; it can only fail to help.  This is the Lewis assumption that
coordination problems have no punitive payoffs. -/
theorem coordPayoff_nonneg (n : ℕ) (M : α → Prop) (i : Fin n)
    (σ : Fin n → α) : 0 ≤ coordPayoff n M i σ := by
  classical
  unfold coordPayoff
  split_ifs <;> norm_num

/-! ## §4. Conventions in the coordination game -/

/-- **T1 (Coordinated profiles are conventions).**  Any profile whose joint
practice already lies in the meaning set is a convention: no unilateral
deviation can do better than perfect coordination.  This is the formal
interpretation of "meaning is use" — a successful use *is* the convention. -/
theorem coord_convention_of_meaning {n : ℕ} {M : α → Prop} {σ : Fin n → α}
    (hM : M (effectiveMeaning σ)) : IsConvention (coordGame n M) σ := by
  intro i b
  show coordPayoff n M i (update σ i b) ≤ coordPayoff n M i σ
  have h1 : coordPayoff n M i σ = 1 := (coordPayoff_eq_one_iff n M i σ).mpr hM
  rw [h1]
  exact coordPayoff_le_one n M i (update σ i b)

/-- **T2 (Trivial zero-speaker game).**  The empty profile is vacuously a
convention: with no speakers, no deviation is possible.  A sanity check
mirroring `GameTheory.exists_nash_one_player`. -/
theorem coord_convention_zero (M : α → Prop) (σ : Fin 0 → α) :
    IsConvention (coordGame 0 M) σ := by
  intro i _
  exact i.elim0

/-- **T3 (Wittgenstein–Nash bridge: existence).**  Whenever the meaning set is
non-empty, the coordination game has at least one convention — namely the
loud-speaker profile carrying any element of the meaning set.  This is the
capstone existence theorem: language users can always find a convention if
*any* meaning is mutually intelligible. -/
theorem wittgenstein_nash_existence {n : ℕ} (hn : 1 ≤ n) {M : α → Prop}
    {a : α} (ha : M a) :
    ∃ σ : Fin n → α, IsConvention (coordGame n M) σ := by
  refine ⟨loudProfile n a, ?_⟩
  apply coord_convention_of_meaning
  rw [effectiveMeaning_loudProfile hn]
  exact ha

/-- **T4 (Single-speaker convention exists on finite carriers).**  A
one-speaker meaning game with non-empty meaning set has a convention.  This
mirrors `IdeaTheory.GameTheory.exists_nash_one_player`. -/
theorem exists_convention_one_speaker (M : α → Prop) {a : α} (ha : M a) :
    ∃ σ : Fin 1 → α, IsConvention (coordGame 1 M) σ := by
  refine ⟨fun _ => a, ?_⟩
  apply coord_convention_of_meaning
  rw [effectiveMeaning_one]
  exact ha

/-! ## §5. Refinement, dominance, and closure -/

/-- **T5 (Refinement / extension).**  If `M ⊆ N`, then any profile coordinated
under `M` is a convention of the larger meaning game with meaning set `N`.
Every `G'`-convention restricts to a `G`-convention when meaning sets stand in
inclusion. -/
theorem coord_convention_mono {M N : α → Prop} (hMN : ∀ a, M a → N a)
    {n : ℕ} {σ : Fin n → α} (hM : M (effectiveMeaning σ)) :
    IsConvention (coordGame n N) σ :=
  coord_convention_of_meaning (hMN _ hM)

/-- **T6 (Composition closure of conventions / disjoint payoff rule).**  The
union of two meaning sets inherits the conventions coordinated under either:
agreement is preserved when meaning sets are merged.  This is the disjoint
sum of language games at the convention level. -/
theorem coord_convention_union {M N : α → Prop} {n : ℕ} {σ : Fin n → α}
    (h : M (effectiveMeaning σ) ∨ N (effectiveMeaning σ)) :
    IsConvention (coordGame n (fun a => M a ∨ N a)) σ :=
  coord_convention_of_meaning h

/-- **T7 (Closure of effective meaning under op-closed sets).**  If the
meaning set contains the identity and is closed under composition, then the
joint practice of any all-meaningful profile remains in the meaning set.  This
is the "closure under composition" of intelligibility — Brandom's inferential
closure of conceptual content. -/
theorem effectiveMeaning_in_meaningSet {M : α → Prop} (hId : M ident)
    (hOp : ∀ a b, M a → M b → M (op a b)) {n : ℕ} (σ : Fin n → α)
    (hσ : ∀ i, M (σ i)) : M (effectiveMeaning σ) := by
  unfold effectiveMeaning
  apply foldl_op_in_M hOp _ hId
  intro x hx
  rw [List.mem_ofFn] at hx
  obtain ⟨i, hi⟩ := hx
  rw [← hi]; exact hσ i

/-- **T8 (Constant payoffs make every profile a convention).**  If payoffs are
profile-independent, every profile is a convention — there is no preferred use.
The general analogue of the constant-payoff lemma in classical game theory. -/
theorem convention_of_constant_payoff (G : MeaningGame α)
    (h : ∀ (i : Fin G.n) (s t : Fin G.n → α), G.payoff i s = G.payoff i t)
    (σ : Fin G.n → α) : IsConvention G σ := by
  intro i b
  exact le_of_eq (h i _ _)

/-! ## §6. The private-language argument -/

/-- The *trivial payoff*: every speaker receives 0 regardless of the profile.
A meaning game where coordination is impossible because there is no signal. -/
def trivialPayoff (n : ℕ) : Fin n → (Fin n → α) → ℝ := fun _ _ => 0

/-- **T9 (Private-language argument; Wittgenstein PI §§243–315).**  In a
single-speaker game with no coordination signal (trivial payoff), *every*
profile is vacuously a convention — meaning that "private convention" is
vacuous.  The lone speaker has no way to fix any particular use as the
convention; meaning cannot arise without an audience. -/
theorem private_no_unique_convention (M : α → Prop) (σ : Fin 1 → α) :
    IsConvention
      ({ n := 1, meaningSet := M, payoff := trivialPayoff 1 } : MeaningGame α)
      σ := by
  intro _ _
  exact le_refl _

/-! ## §7. Lewis salience and focal points -/

/-- A use is *salient* (in the sense of a Lewis focal point) if it is
idempotent under composition — repeating it changes nothing. -/
def Salient (a : α) : Prop := op a a = a

/-- **T10 (Lewis salience theorem).**  A salient use that lies in the meaning
set is a convention of the coordination game with that meaning set, played by
every speaker.  This formalises Lewis's claim that focal points produce
self-enforcing conventions. -/
theorem salient_convention_in_meaning {a : α} (hs : Salient a) {n : ℕ}
    (hn : 1 ≤ n) {M : α → Prop} (hM : M a) :
    IsConvention (coordGame n M) (fun _ => a) := by
  apply coord_convention_of_meaning
  show M (effectiveMeaning (fun _ : Fin n => a))
  rw [effectiveMeaning_const_idemp a hs hn]
  exact hM

/-! ## §8. Family resemblance -/

/-- A *family resemblance* (Wittgenstein PI §§65–67) on a class `F` of ideas
is the existence, for any two members, of a shared idempotent "common feature"
that absorbs each of them.  Concretely: a witness `c` with `c ⋆ c = c`,
`c ⋆ a = a`, and `c ⋆ b = b`. -/
def FamilyResemblance (F : α → Prop) : Prop :=
  ∀ a, F a → ∀ b, F b → ∃ c : α, op c c = c ∧ op c a = a ∧ op c b = b

/-- **T11 (Family resemblance yields an idempotent).**  Any non-empty
family-resemblance class has an idempotent "common feature" that absorbs at
least one of its members.  Wittgenstein's overlapping-similarities picture is
witnessed by a shared sub-structure. -/
theorem family_resemblance_idempotent {F : α → Prop} (hF : FamilyResemblance F)
    {a : α} (ha : F a) : ∃ c : α, Salient c ∧ op c a = a := by
  obtain ⟨c, hc, hca, _⟩ := hF a ha a ha
  exact ⟨c, hc, hca⟩

/-- **T12 (Family resemblance ⇒ convention exists).**  A non-empty
family-resemblance class supports a convention in the coordination game on
that class: pick any member and play the loud-speaker profile.  Family
resemblance is therefore a sufficient condition for stable coordination. -/
theorem family_resemblance_convention {F : α → Prop} (_ : FamilyResemblance F)
    {a : α} (ha : F a) {n : ℕ} (hn : 1 ≤ n) :
    ∃ σ : Fin n → α, IsConvention (coordGame n F) σ :=
  wittgenstein_nash_existence hn ha

/-! ## §9. Strict dominance -/

/-- A use `u` *strictly Wittgenstein-dominates* `u'` for speaker `i` if, at
every opponent profile, switching from `u'` to `u` strictly increases `i`'s
payoff. -/
def StrictlyDominates (G : MeaningGame α) (i : Fin G.n) (u u' : α) : Prop :=
  ∀ σ : Fin G.n → α, G.payoff i (update σ i u') < G.payoff i (update σ i u)

/-- **T13 (Strict dominance ⇒ unique convention).**  If a single use `u`
strictly dominates every alternative for every speaker, then every convention
has every speaker playing `u` — the convention is unique up to permutation
(here vacuous, since speakers all play the same use). -/
theorem dominance_unique {G : MeaningGame α} {u : α}
    (hd : ∀ i : Fin G.n, ∀ u' : α, u' ≠ u → StrictlyDominates G i u u')
    {σ : Fin G.n → α} (hσ : IsConvention G σ) :
    ∀ i : Fin G.n, σ i = u := by
  intro i
  by_contra hne
  have hstrict := hd i (σ i) hne σ
  rw [update_eq_self] at hstrict
  have hN := hσ i u
  linarith

/-! ## §10. The rule-following paradox (Kripkenstein) -/

/-- **T14 (Kripkenstein finite underdetermination).**  For any finite history
`h` and any value `val`, there exist two distinct rules `r₁ ≠ r₂` that both
agree on the observation `h ↦ val`.  Concretely: the constant-`val` rule and
a rule that agrees on `h` but flips on a longer input.  Hence finite
observation can never single out a rule — Wittgenstein's rule-following
paradox in its sharpest finite form. -/
theorem kripkenstein_underdetermination {a b : α} (hab : a ≠ b)
    (h : List α) :
    ∃ r₁ r₂ : List α → α, r₁ h = r₂ h ∧ r₁ ≠ r₂ := by
  classical
  refine ⟨(fun _ => a), (fun l => if l = h then a else b), ?_, ?_⟩
  · simp
  · intro heq
    have hne : h ++ [ident] ≠ h := by
      intro hcontra
      have hlen : (h ++ [ident]).length = h.length := by rw [hcontra]
      simp at hlen
    have key : (fun _ : List α => a) (h ++ [ident])
              = (fun l => if l = h then a else b) (h ++ [ident]) :=
      congrFun heq (h ++ [ident])
    simp only [if_neg hne] at key
    exact hab key

/-! ## §11. Iterated meaning games / cultural drift -/

/-- The *iterated meaning set*: at step `0` it is the original meaning set;
at step `k+1` it adds all `op`-products of an earlier-iterated meaning with a
base meaning.  Models cultural transmission with non-erasing accretion. -/
def iterMeaning (M : α → Prop) : ℕ → α → Prop
  | 0       => M
  | k+1     => fun a => iterMeaning M k a ∨
                          ∃ b c, iterMeaning M k b ∧ M c ∧ a = op b c

/-- **T15 (Cultural drift is monotone / non-erasing transmission).**  Under
the non-erasing transmission rule, the support of the iterated meaning set is
monotonically non-decreasing: every meaning available at step `k` remains
available at step `k+1`.  Cultural ratchet, formalised. -/
theorem iterMeaning_monotone {M : α → Prop} (k : ℕ) (a : α) :
    iterMeaning M k a → iterMeaning M (k+1) a := by
  intro h
  exact Or.inl h

/-! ## §12. Aggregation -/

/-- **T16 (Aggregation theorem for constant conventions).**  When the
convention has every speaker play the same salient (idempotent) use, the
effective meaning of the convention is exactly that use; if it lies in the
meaning set, the convention realises perfect coordination.  This is the
"agreed reading" of a unanimous convention. -/
theorem aggregation_constant_convention {n : ℕ} (hn : 1 ≤ n) {a : α}
    (ha : Salient a) {M : α → Prop} (hM : M a) :
    M (effectiveMeaning (fun _ : Fin n => a)) := by
  rw [effectiveMeaning_const_idemp a ha hn]
  exact hM

end IdeaTheory.MeaningGames
