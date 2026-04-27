import IdeaTheory.Foundations
import IdeaTheory.Theorems10

/-!
# IdeaTheory: Theorems 11 — Cultural Transmission (Volume 6)

## What this file formalizes

This file belongs to Volume 6 of the IdeaTheory project, the
*Advanced Applications and Unifying Perspectives* arc, and develops
the formal theory of **cultural transmission** of ideas.  Where
Volume 5 reread the Volume 1 algebraic operation `op : α → α → α`
as the *aggregation* of two co-present agents into a coalition, the
present file rereads the same operation as a *temporal* operation:
the way a previously-held idea is transformed by an agent who
*receives* and *transmits* it onward to the next generation.  Under
this reading the operator `leftMul a : x ↦ op a x` is a single
"transmission step" by an agent who contributes the cultural
material `a` to the inherited idea `x`, and a finite *lineage* of
agents `[a₁, …, aₙ]` is a transmission chain whose total effect on
an inherited idea `x` is `op a₁ (op a₂ (… (op aₙ x) …))`.  The IDT
manuscript (Volume VI, Chapter 1, *"Cultural Transmission of
Ideas"*) argues that this rereading lets the algebraic theorems of
Volume 1 pull double duty as the basic laws governing how ideas
propagate across generations: associativity becomes "inheritance is
order-independent across consecutive ancestors", the identity
element becomes the "silent generation" who transmits without
adding, and the various silent-agent invariance lemmas become
"culturally invisible generations may be inserted or removed
without changing what the lineage transmits".

## Authors and works drawn upon

In addition to the IDT manuscript itself, this file draws on the
non-formalized cultural-evolution literature: Cavalli-Sforza and
Feldman, *Cultural Transmission and Evolution* (Princeton, 1981),
Chapters 1–3, for the very notion of a cultural transmission rule
between generations; Boyd and Richerson, *Culture and the
Evolutionary Process* (Chicago, 1985), §3.3, for the discussion of
"vertical" and "horizontal" transmission lineages; Sperber, *Explaining
Culture* (Blackwell, 1996), Chapter 4, for the concept of a
"cultural variant" and the notion that two transmission paths are
equivalent when their final cultural products coincide; and Henrich,
*The Secret of Our Success* (Princeton, 2015), §10, for the idea of
"faithful" transmission as the special case in which the receiving
agent contributes nothing of their own.  The technical pattern of
modelling transmission as composition of left-multiplication maps
follows MacLane, *Categories for the Working Mathematician*
(Springer, 1971), §I.1, where any monoidal element acts on its
ambient set by left translation.

## Design decisions and conventions

* We continue to take `IdeaTheoryStructure` as the only primitive
  algebraic context.  All transmission machinery is built on top of
  `op`, `ident`, `assoc`, `id_left`, `id_right` — nothing else.
* A *transmission* is a function `α → α`.  The composition of two
  transmissions is ordinary function composition.
* A *lineage* is reused from `Theorems10` as `Coalition α := List α`,
  but reread as a *temporal* sequence of agents rather than a
  spatial coalition.  The two readings are mathematically identical;
  it is only the application that differs.
* The transmission attached to a lineage `[a₁,…,aₙ]` is
  `leftMul a₁ ∘ leftMul a₂ ∘ … ∘ leftMul aₙ`, which on input `x`
  evaluates to `op a₁ (op a₂ (… (op aₙ x) …))`.  This is the
  *vertical* transmission of Boyd–Richerson 1985.
* A transmission is *faithful* iff it is the identity on `α`; this
  matches Henrich 2015 §10.
* Two lineages are *culturally equivalent* iff their associated
  transmissions agree on every input.  This is Sperber 1996's
  cultural-variant equivalence.

## Roadmap

1. §11.0  Auxiliary definitions: `Transmission`, `idTrans`,
   `composeTrans`, `leftMul`, `rightMul`, `Lineage`,
   `transmitVertical`, `transmitHorizontal`, `Generation`,
   `Tradition`, `Faithful`, `LineageEquiv`, `Variant`.
2. §11.1  Closure lemmas (identity, composition).
3. §11.2  Vertical transmission and the link to `aggregate`.
4. §11.3  Faithful transmission and silent generations.
5. §11.4  Lineage equivalence and Sperber variants.
6. §11.5  `theorem_11_1` — Vertical-Transmission Composition Law.
7. §11.6  `theorem_11_2` — Faithfulness Characterization.
8. §11.7  `theorem_11_3` — Cultural-Equivalence Congruence.
9. §11.8  Corollaries `corollary_11_1`–`corollary_11_5`.
10. §11.9 Examples and sanity checks.
11. End-of-file index.

## Role inside Volume 6

Volume 6 unifies the social-, humanistic-, cognitive-, and
emergence-flavoured rereadings of Volume 1 by showing that several
of them are different *temporal* projections of the same underlying
algebra.  The present file gives the technical core of one such
projection — the *cultural-transmission* projection — and is reused
by later files in Volume 6 to model both the formation of cultural
traditions and the propagation of cognitive structures across
agents.  All later cultural- and tradition-flavoured results in the
project ultimately depend on `theorem_11_1`, `theorem_11_2`,
`theorem_11_3` proved here.
-/

namespace IdeaTheory

open IdeaTheoryStructure

variable {α : Type*} [inst : IdeaTheoryStructure α]

/-! ## §11.0 Auxiliary definitions for cultural transmission -/

/-- A *transmission* is an endofunction on the carrier of ideas.
    It models the rule "given an inherited idea, produce the idea
    you transmit onward".  Compare Cavalli-Sforza/Feldman 1981 §1.2
    where a "transmission rule" is exactly such a function. -/
abbrev Transmission (α : Type*) := α → α

/-- The *identity transmission*: pass on what you received.  This is
    the cultural counterpart of the algebraic `ident` and corresponds
    to Henrich 2015 §10's "perfectly faithful" transmission. -/
def idTrans (α : Type*) : Transmission α := fun x => x

/-- *Composition of transmissions*: first apply `g`, then `f`. -/
def composeTrans (f g : Transmission α) : Transmission α :=
  fun x => f (g x)

/-- The *left-multiplication transmission* by an agent's
    contribution `a`.  This is the canonical "vertical transmission
    by a single generation" of Boyd–Richerson 1985, §3.3. -/
def leftMul [IdeaTheoryStructure α] (a : α) : Transmission α :=
  fun x => op a x

/-- The *right-multiplication transmission* by an agent's
    contribution `a`.  This models a "horizontal transmission" in
    which the new contribution is appended after the inherited
    material rather than prepended.  Cf. Boyd–Richerson 1985, §3.3. -/
def rightMul [IdeaTheoryStructure α] (a : α) : Transmission α :=
  fun x => op x a

/-- A *lineage* of agents in the cultural-transmission reading is a
    finite sequence of contributors.  We reuse the `Coalition`
    abbreviation from `Theorems10`, with the temporal interpretation
    detailed in the module docstring. -/
abbrev Lineage (α : Type*) := Coalition α

/-- The *vertical transmission* of an inherited idea `x` along a
    lineage `[a₁, …, aₙ]` produces
    `op a₁ (op a₂ (… (op aₙ x) …))`.  This is the standard model of
    Cavalli-Sforza/Feldman 1981 §1.2 "vertical transmission". -/
def transmitVertical [IdeaTheoryStructure α] :
    Lineage α → α → α
  | [],      x => x
  | a :: as, x => op a (transmitVertical as x)

/-- The *horizontal transmission* of an inherited idea `x` along a
    lineage `[a₁, …, aₙ]` produces
    `op (op (… (op x a₁) …) aₙ`.  This is the dual of
    `transmitVertical` and corresponds to Boyd–Richerson 1985's
    horizontal-transmission case. -/
def transmitHorizontal [IdeaTheoryStructure α] :
    α → Lineage α → α
  | x, []      => x
  | x, a :: as => transmitHorizontal (op x a) as

/-- A *generation* in the IDT cultural model is just an inhabitant
    of `α` paired with its transmission rule.  Bundling them is
    convenient for stating temporal lemmas. -/
structure Generation (α : Type*) [IdeaTheoryStructure α] where
  /-- The cultural contribution of this generation. -/
  contribution : α
  /-- The transmission rule used by this generation. -/
  rule         : Transmission α

/-- The *cultural tradition* of a lineage is the aggregate of the
    contributions of all its generations.  This re-uses
    `Theorems10.aggregate` and matches the IDT manuscript's
    Vol. VI §1.4 definition of *tradition*. -/
def tradition [IdeaTheoryStructure α] (l : Lineage α) : α :=
  aggregate l

/-- A transmission is *faithful* iff it is the identity on every
    input.  Cf. Henrich 2015 §10. -/
def Faithful [IdeaTheoryStructure α] (f : Transmission α) : Prop :=
  ∀ x : α, f x = x

/-- Two lineages are *culturally equivalent* iff their vertical
    transmissions agree on every inherited input.  Cf. Sperber 1996
    Ch. 4: a *cultural variant equivalence*. -/
def LineageEquiv [IdeaTheoryStructure α] (l₁ l₂ : Lineage α) : Prop :=
  ∀ x : α, transmitVertical l₁ x = transmitVertical l₂ x

/-- A *cultural variant* of a lineage: another lineage equivalent to
    it under `LineageEquiv`. -/
def Variant [IdeaTheoryStructure α] (l : Lineage α) : Type _ :=
  { l' : Lineage α // LineageEquiv l l' }

/-- The *trivial lineage*: a lineage of `n` silent generations.
    Reused from `Coalition.trivial`. -/
def Lineage.trivial (α : Type*) [IdeaTheoryStructure α] (n : Nat) :
    Lineage α := Coalition.trivial α n

/-- The *singleton lineage* of a single generation. -/
def Lineage.singleton (a : α) : Lineage α := [a]

/-- The *concatenation* of two lineages: the first generation
    transmits, then the second. -/
def Lineage.then (l₁ l₂ : Lineage α) : Lineage α := l₁ ++ l₂

/-! ## §11.1 Closure lemmas for transmissions and lineages -/

section Closure

/-- The identity transmission applied to any input is the input. -/
lemma idTrans_apply (x : α) : idTrans α x = x := rfl

/-- Composition of transmissions is given by `f (g x)`. -/
lemma composeTrans_apply (f g : Transmission α) (x : α) :
    composeTrans f g x = f (g x) := rfl

/-- The identity is a left-identity for `composeTrans`. -/
lemma idTrans_compose_left (f : Transmission α) :
    composeTrans (idTrans α) f = f := by
  funext x
  rfl

/-- The identity is a right-identity for `composeTrans`. -/
lemma idTrans_compose_right (f : Transmission α) :
    composeTrans f (idTrans α) = f := by
  funext x
  rfl

/-- Composition of transmissions is associative. -/
lemma composeTrans_assoc (f g h : Transmission α) :
    composeTrans (composeTrans f g) h = composeTrans f (composeTrans g h) := by
  funext x
  rfl

/-- `leftMul a` evaluated at `x` is `op a x`. -/
lemma leftMul_apply (a x : α) : leftMul a x = op a x := rfl

/-- `rightMul a` evaluated at `x` is `op x a`. -/
lemma rightMul_apply (a x : α) : rightMul a x = op x a := rfl

/-- `leftMul ident` is the identity transmission. -/
lemma leftMul_ident : leftMul (ident : α) = idTrans α := by
  funext x
  -- leftMul ident x = op ident x = x
  show op (ident : α) x = x
  exact id_left x

/-- `rightMul ident` is the identity transmission. -/
lemma rightMul_ident : rightMul (ident : α) = idTrans α := by
  funext x
  show op x (ident : α) = x
  exact id_right x

/-- Composing two `leftMul` transmissions yields `leftMul` of the
    `op` of the two contributions. -/
lemma leftMul_compose (a b : α) :
    composeTrans (leftMul a) (leftMul b) = leftMul (op a b) := by
  funext x
  show op a (op b x) = op (op a b) x
  exact (assoc a b x).symm

/-- Composing two `rightMul` transmissions yields `rightMul` of the
    `op` of the two contributions, in reverse order. -/
lemma rightMul_compose (a b : α) :
    composeTrans (rightMul a) (rightMul b) = rightMul (op b a) := by
  funext x
  show op (op x b) a = op x (op b a)
  exact assoc x b a

/-- The transmission of an empty lineage is the identity. -/
lemma transmitVertical_nil (x : α) :
    transmitVertical ([] : Lineage α) x = x := rfl

/-- The transmission of a `cons` lineage decomposes via `op`. -/
lemma transmitVertical_cons (a : α) (l : Lineage α) (x : α) :
    transmitVertical (a :: l) x = op a (transmitVertical l x) := rfl

/-- The transmission of a singleton lineage is `leftMul`. -/
lemma transmitVertical_singleton (a x : α) :
    transmitVertical (Lineage.singleton a) x = op a x := by
  unfold Lineage.singleton
  show op a (transmitVertical ([] : Lineage α) x) = op a x
  rw [transmitVertical_nil]

/-- The horizontal transmission of an empty lineage is the identity. -/
lemma transmitHorizontal_nil (x : α) :
    transmitHorizontal x ([] : Lineage α) = x := rfl

/-- The horizontal transmission of a `cons` lineage decomposes. -/
lemma transmitHorizontal_cons (x a : α) (l : Lineage α) :
    transmitHorizontal x (a :: l) = transmitHorizontal (op x a) l := rfl

/-- The horizontal transmission of a singleton lineage is `rightMul`. -/
lemma transmitHorizontal_singleton (x a : α) :
    transmitHorizontal x (Lineage.singleton a) = op x a := by
  unfold Lineage.singleton
  show transmitHorizontal (op x a) ([] : Lineage α) = op x a
  rw [transmitHorizontal_nil]

end Closure

/-! ## §11.2 Vertical transmission and the link to `aggregate` -/

section Vertical

/-- Vertical transmission applied to `ident` recovers the
    cultural-tradition aggregate of the lineage. -/
lemma transmitVertical_at_ident (l : Lineage α) :
    transmitVertical l (ident : α) = aggregate l := by
  induction l with
  | nil =>
      rw [transmitVertical_nil, aggregate_nil]
  | cons a as ih =>
      rw [transmitVertical_cons, aggregate_cons, ih]

/-- The tradition of a lineage equals its vertical transmission of
    `ident`. -/
lemma tradition_eq_transmit_at_ident (l : Lineage α) :
    tradition l = transmitVertical l (ident : α) := by
  unfold tradition
  rw [transmitVertical_at_ident]

/-- Vertical transmission factors through `aggregate`: the
    transmission along `l` of input `x` equals
    `op (aggregate l) x`. -/
lemma transmitVertical_eq_op_aggregate (l : Lineage α) (x : α) :
    transmitVertical l x = op (aggregate l) x := by
  induction l with
  | nil =>
      rw [transmitVertical_nil, aggregate_nil]
      exact (id_left x).symm
  | cons a as ih =>
      rw [transmitVertical_cons, aggregate_cons, ih]
      -- op a (op (aggregate as) x) = op (op a (aggregate as)) x
      exact (assoc a (aggregate as) x).symm

/-- Vertical transmission along a concatenation of lineages factors
    through the two sub-transmissions. -/
lemma transmitVertical_append (l₁ l₂ : Lineage α) (x : α) :
    transmitVertical (l₁ ++ l₂) x
      = transmitVertical l₁ (transmitVertical l₂ x) := by
  induction l₁ with
  | nil =>
      show transmitVertical l₂ x = transmitVertical ([] : Lineage α) (transmitVertical l₂ x)
      rw [transmitVertical_nil]
  | cons a as ih =>
      show transmitVertical (a :: (as ++ l₂)) x
            = transmitVertical (a :: as) (transmitVertical l₂ x)
      rw [transmitVertical_cons, transmitVertical_cons]
      rw [ih]

/-- Vertical transmission along a `then` is the composition of the
    two transmissions. -/
lemma transmitVertical_then (l₁ l₂ : Lineage α) (x : α) :
    transmitVertical (Lineage.then l₁ l₂) x
      = transmitVertical l₁ (transmitVertical l₂ x) := by
  unfold Lineage.then
  exact transmitVertical_append l₁ l₂ x

/-- The vertical-transmission map of a lineage equals the
    `leftMul` map of the lineage's tradition. -/
lemma transmitVertical_eq_leftMul (l : Lineage α) :
    (fun x => transmitVertical l x) = leftMul (tradition l) := by
  funext x
  unfold tradition
  rw [transmitVertical_eq_op_aggregate]
  rfl

/-- Vertical transmission of a singleton lineage `[a]` at `ident` is
    `a` itself. -/
lemma transmitVertical_singleton_at_ident (a : α) :
    transmitVertical (Lineage.singleton a) (ident : α) = a := by
  rw [transmitVertical_singleton]
  exact id_right a

/-- The aggregate of a lineage's `then` decomposes additively. -/
lemma tradition_then (l₁ l₂ : Lineage α) :
    tradition (Lineage.then l₁ l₂) = op (tradition l₁) (tradition l₂) := by
  unfold tradition Lineage.then
  exact aggregate_append l₁ l₂

/-- Compositional form: vertical transmission along `then` is
    `composeTrans` of the two vertical transmissions. -/
lemma transmitVertical_then_compose (l₁ l₂ : Lineage α) :
    (fun x => transmitVertical (Lineage.then l₁ l₂) x)
      = composeTrans (fun x => transmitVertical l₁ x)
                     (fun x => transmitVertical l₂ x) := by
  funext x
  show transmitVertical (Lineage.then l₁ l₂) x
        = transmitVertical l₁ (transmitVertical l₂ x)
  exact transmitVertical_then l₁ l₂ x

/-- Vertical transmission along a trivial lineage of silent
    generations is the identity. -/
lemma transmitVertical_trivial (n : Nat) (x : α) :
    transmitVertical (Lineage.trivial α n) x = x := by
  induction n with
  | zero =>
      show transmitVertical (([] : Lineage α)) x = x
      rw [transmitVertical_nil]
  | succ k ih =>
      show transmitVertical ((ident : α) :: Lineage.trivial α k) x = x
      rw [transmitVertical_cons]
      rw [ih]
      exact id_left x

end Vertical

/-! ## §11.3 Faithful transmission and silent generations -/

section Faithful

/-- The identity transmission is faithful. -/
lemma idTrans_faithful : Faithful (idTrans α) := by
  intro x
  rfl

/-- `leftMul ident` is faithful. -/
lemma leftMul_ident_faithful : Faithful (leftMul (ident : α)) := by
  intro x
  show op (ident : α) x = x
  exact id_left x

/-- `rightMul ident` is faithful. -/
lemma rightMul_ident_faithful : Faithful (rightMul (ident : α)) := by
  intro x
  show op x (ident : α) = x
  exact id_right x

/-- The composition of two faithful transmissions is faithful. -/
lemma composeTrans_faithful {f g : Transmission α}
    (hf : Faithful f) (hg : Faithful g) : Faithful (composeTrans f g) := by
  intro x
  show f (g x) = x
  rw [hg x]
  exact hf x

/-- Vertical transmission along the empty lineage is faithful. -/
lemma transmitVertical_nil_faithful :
    Faithful (fun x : α => transmitVertical ([] : Lineage α) x) := by
  intro x
  show transmitVertical ([] : Lineage α) x = x
  rw [transmitVertical_nil]

/-- Vertical transmission along a trivial lineage is faithful. -/
lemma transmitVertical_trivial_faithful (n : Nat) :
    Faithful (fun x : α => transmitVertical (Lineage.trivial α n) x) := by
  intro x
  exact transmitVertical_trivial n x

/-- A vertical transmission whose tradition is `ident` is faithful. -/
lemma transmitVertical_faithful_of_tradition_ident
    {l : Lineage α} (h : tradition l = ident) :
    Faithful (fun x : α => transmitVertical l x) := by
  intro x
  show transmitVertical l x = x
  rw [transmitVertical_eq_op_aggregate]
  have : aggregate l = ident := by
    have ht : tradition l = aggregate l := rfl
    rw [← ht]; exact h
  rw [this]
  exact id_left x

/-- Conversely, a faithful vertical transmission has identity tradition. -/
lemma tradition_ident_of_transmitVertical_faithful
    {l : Lineage α} (h : Faithful (fun x : α => transmitVertical l x)) :
    tradition l = ident := by
  -- evaluate faithfulness at `ident`
  have h0 := h (ident : α)
  -- h0 : transmitVertical l ident = ident
  unfold tradition
  rw [← transmitVertical_at_ident]
  exact h0

/-- Faithful vertical transmission is exactly identity-tradition. -/
lemma transmitVertical_faithful_iff (l : Lineage α) :
    Faithful (fun x : α => transmitVertical l x) ↔ tradition l = ident := by
  refine ⟨tradition_ident_of_transmitVertical_faithful,
          transmitVertical_faithful_of_tradition_ident⟩

/-- A lineage of silent generations has identity tradition. -/
lemma tradition_trivial (n : Nat) :
    tradition (Lineage.trivial α n) = ident := by
  unfold tradition Lineage.trivial
  exact aggregate_trivial n

/-- Concatenating a faithful lineage on the right does not change a
    vertical transmission. -/
lemma transmitVertical_append_faithful_right (l₁ l₂ : Lineage α)
    (h : Faithful (fun x : α => transmitVertical l₂ x)) (x : α) :
    transmitVertical (l₁ ++ l₂) x = transmitVertical l₁ x := by
  rw [transmitVertical_append]
  have hx : transmitVertical l₂ x = x := h x
  rw [hx]

/-- Concatenating a faithful lineage on the left does not change a
    vertical transmission. -/
lemma transmitVertical_append_faithful_left (l₁ l₂ : Lineage α)
    (h : Faithful (fun x : α => transmitVertical l₁ x)) (x : α) :
    transmitVertical (l₁ ++ l₂) x = transmitVertical l₂ x := by
  rw [transmitVertical_append]
  exact h (transmitVertical l₂ x)

/-- An "all-silent" lineage's vertical transmission is faithful. -/
lemma transmitVertical_all_silent_faithful {l : Lineage α}
    (h : Coalition.AllSilent l) :
    Faithful (fun x : α => transmitVertical l x) := by
  apply transmitVertical_faithful_of_tradition_ident
  unfold tradition
  exact aggregate_of_all_silent l h

end Faithful

/-! ## §11.4 Lineage equivalence and Sperber variants -/

section LineageEquivSection

/-- `LineageEquiv` is reflexive. -/
lemma LineageEquiv.refl (l : Lineage α) : LineageEquiv l l := by
  intro x; rfl

/-- `LineageEquiv` is symmetric. -/
lemma LineageEquiv.symm {l₁ l₂ : Lineage α}
    (h : LineageEquiv l₁ l₂) : LineageEquiv l₂ l₁ := by
  intro x; exact (h x).symm

/-- `LineageEquiv` is transitive. -/
lemma LineageEquiv.trans {l₁ l₂ l₃ : Lineage α}
    (h₁ : LineageEquiv l₁ l₂) (h₂ : LineageEquiv l₂ l₃) :
    LineageEquiv l₁ l₃ := by
  intro x
  exact Eq.trans (h₁ x) (h₂ x)

/-- Two lineages with equal traditions are culturally equivalent. -/
lemma LineageEquiv.of_tradition_eq {l₁ l₂ : Lineage α}
    (h : tradition l₁ = tradition l₂) : LineageEquiv l₁ l₂ := by
  intro x
  rw [transmitVertical_eq_op_aggregate, transmitVertical_eq_op_aggregate]
  -- aggregate = tradition
  have h' : aggregate l₁ = aggregate l₂ := h
  rw [h']

/-- Two culturally equivalent lineages have equal traditions. -/
lemma tradition_eq_of_LineageEquiv {l₁ l₂ : Lineage α}
    (h : LineageEquiv l₁ l₂) : tradition l₁ = tradition l₂ := by
  have h0 := h (ident : α)
  -- transmitVertical l_i ident = aggregate l_i
  rw [transmitVertical_at_ident, transmitVertical_at_ident] at h0
  unfold tradition
  exact h0

/-- Cultural equivalence iff equal tradition. -/
lemma LineageEquiv_iff_tradition_eq (l₁ l₂ : Lineage α) :
    LineageEquiv l₁ l₂ ↔ tradition l₁ = tradition l₂ := by
  refine ⟨tradition_eq_of_LineageEquiv, LineageEquiv.of_tradition_eq⟩

/-- Cultural equivalence is preserved by `then` on the right. -/
lemma LineageEquiv.then_right {l₁ l₂ : Lineage α}
    (h : LineageEquiv l₁ l₂) (l₃ : Lineage α) :
    LineageEquiv (Lineage.then l₁ l₃) (Lineage.then l₂ l₃) := by
  apply LineageEquiv.of_tradition_eq
  rw [tradition_then, tradition_then]
  rw [tradition_eq_of_LineageEquiv h]

/-- Cultural equivalence is preserved by `then` on the left. -/
lemma LineageEquiv.then_left (l₁ : Lineage α) {l₂ l₃ : Lineage α}
    (h : LineageEquiv l₂ l₃) :
    LineageEquiv (Lineage.then l₁ l₂) (Lineage.then l₁ l₃) := by
  apply LineageEquiv.of_tradition_eq
  rw [tradition_then, tradition_then]
  rw [tradition_eq_of_LineageEquiv h]

/-- Cultural equivalence is preserved by simultaneous `then`. -/
lemma LineageEquiv.then {l₁ l₂ m₁ m₂ : Lineage α}
    (h₁ : LineageEquiv l₁ l₂) (h₂ : LineageEquiv m₁ m₂) :
    LineageEquiv (Lineage.then l₁ m₁) (Lineage.then l₂ m₂) := by
  apply LineageEquiv.of_tradition_eq
  rw [tradition_then, tradition_then]
  rw [tradition_eq_of_LineageEquiv h₁, tradition_eq_of_LineageEquiv h₂]

/-- Cultural equivalence is preserved by inserting silent generations. -/
lemma LineageEquiv.insert_silent (n : Nat) (l : Lineage α) :
    LineageEquiv l (Coalition.insertAt (ident : α) n l) := by
  apply LineageEquiv.of_tradition_eq
  unfold tradition
  exact (aggregate_insert_ident n l).symm

/-- Cultural equivalence: a trivial lineage is equivalent to the empty
    lineage. -/
lemma LineageEquiv.trivial_nil (n : Nat) :
    LineageEquiv (Lineage.trivial α n) ([] : Lineage α) := by
  apply LineageEquiv.of_tradition_eq
  rw [tradition_trivial]
  unfold tradition
  rw [aggregate_nil]

/-- Faithful lineages are exactly those equivalent to the empty
    lineage. -/
lemma LineageEquiv_nil_iff_faithful (l : Lineage α) :
    LineageEquiv l ([] : Lineage α) ↔
      Faithful (fun x : α => transmitVertical l x) := by
  rw [LineageEquiv_iff_tradition_eq]
  unfold tradition
  rw [aggregate_nil]
  -- now: aggregate l = ident ↔ Faithful (...)
  refine ⟨?_, ?_⟩
  · intro h
    apply transmitVertical_faithful_of_tradition_ident
    unfold tradition
    exact h
  · intro h
    have := tradition_ident_of_transmitVertical_faithful h
    unfold tradition at this
    exact this

end LineageEquivSection

/-! ## §11.5 `theorem_11_1` — Vertical-Transmission Composition Law -/

/-- **Theorem 11.1 (Vertical-Transmission Composition Law).**

    *Informal claim.*  The IDT manuscript, Volume VI Chapter 1, asserts
    the *Cultural-Transmission Composition Law*: "the vertical
    transmission along a lineage formed by appending two lineages is
    the composition of the two individual vertical transmissions, and
    this composition is associative".  This is the temporal rereading
    of the Volume 1 associativity theorem in the form it takes in
    cultural-evolution models (Cavalli-Sforza/Feldman 1981 §1.2,
    Boyd/Richerson 1985 §3.3).

    *Sources.*  Cavalli-Sforza/Feldman 1981, Ch. 1 §1.2; Boyd/Richerson
    1985, §3.3 ("composition of vertical transmissions"); Sperber 1996,
    Ch. 4 ("transmission chains"); IDT manuscript Vol. VI §1.2.

    *Lemmas used.*  `transmitVertical_append`, `transmitVertical_then`,
    `transmitVertical_eq_op_aggregate`, `tradition_then`,
    `composeTrans_assoc`.

    *Sharpening.*  The informal version states the composition law in
    pointwise form; the present statement gives both the pointwise law
    and the *strong* form that the entire vertical-transmission map of
    a `then`-lineage equals the function composition of the two
    component vertical-transmission maps.  In addition the theorem
    packages the *associativity* of three-fold transmission, which is
    only implicit in the informal sources.

    *Proof strategy.*
    1. The pointwise composition law is `transmitVertical_then`.
    2. The functional composition law follows by `funext`.
    3. The associativity of three-fold transmission follows from
       `composeTrans_assoc` together with the pointwise version.
    4. Bundle the three statements via `⟨_, _, _⟩`. -/
theorem theorem_11_1 (l₁ l₂ l₃ : Lineage α) :
    (∀ x : α,
      transmitVertical (Lineage.then l₁ l₂) x
        = transmitVertical l₁ (transmitVertical l₂ x)) ∧
    ((fun x : α => transmitVertical (Lineage.then l₁ l₂) x)
        = composeTrans (fun x : α => transmitVertical l₁ x)
                       (fun x : α => transmitVertical l₂ x)) ∧
    (∀ x : α,
      transmitVertical (Lineage.then (Lineage.then l₁ l₂) l₃) x
        = transmitVertical (Lineage.then l₁ (Lineage.then l₂ l₃)) x) := by
  refine ⟨?_, ?_, ?_⟩
  · -- pointwise composition
    intro x
    exact transmitVertical_then l₁ l₂ x
  · -- functional composition
    exact transmitVertical_then_compose l₁ l₂
  · -- associativity of three-fold
    intro x
    -- both sides are vertical transmission along l₁ ++ l₂ ++ l₃ up
    -- to the choice of association in the underlying append.
    have hL : transmitVertical (Lineage.then (Lineage.then l₁ l₂) l₃) x
              = transmitVertical (Lineage.then l₁ l₂) (transmitVertical l₃ x) :=
      transmitVertical_then (Lineage.then l₁ l₂) l₃ x
    have hLL : transmitVertical (Lineage.then l₁ l₂) (transmitVertical l₃ x)
              = transmitVertical l₁ (transmitVertical l₂ (transmitVertical l₃ x)) :=
      transmitVertical_then l₁ l₂ (transmitVertical l₃ x)
    have hR : transmitVertical (Lineage.then l₁ (Lineage.then l₂ l₃)) x
              = transmitVertical l₁ (transmitVertical (Lineage.then l₂ l₃) x) :=
      transmitVertical_then l₁ (Lineage.then l₂ l₃) x
    have hRR : transmitVertical (Lineage.then l₂ l₃) x
              = transmitVertical l₂ (transmitVertical l₃ x) :=
      transmitVertical_then l₂ l₃ x
    -- combine
    rw [hL, hLL, hR, hRR]

/-! ## §11.6 `theorem_11_2` — Faithfulness Characterization -/

/-- **Theorem 11.2 (Faithfulness Characterization).**

    *Informal claim.*  The IDT manuscript, Volume VI §1.3, asserts
    that "a lineage transmits faithfully iff its tradition is the
    identity element, equivalently iff every cultural innovation
    introduced by some generation is exactly cancelled by another
    generation's contribution".  In Henrich 2015 §10 this is cast
    as: "perfectly faithful transmission is the special case in
    which the receiver adds nothing of their own".

    *Sources.*  Henrich 2015, §10; Sperber 1996, Ch. 4 ("variant
    invariance"); IDT manuscript Vol. VI §1.3.

    *Lemmas used.*  `transmitVertical_faithful_of_tradition_ident`,
    `tradition_ident_of_transmitVertical_faithful`,
    `transmitVertical_trivial_faithful`,
    `transmitVertical_all_silent_faithful`,
    `tradition_trivial`.

    *Sharpening.*  The informal version states only the equivalence
    "faithful ↔ tradition = ident".  The present formal statement
    additionally records: (i) the trivial lineage is always faithful;
    (ii) every all-silent lineage is faithful; (iii) the identity
    transmission is itself faithful.  Together these four facts give
    a complete picture of the faithfulness predicate within Volume 6.

    *Proof strategy.*
    1. Use `transmitVertical_faithful_iff` for the central biconditional.
    2. Use `transmitVertical_trivial_faithful` for the trivial case.
    3. Use `transmitVertical_all_silent_faithful` for the silent case.
    4. Use `idTrans_faithful` for the identity case.
    5. Bundle into a 4-tuple. -/
theorem theorem_11_2 :
    (∀ l : Lineage α,
      Faithful (fun x : α => transmitVertical l x) ↔ tradition l = ident) ∧
    (∀ n : Nat,
      Faithful (fun x : α => transmitVertical (Lineage.trivial α n) x)) ∧
    (∀ l : Lineage α,
      Coalition.AllSilent l →
        Faithful (fun x : α => transmitVertical l x)) ∧
    Faithful (idTrans α) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro l
    exact transmitVertical_faithful_iff l
  · intro n
    exact transmitVertical_trivial_faithful n
  · intro l h
    exact transmitVertical_all_silent_faithful h
  · exact idTrans_faithful

/-! ## §11.7 `theorem_11_3` — Cultural-Equivalence Congruence -/

/-- **Theorem 11.3 (Cultural-Equivalence Congruence).**

    *Informal claim.*  Sperber 1996 Ch. 4 and the IDT manuscript
    Vol. VI §1.4 jointly assert that "cultural equivalence of
    lineages is an equivalence relation that is preserved under
    every lineage operation considered in this chapter, and reduces
    in the end to equality of traditions".  This is the temporal
    counterpart of the social-congruence theorem of Volume 5.

    *Sources.*  Sperber 1996, Ch. 4; Boyd/Richerson 1985 §3.3
    ("variant equivalence"); IDT manuscript Vol. VI §1.4.

    *Lemmas used.*  `LineageEquiv.refl`, `LineageEquiv.symm`,
    `LineageEquiv.trans`, `LineageEquiv.then`,
    `LineageEquiv.then_left`, `LineageEquiv.then_right`,
    `LineageEquiv.insert_silent`,
    `LineageEquiv_iff_tradition_eq`.

    *Sharpening.*  The informal version mentions only that cultural
    equivalence is an equivalence relation.  The formal statement
    packages **eight** independent facts, including the silent-
    insertion congruence move and the tradition-equality
    characterisation.

    *Proof strategy.*
    1. Each of the eight conjuncts is handled by the corresponding
       lemma proved in §11.4.
    2. They are bundled into an 8-tuple by `refine`. -/
theorem theorem_11_3 :
    (∀ l : Lineage α, LineageEquiv l l) ∧
    (∀ l₁ l₂ : Lineage α, LineageEquiv l₁ l₂ → LineageEquiv l₂ l₁) ∧
    (∀ l₁ l₂ l₃ : Lineage α,
      LineageEquiv l₁ l₂ → LineageEquiv l₂ l₃ → LineageEquiv l₁ l₃) ∧
    (∀ l₁ l₂ m₁ m₂ : Lineage α,
      LineageEquiv l₁ l₂ → LineageEquiv m₁ m₂ →
      LineageEquiv (Lineage.then l₁ m₁) (Lineage.then l₂ m₂)) ∧
    (∀ l₁ : Lineage α, ∀ l₂ l₃ : Lineage α,
      LineageEquiv l₂ l₃ →
      LineageEquiv (Lineage.then l₁ l₂) (Lineage.then l₁ l₃)) ∧
    (∀ l₃ : Lineage α, ∀ l₁ l₂ : Lineage α,
      LineageEquiv l₁ l₂ →
      LineageEquiv (Lineage.then l₁ l₃) (Lineage.then l₂ l₃)) ∧
    (∀ n : Nat, ∀ l : Lineage α,
      LineageEquiv l (Coalition.insertAt (ident : α) n l)) ∧
    (∀ l₁ l₂ : Lineage α,
      LineageEquiv l₁ l₂ ↔ tradition l₁ = tradition l₂) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro l; exact LineageEquiv.refl l
  · intro l₁ l₂ h; exact LineageEquiv.symm h
  · intro l₁ l₂ l₃ h₁ h₂; exact LineageEquiv.trans h₁ h₂
  · intro l₁ l₂ m₁ m₂ h₁ h₂; exact LineageEquiv.then h₁ h₂
  · intro l₁ l₂ l₃ h; exact LineageEquiv.then_left l₁ h
  · intro l₃ l₁ l₂ h; exact LineageEquiv.then_right h l₃
  · intro n l; exact LineageEquiv.insert_silent n l
  · intro l₁ l₂; exact LineageEquiv_iff_tradition_eq l₁ l₂

/-! ## §11.8 Corollaries -/

/-- **Corollary 11.1 (Lineage-tradition decomposition).**
    The tradition of the concatenation of two lineages is the `op`
    of the two traditions.  This is the form most often quoted in
    cultural-evolution writings (Cavalli-Sforza/Feldman 1981 §1.2). -/
theorem corollary_11_1 (l₁ l₂ : Lineage α) :
    tradition (Lineage.then l₁ l₂) = op (tradition l₁) (tradition l₂) :=
  tradition_then l₁ l₂

/-- **Corollary 11.2 (Silent generation invariance).**
    Inserting a silent generation into a lineage at any position
    yields a culturally equivalent lineage.  This is the IDT
    manuscript's Vol. VI §1.4 statement that "culturally invisible
    generations are congruence moves". -/
theorem corollary_11_2 (n : Nat) (l : Lineage α) :
    LineageEquiv l (Coalition.insertAt (ident : α) n l) :=
  LineageEquiv.insert_silent n l

/-- **Corollary 11.3 (Faithful-lineage characterization).**
    A lineage is culturally equivalent to the empty lineage iff its
    vertical transmission is faithful.  This formalises Henrich
    2015 §10's "perfectly faithful transmission". -/
theorem corollary_11_3 (l : Lineage α) :
    LineageEquiv l ([] : Lineage α) ↔
      Faithful (fun x : α => transmitVertical l x) :=
  LineageEquiv_nil_iff_faithful l

/-- **Corollary 11.4 (Vertical = leftMul of tradition).**
    Every vertical transmission is left-multiplication by its
    tradition.  This is the formal version of the slogan "a
    lineage's effect on cultural material is precisely the
    application of its accumulated tradition" (IDT Vol. VI §1.5). -/
theorem corollary_11_4 (l : Lineage α) :
    (fun x : α => transmitVertical l x) = leftMul (tradition l) :=
  transmitVertical_eq_leftMul l

/-- **Corollary 11.5 (Trivial-lineage collapse).**
    A trivial lineage of any length is culturally equivalent to the
    empty lineage; in particular, a "long history of silent
    generations" leaves no cultural trace.  Cf. Sperber 1996 Ch. 4. -/
theorem corollary_11_5 (n : Nat) :
    LineageEquiv (Lineage.trivial α n) ([] : Lineage α) :=
  LineageEquiv.trivial_nil n

/-! ## §11.9 Examples and sanity checks -/

/-- Example: the empty lineage transmits everything unchanged. -/
example (x : α) : transmitVertical ([] : Lineage α) x = x :=
  transmitVertical_nil x

/-- Example: a singleton lineage `[a]` transmits `x` to `op a x`. -/
example (a x : α) : transmitVertical (Lineage.singleton a) x = op a x :=
  transmitVertical_singleton a x

/-- Example: vertical transmission factors through the tradition. -/
example (l : Lineage α) (x : α) :
    transmitVertical l x = op (tradition l) x := by
  unfold tradition
  exact transmitVertical_eq_op_aggregate l x

/-- Example: vertical transmission along a `then` is composition. -/
example (l₁ l₂ : Lineage α) (x : α) :
    transmitVertical (Lineage.then l₁ l₂) x
      = transmitVertical l₁ (transmitVertical l₂ x) := by
  exact (theorem_11_1 l₁ l₂ ([] : Lineage α)).1 x

/-- Example: a 5-fold trivial lineage is faithful. -/
example : Faithful (fun x : α => transmitVertical (Lineage.trivial α 5) x) :=
  (theorem_11_2 (α := α)).2.1 5

/-- Example: lineage equivalence reduces to tradition equality. -/
example (l₁ l₂ : Lineage α) :
    LineageEquiv l₁ l₂ ↔ tradition l₁ = tradition l₂ :=
  (theorem_11_3 (α := α)).2.2.2.2.2.2.2 l₁ l₂

/-- Example: inserting a silent generation at position 3 yields a
    culturally equivalent lineage. -/
example (l : Lineage α) :
    LineageEquiv l (Coalition.insertAt (ident : α) 3 l) :=
  corollary_11_2 3 l

/-- Example: the tradition of `then l₁ l₂` decomposes additively. -/
example (l₁ l₂ : Lineage α) :
    tradition (Lineage.then l₁ l₂) = op (tradition l₁) (tradition l₂) :=
  corollary_11_1 l₁ l₂

/-! ## Index of results

Public declarations in this file (Volume 6, "Cultural Transmission"):

* §11.0 auxiliary definitions
  - `Transmission`                                  : abbrev for `α → α`.
  - `idTrans`                                       : identity transmission.
  - `composeTrans`                                  : composition of transmissions.
  - `leftMul`, `rightMul`                           : single-generation transmissions.
  - `Lineage`                                       : abbrev for `Coalition α`.
  - `transmitVertical`                              : vertical transmission map.
  - `transmitHorizontal`                            : horizontal transmission map.
  - `Generation`                                    : bundled generation/contribution/rule.
  - `tradition`                                     : aggregate of a lineage.
  - `Faithful`                                      : faithful-transmission predicate.
  - `LineageEquiv`                                  : cultural equivalence.
  - `Variant`                                       : a Sperber variant subtype.
  - `Lineage.trivial`, `Lineage.singleton`,
    `Lineage.then`                                  : lineage constructors.

* §11.1 closure
  - `idTrans_apply`, `composeTrans_apply`,
  - `idTrans_compose_left`, `idTrans_compose_right`,
  - `composeTrans_assoc`,
  - `leftMul_apply`, `rightMul_apply`,
  - `leftMul_ident`, `rightMul_ident`,
  - `leftMul_compose`, `rightMul_compose`,
  - `transmitVertical_nil/cons/singleton`,
  - `transmitHorizontal_nil/cons/singleton`.

* §11.2 vertical transmission and aggregate link
  - `transmitVertical_at_ident`,
  - `tradition_eq_transmit_at_ident`,
  - `transmitVertical_eq_op_aggregate`,
  - `transmitVertical_append`,
  - `transmitVertical_then`,
  - `transmitVertical_eq_leftMul`,
  - `transmitVertical_singleton_at_ident`,
  - `tradition_then`,
  - `transmitVertical_then_compose`,
  - `transmitVertical_trivial`.

* §11.3 faithful transmission
  - `idTrans_faithful`,
  - `leftMul_ident_faithful`, `rightMul_ident_faithful`,
  - `composeTrans_faithful`,
  - `transmitVertical_nil_faithful`,
  - `transmitVertical_trivial_faithful`,
  - `transmitVertical_faithful_of_tradition_ident`,
  - `tradition_ident_of_transmitVertical_faithful`,
  - `transmitVertical_faithful_iff`,
  - `tradition_trivial`,
  - `transmitVertical_append_faithful_right/left`,
  - `transmitVertical_all_silent_faithful`.

* §11.4 lineage equivalence
  - `LineageEquiv.refl/symm/trans`,
  - `LineageEquiv.of_tradition_eq`,
  - `tradition_eq_of_LineageEquiv`,
  - `LineageEquiv_iff_tradition_eq`,
  - `LineageEquiv.then_right/then_left/then`,
  - `LineageEquiv.insert_silent`,
  - `LineageEquiv.trivial_nil`,
  - `LineageEquiv_nil_iff_faithful`.

* §11.5 `theorem_11_1` : Vertical-Transmission Composition Law.
* §11.6 `theorem_11_2` : Faithfulness Characterization.
* §11.7 `theorem_11_3` : Cultural-Equivalence Congruence.

* §11.8 corollaries
  - `corollary_11_1` : lineage-tradition decomposition.
  - `corollary_11_2` : silent-generation invariance.
  - `corollary_11_3` : faithful-lineage characterization.
  - `corollary_11_4` : vertical = leftMul of tradition.
  - `corollary_11_5` : trivial-lineage collapse.

* §11.9 examples (sanity checks).
-/

end IdeaTheory
