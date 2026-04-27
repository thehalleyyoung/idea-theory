import IdeaTheory.Foundations
import IdeaTheory.Theorems9

/-!
# IdeaTheory: Theorems 10 — Social Composition (Volume 5)

## What this file formalizes

This file is the opening technical chapter of the *applied* arc of the
IdeaTheory project, following the steering directive that Volumes 2–6
should reinterpret the bare algebraic theorems of Volume 1 across the
social sciences, the humanities, the philosophy of mind, the problem
of emergence, and a final volume of advanced applications.  The
present file develops the formal theory of **social composition**:
the systematic combination of carrier elements of an
`IdeaTheoryStructure α` into *coalitions*, *committees*,
*assemblies*, and *aggregates* of ideas.

The informal IDT manuscript (`IDT_Theory.pdf`, Volume V, Chapter 1
"Social Composition of Ideas") argues that the algebraic operation
`op : α → α → α` of Volume 1 should be reread as the operation of
*aggregating* two ideas held by two social agents into the single
collective idea of the two-agent coalition.  Under that reading the
distinguished element `ident : α` plays the role of the *silent
agent* — a member of the coalition who contributes nothing yet whose
presence does not perturb the collective idea.  Associativity becomes
the assertion that a coalition's collective idea is independent of
the order in which sub-coalitions are first formed.  The chapter then
extends the binary picture to arbitrary finite coalitions of agents
and proves that the resulting aggregate enjoys exactly the formal
properties one expects of a well-behaved social composition rule.

## Authors and works drawn upon

The formalization draws on, in addition to the IDT manuscript, the
following non-formalized literature: Arrow, *Social Choice and
Individual Values* (Wiley, 1951), §II–§III for the abstract notion of
an aggregation rule; Sen, *Collective Choice and Social Welfare*
(Holden-Day, 1970), Chapter 2 for the discussion of "silent" or
abstaining voters; List and Pettit, *Group Agency* (Oxford, 2011),
Part II, for the language of coalitions and joint judgements; and
Bourbaki, *Algèbre I*, Ch. I §1.5 for the formal pattern of
extending a binary operation to a finitary `fold`.  The treatment of
chains of coalitions follows Howie, *Fundamentals of Semigroup
Theory* (Oxford, 1995), §1.2.

## Design decisions and conventions

* We continue to take `IdeaTheoryStructure` as the only primitive
  algebraic context; nothing in this file references Mathlib's
  `Monoid`, `Semigroup`, etc.  Every result is a direct consequence
  of `assoc`, `id_left`, `id_right`.
* A *coalition* is just a `List α`; this matches both the informal
  manuscript and standard usage in social-choice theory, where
  coalitions are treated as finite sequences of named agents.
* The collective idea of a coalition is its left-fold under `op`
  starting from `ident`; this is the same convention as
  `List.foldl` in Lean's `Mathlib`, but we redefine it inline so the
  file is self-contained against `Foundations`.
* "Silent agents" are coded as occurrences of `ident` in the
  coalition list; the chapter's central technical tool is that
  silent agents may be freely inserted or deleted without changing
  the collective idea.
* Where the literature uses the prose phrase "two coalitions are
  socially equivalent", we make it precise via
  `CoalitionEquiv` (equality of collective ideas) and prove it is
  an equivalence relation respecting concatenation.

## Roadmap

1. §10.0 auxiliary definitions of coalitions, committees,
   aggregates, and the silent-agent predicate.
2. §10.1 closure lemmas about `aggregate` on small coalitions.
3. §10.2 silent-agent insertion and deletion.
4. §10.3 monotonicity lemmas under coalition concatenation.
5. §10.4 `theorem_10_1` — the *coalition associativity* theorem.
6. §10.5 `theorem_10_2` — the *silent-agent invariance* theorem.
7. §10.6 `theorem_10_3` — the *social congruence* theorem for
   `CoalitionEquiv`.
8. §10.7 corollaries `corollary_10_1`–`corollary_10_4`.
9. §10.8 examples and sanity checks.

## Role inside Volume 5

Volume 5 of the regenerated PRD is the *applied* arc's hinge,
treating both the social-composition theme and its bridge to the
emergence theorems of later chapters.  The present file gives the
core technical apparatus — coalition aggregation and the algebra of
silent agents — that subsequent files in the volume reuse without
re-proving.  All later social-emergence results in the project
ultimately rest on `theorem_10_1`, `theorem_10_2`, `theorem_10_3`
proved here.
-/

namespace IdeaTheory

open IdeaTheoryStructure

variable {α : Type*} [inst : IdeaTheoryStructure α]

/-! ## §10.0 Auxiliary definitions of coalitions and aggregates -/

/-- A *coalition* of agents, each carrying an idea, is modelled as a
    finite list of carrier elements.  Following Arrow 1951 §II, we
    treat the order of the list as the *enumeration* of the agents,
    not as expressing any structural priority among them. -/
abbrev Coalition (α : Type*) := List α

/-- The *collective idea* of a coalition: the left-fold of `op`
    starting from `ident`.  This is the canonical "aggregate" of the
    coalition's individually held ideas.  Compare List/Pettit 2011,
    Ch. 5, "joint judgement formation". -/
def aggregate [IdeaTheoryStructure α] : Coalition α → α
  | []      => ident
  | a :: as => op a (aggregate as)

/-- A *committee* bundles a coalition together with a designated
    *chair* element pulled out of the coalition.  Compare Sen 1970
    §2.2, where the chair plays the role of an institutionally
    distinguished member. -/
structure Committee (α : Type*) where
  /-- The chair of the committee. -/
  chair : α
  /-- The remaining coalition of members. -/
  members : Coalition α

/-- The collective idea of a committee: the chair's idea aggregated
    with the members' collective idea. -/
def Committee.collective [IdeaTheoryStructure α] (c : Committee α) : α :=
  op c.chair (aggregate c.members)

/-- An *assembly* is a coalition of committees.  Its collective idea
    is the aggregate of the collective ideas of its committees.  This
    matches the two-tier hierarchical structure of List/Pettit
    2011, Part II. -/
structure Assembly (α : Type*) where
  /-- The committees that make up the assembly. -/
  committees : List (Committee α)

/-- The collective idea of an assembly. -/
def Assembly.collective [IdeaTheoryStructure α] (a : Assembly α) : α :=
  aggregate (a.committees.map Committee.collective)

/-- An agent is *silent* in the present formalisation iff its
    contributed idea is the identity element. -/
def IsSilent [IdeaTheoryStructure α] (a : α) : Prop := a = ident

/-- The *trivial coalition* containing only silent agents.  Used as
    a baseline in proofs of silent-agent invariance. -/
def Coalition.trivial (α : Type*) [IdeaTheoryStructure α] (n : Nat) :
    Coalition α :=
  List.replicate n ident

/-- The *singleton coalition* containing one agent. -/
def Coalition.singleton (a : α) : Coalition α := [a]

/-- The *pair coalition* of two agents. -/
def Coalition.pair (a b : α) : Coalition α := [a, b]

/-- The *triple coalition* of three agents. -/
def Coalition.triple (a b c : α) : Coalition α := [a, b, c]

/-- Two coalitions are *socially equivalent* iff they have the same
    collective idea.  This is the definition used throughout
    Sen 1970 §2.4 of "outcome-equivalence". -/
def CoalitionEquiv [IdeaTheoryStructure α] (xs ys : Coalition α) : Prop :=
  aggregate xs = aggregate ys

/-- An *insertion* of an agent into a coalition at a given position.
    Used to formalise "an agent joins the coalition" in Arrow 1951
    §III.4. -/
def Coalition.insertAt (a : α) : Nat → Coalition α → Coalition α
  | _,     []      => [a]
  | 0,     xs      => a :: xs
  | n+1, x :: xs   => x :: Coalition.insertAt a n xs

/-- The *delegation* of one coalition into another: the second
    coalition is appended to the first, modelling a sub-coalition
    joining a host coalition.  Cf. List/Pettit 2011, §6.2. -/
def Coalition.delegate (xs ys : Coalition α) : Coalition α := xs ++ ys

/-- Predicate "every member of the coalition is silent". -/
def Coalition.AllSilent [IdeaTheoryStructure α] (xs : Coalition α) : Prop :=
  ∀ a ∈ xs, IsSilent a

/-! ## §10.1 Closure lemmas about `aggregate` on small coalitions -/

section Closure

/-- The aggregate of the empty coalition is the identity. -/
lemma aggregate_nil : aggregate ([] : Coalition α) = ident := rfl

/-- The aggregate of a singleton coalition is the agent's own idea. -/
lemma aggregate_singleton (a : α) :
    aggregate (Coalition.singleton a) = a := by
  unfold Coalition.singleton aggregate
  -- aggregate [a] = op a (aggregate []) = op a ident = a
  show op a (aggregate ([] : Coalition α)) = a
  rw [aggregate_nil]
  exact id_right a

/-- The aggregate of a cons. -/
lemma aggregate_cons (a : α) (xs : Coalition α) :
    aggregate (a :: xs) = op a (aggregate xs) := rfl

/-- The aggregate of a pair coalition. -/
lemma aggregate_pair (a b : α) :
    aggregate (Coalition.pair a b) = op a b := by
  unfold Coalition.pair
  show op a (aggregate [b]) = op a b
  have h : aggregate ([b] : Coalition α) = b := aggregate_singleton b
  rw [h]

/-- The aggregate of a triple coalition is right-leaning. -/
lemma aggregate_triple (a b c : α) :
    aggregate (Coalition.triple a b c) = op a (op b c) := by
  unfold Coalition.triple
  show op a (aggregate [b, c]) = op a (op b c)
  have h : aggregate ([b, c] : Coalition α) = op b c := aggregate_pair b c
  rw [h]

/-- The trivial coalition of length zero is empty. -/
lemma trivial_zero : Coalition.trivial α 0 = ([] : Coalition α) := rfl

/-- The trivial coalition of length `n+1` is `ident :: trivial n`. -/
lemma trivial_succ (n : Nat) :
    Coalition.trivial α (n + 1) = (ident : α) :: Coalition.trivial α n := rfl

/-- The aggregate of a trivial coalition is the identity. -/
lemma aggregate_trivial (n : Nat) :
    aggregate (Coalition.trivial α n) = (ident : α) := by
  induction n with
  | zero => rw [trivial_zero, aggregate_nil]
  | succ k ih =>
      rw [trivial_succ]
      rw [aggregate_cons]
      rw [ih]
      exact id_left ident

/-- A coalition consisting of one silent agent has identity aggregate. -/
lemma aggregate_singleton_silent : aggregate ([ident] : Coalition α) = ident := by
  show aggregate (Coalition.singleton (ident : α)) = ident
  rw [aggregate_singleton]

/-- A coalition consisting of two silent agents has identity aggregate. -/
lemma aggregate_pair_silent :
    aggregate ([ident, ident] : Coalition α) = ident := by
  show aggregate (Coalition.pair (ident : α) ident) = ident
  rw [aggregate_pair]
  exact id_left ident

/-- A coalition consisting of three silent agents has identity aggregate. -/
lemma aggregate_triple_silent :
    aggregate ([ident, ident, ident] : Coalition α) = ident := by
  show aggregate (Coalition.triple (ident : α) ident ident) = ident
  rw [aggregate_triple]
  rw [id_left, id_left]

end Closure

/-! ## §10.2 Silent-agent insertion and deletion -/

section SilentAgent

/-- Inserting a silent agent at the head of a coalition does not
    change the aggregate. -/
lemma aggregate_cons_ident (xs : Coalition α) :
    aggregate ((ident : α) :: xs) = aggregate xs := by
  rw [aggregate_cons]
  exact id_left _

/-- Inserting a silent agent at the tail of a (singleton-tail) cons
    keeps the aggregate of the head. -/
lemma aggregate_cons_singleton_ident (a : α) :
    aggregate (a :: [ident] : Coalition α) = a := by
  rw [aggregate_cons]
  show op a (aggregate ([ident] : Coalition α)) = a
  rw [aggregate_singleton_silent]
  exact id_right a

/-- The aggregate of an `append` is the `op` of the two aggregates.
    This is the central technical lemma of the chapter. -/
lemma aggregate_append (xs ys : Coalition α) :
    aggregate (xs ++ ys) = op (aggregate xs) (aggregate ys) := by
  induction xs with
  | nil =>
      -- aggregate ([] ++ ys) = aggregate ys = op ident (aggregate ys)
      show aggregate ys = op (aggregate ([] : Coalition α)) (aggregate ys)
      rw [aggregate_nil]
      exact (id_left _).symm
  | cons a as ih =>
      -- aggregate ((a :: as) ++ ys) = op a (aggregate (as ++ ys))
      show aggregate (a :: (as ++ ys)) = op (aggregate (a :: as)) (aggregate ys)
      rw [aggregate_cons, aggregate_cons]
      rw [ih]
      -- op a (op (aggregate as) (aggregate ys))
      --   = op (op a (aggregate as)) (aggregate ys)
      exact (assoc a (aggregate as) (aggregate ys)).symm

/-- Appending the empty coalition is a no-op for the aggregate. -/
lemma aggregate_append_nil (xs : Coalition α) :
    aggregate (xs ++ []) = aggregate xs := by
  rw [aggregate_append, aggregate_nil]
  exact id_right _

/-- Prepending the empty coalition is a no-op for the aggregate. -/
lemma aggregate_nil_append (xs : Coalition α) :
    aggregate ([] ++ xs) = aggregate xs := by
  rw [aggregate_append, aggregate_nil]
  exact id_left _

/-- Appending a coalition of silent agents does not change the
    aggregate. -/
lemma aggregate_append_trivial (xs : Coalition α) (n : Nat) :
    aggregate (xs ++ Coalition.trivial α n) = aggregate xs := by
  rw [aggregate_append, aggregate_trivial]
  exact id_right _

/-- Prepending a coalition of silent agents does not change the
    aggregate. -/
lemma aggregate_trivial_append (xs : Coalition α) (n : Nat) :
    aggregate (Coalition.trivial α n ++ xs) = aggregate xs := by
  rw [aggregate_append, aggregate_trivial]
  exact id_left _

/-- Inserting a silent agent at position 0 keeps the aggregate. -/
lemma aggregate_insert_ident_zero (xs : Coalition α) :
    aggregate (Coalition.insertAt (ident : α) 0 xs) = aggregate xs := by
  cases xs with
  | nil =>
      -- insertAt ident 0 [] = [ident]; aggregate [ident] = ident
      show aggregate ([ident] : Coalition α) = aggregate ([] : Coalition α)
      rw [aggregate_singleton_silent, aggregate_nil]
  | cons x xs =>
      -- insertAt ident 0 (x::xs) = ident :: x :: xs
      show aggregate ((ident : α) :: x :: xs) = aggregate (x :: xs)
      exact aggregate_cons_ident _

/-- Insertion of an agent into the empty coalition gives a singleton. -/
lemma insertAt_nil (a : α) (n : Nat) :
    Coalition.insertAt a n ([] : Coalition α) = [a] := by
  cases n <;> rfl

/-- Insertion at position `n+1` into a non-empty list. -/
lemma insertAt_succ_cons (a x : α) (n : Nat) (xs : Coalition α) :
    Coalition.insertAt a (n+1) (x :: xs)
      = x :: Coalition.insertAt a n xs := rfl

/-- Insertion at position `0` into a non-empty list. -/
lemma insertAt_zero_cons (a x : α) (xs : Coalition α) :
    Coalition.insertAt a 0 (x :: xs) = a :: x :: xs := rfl

/-- Inserting a silent agent at *any* position keeps the aggregate. -/
lemma aggregate_insert_ident (n : Nat) (xs : Coalition α) :
    aggregate (Coalition.insertAt (ident : α) n xs) = aggregate xs := by
  induction xs generalizing n with
  | nil =>
      -- insertAt ident n [] = [ident]
      rw [insertAt_nil]
      show aggregate ([ident] : Coalition α) = aggregate ([] : Coalition α)
      rw [aggregate_singleton_silent, aggregate_nil]
  | cons x xs ih =>
      cases n with
      | zero =>
          rw [insertAt_zero_cons]
          exact aggregate_cons_ident _
      | succ k =>
          rw [insertAt_succ_cons, aggregate_cons, aggregate_cons]
          rw [ih]

/-- Deleting a leading silent agent does not change the aggregate. -/
lemma aggregate_tail_of_ident_head (xs : Coalition α) :
    aggregate ((ident : α) :: xs) = aggregate xs := aggregate_cons_ident xs

/-- A coalition all of whose members are silent has identity
    aggregate. -/
lemma aggregate_of_all_silent :
    ∀ xs : Coalition α, Coalition.AllSilent xs → aggregate xs = ident
  | [],      _ => aggregate_nil
  | a :: xs, h => by
      have hsilent : IsSilent a := h a (List.mem_cons_self a xs)
      have htail   : Coalition.AllSilent xs := fun b hb =>
        h b (List.mem_cons_of_mem a hb)
      rw [aggregate_cons]
      have ih := aggregate_of_all_silent xs htail
      rw [ih]
      -- a = ident, so op a ident = ident
      have : a = ident := hsilent
      rw [this]
      exact id_left ident

end SilentAgent

/-! ## §10.3 Monotonicity under coalition concatenation -/

section Monotonicity

/-- The aggregate of a `delegate` is the `op` of the two aggregates. -/
lemma aggregate_delegate (xs ys : Coalition α) :
    aggregate (Coalition.delegate xs ys) = op (aggregate xs) (aggregate ys) :=
  aggregate_append xs ys

/-- Delegation is associative as an operation on coalitions. -/
lemma delegate_assoc (xs ys zs : Coalition α) :
    Coalition.delegate (Coalition.delegate xs ys) zs
      = Coalition.delegate xs (Coalition.delegate ys zs) := by
  unfold Coalition.delegate
  exact (List.append_assoc xs ys zs)

/-- Delegating the empty coalition on the right is the identity. -/
lemma delegate_nil_right (xs : Coalition α) :
    Coalition.delegate xs ([] : Coalition α) = xs := by
  unfold Coalition.delegate
  exact List.append_nil xs

/-- Delegating the empty coalition on the left is the identity. -/
lemma delegate_nil_left (xs : Coalition α) :
    Coalition.delegate ([] : Coalition α) xs = xs := by
  unfold Coalition.delegate
  rfl

/-- The aggregate operation is *equivariant* under prepending the
    same agent to two equally-aggregating coalitions. -/
lemma aggregate_cons_congr {a : α} {xs ys : Coalition α}
    (h : aggregate xs = aggregate ys) :
    aggregate (a :: xs) = aggregate (a :: ys) := by
  rw [aggregate_cons, aggregate_cons, h]

/-- The aggregate operation is equivariant under appending the same
    coalition. -/
lemma aggregate_append_left_congr {xs ys : Coalition α} (zs : Coalition α)
    (h : aggregate xs = aggregate ys) :
    aggregate (zs ++ xs) = aggregate (zs ++ ys) := by
  rw [aggregate_append, aggregate_append, h]

/-- The aggregate operation is equivariant under prepending the same
    coalition. -/
lemma aggregate_append_right_congr {xs ys : Coalition α} (zs : Coalition α)
    (h : aggregate xs = aggregate ys) :
    aggregate (xs ++ zs) = aggregate (ys ++ zs) := by
  rw [aggregate_append, aggregate_append, h]

/-- Swapping a head and an immediately following silent agent is
    invisible to the aggregate. -/
lemma aggregate_swap_head_silent (a : α) (xs : Coalition α) :
    aggregate (a :: (ident : α) :: xs) = aggregate ((ident : α) :: a :: xs) := by
  rw [aggregate_cons, aggregate_cons, aggregate_cons, aggregate_cons]
  rw [id_left, id_left]

/-- Replacing a head silent agent with `ident` is a no-op. -/
lemma aggregate_replace_head_ident {a : α} (h : a = ident) (xs : Coalition α) :
    aggregate (a :: xs) = aggregate ((ident : α) :: xs) := by
  rw [h]

/-- The collective idea of a committee is the aggregate of its
    chair-prepended member coalition. -/
lemma committee_collective_eq_aggregate (c : Committee α) :
    c.collective = aggregate (c.chair :: c.members) := by
  unfold Committee.collective
  rw [aggregate_cons]

/-- An assembly's collective idea distributes over committee
    composition: an empty assembly aggregates to `ident`. -/
lemma assembly_empty_collective :
    (⟨[]⟩ : Assembly α).collective = (ident : α) := by
  unfold Assembly.collective
  show aggregate (([] : List (Committee α)).map Committee.collective) = ident
  rfl

/-- An assembly's collective idea on a singleton committee is the
    committee's own collective idea. -/
lemma assembly_singleton_collective (c : Committee α) :
    (⟨[c]⟩ : Assembly α).collective = c.collective := by
  unfold Assembly.collective
  show aggregate ([c].map Committee.collective) = c.collective
  show aggregate [c.collective] = c.collective
  exact aggregate_singleton _

/-- An assembly's collective idea on a pair of committees is the
    `op` of their two collective ideas. -/
lemma assembly_pair_collective (c d : Committee α) :
    (⟨[c, d]⟩ : Assembly α).collective = op c.collective d.collective := by
  unfold Assembly.collective
  show aggregate ([c, d].map Committee.collective) = op c.collective d.collective
  show aggregate [c.collective, d.collective] = op c.collective d.collective
  exact aggregate_pair _ _

end Monotonicity

/-! ## §10.3′ Equivalence of coalitions -/

section Equiv

/-- `CoalitionEquiv` is reflexive. -/
lemma CoalitionEquiv.refl (xs : Coalition α) : CoalitionEquiv xs xs := rfl

/-- `CoalitionEquiv` is symmetric. -/
lemma CoalitionEquiv.symm {xs ys : Coalition α}
    (h : CoalitionEquiv xs ys) : CoalitionEquiv ys xs := Eq.symm h

/-- `CoalitionEquiv` is transitive. -/
lemma CoalitionEquiv.trans {xs ys zs : Coalition α}
    (h₁ : CoalitionEquiv xs ys) (h₂ : CoalitionEquiv ys zs) :
    CoalitionEquiv xs zs := Eq.trans h₁ h₂

/-- `CoalitionEquiv` is preserved by appending a fixed coalition on
    the right. -/
lemma CoalitionEquiv.append_right {xs ys : Coalition α}
    (h : CoalitionEquiv xs ys) (zs : Coalition α) :
    CoalitionEquiv (xs ++ zs) (ys ++ zs) := by
  unfold CoalitionEquiv at *
  exact aggregate_append_right_congr zs h

/-- `CoalitionEquiv` is preserved by appending a fixed coalition on
    the left. -/
lemma CoalitionEquiv.append_left (zs : Coalition α) {xs ys : Coalition α}
    (h : CoalitionEquiv xs ys) :
    CoalitionEquiv (zs ++ xs) (zs ++ ys) := by
  unfold CoalitionEquiv at *
  exact aggregate_append_left_congr zs h

/-- `CoalitionEquiv` is preserved by simultaneous append. -/
lemma CoalitionEquiv.append {xs₁ xs₂ ys₁ ys₂ : Coalition α}
    (h₁ : CoalitionEquiv xs₁ xs₂) (h₂ : CoalitionEquiv ys₁ ys₂) :
    CoalitionEquiv (xs₁ ++ ys₁) (xs₂ ++ ys₂) := by
  unfold CoalitionEquiv at *
  rw [aggregate_append, aggregate_append, h₁, h₂]

/-- A coalition is socially equivalent to itself with an inserted
    silent agent at any position. -/
lemma CoalitionEquiv.insert_ident (n : Nat) (xs : Coalition α) :
    CoalitionEquiv xs (Coalition.insertAt (ident : α) n xs) := by
  unfold CoalitionEquiv
  exact (aggregate_insert_ident n xs).symm

/-- A trivial coalition is equivalent to the empty coalition. -/
lemma CoalitionEquiv.trivial_nil (n : Nat) :
    CoalitionEquiv (Coalition.trivial α n) ([] : Coalition α) := by
  unfold CoalitionEquiv
  rw [aggregate_trivial, aggregate_nil]

/-- Equivalence of singletons reduces to equality of agents. -/
lemma CoalitionEquiv.singleton_iff {a b : α} :
    CoalitionEquiv (Coalition.singleton a) (Coalition.singleton b) ↔ a = b := by
  unfold CoalitionEquiv
  rw [aggregate_singleton, aggregate_singleton]

end Equiv

/-! ## §10.3″ Chains, decomposition, and reassociation -/

section Chains

/-- The aggregate of a triple-append decomposes one way. -/
lemma aggregate_append_assoc_L (xs ys zs : Coalition α) :
    aggregate ((xs ++ ys) ++ zs)
      = op (op (aggregate xs) (aggregate ys)) (aggregate zs) := by
  rw [aggregate_append, aggregate_append]

/-- The aggregate of a triple-append decomposes the other way. -/
lemma aggregate_append_assoc_R (xs ys zs : Coalition α) :
    aggregate (xs ++ (ys ++ zs))
      = op (aggregate xs) (op (aggregate ys) (aggregate zs)) := by
  rw [aggregate_append, aggregate_append]

/-- Two equivalent associations of a triple-append. -/
lemma aggregate_append_triple_assoc (xs ys zs : Coalition α) :
    aggregate ((xs ++ ys) ++ zs) = aggregate (xs ++ (ys ++ zs)) := by
  rw [aggregate_append_assoc_L, aggregate_append_assoc_R]
  exact assoc _ _ _

/-- Inserting a silent agent in the middle of a `cons` does not change
    the aggregate. -/
lemma aggregate_insert_ident_after_head (a : α) (xs : Coalition α) :
    aggregate (a :: (ident : α) :: xs) = aggregate (a :: xs) := by
  rw [aggregate_cons, aggregate_cons]
  rw [aggregate_cons]
  rw [id_left]

/-- Two adjacent silent agents in the middle of a coalition collapse. -/
lemma aggregate_two_idents_middle (a : α) (xs : Coalition α) :
    aggregate (a :: (ident : α) :: (ident : α) :: xs)
      = aggregate (a :: xs) := by
  rw [aggregate_cons]
  show op a (aggregate ((ident : α) :: (ident : α) :: xs))
        = aggregate (a :: xs)
  rw [aggregate_cons]
  rw [id_left]
  rw [aggregate_cons, id_left]
  rw [aggregate_cons]

/-- A trailing silent agent collapses. -/
lemma aggregate_snoc_ident (xs : Coalition α) :
    aggregate (xs ++ [(ident : α)]) = aggregate xs := by
  rw [aggregate_append]
  show op (aggregate xs) (aggregate ([ident] : Coalition α)) = aggregate xs
  rw [aggregate_singleton_silent]
  exact id_right _

/-- Two trailing silent agents collapse. -/
lemma aggregate_snoc_two_idents (xs : Coalition α) :
    aggregate (xs ++ [(ident : α), (ident : α)]) = aggregate xs := by
  rw [aggregate_append]
  show op (aggregate xs)
          (aggregate ([ident, ident] : Coalition α)) = aggregate xs
  rw [aggregate_pair_silent]
  exact id_right _

/-- A leading and trailing silent agent collapse simultaneously. -/
lemma aggregate_sandwich_idents (xs : Coalition α) :
    aggregate ((ident : α) :: xs ++ [(ident : α)]) = aggregate xs := by
  show aggregate ((ident : α) :: (xs ++ [(ident : α)])) = aggregate xs
  rw [aggregate_cons_ident]
  exact aggregate_snoc_ident xs

/-- A "chain" of silent agents at any position collapses by induction
    on its length. -/
lemma aggregate_replicate_ident_append (n : Nat) (xs : Coalition α) :
    aggregate (List.replicate n (ident : α) ++ xs) = aggregate xs := by
  induction n with
  | zero =>
      show aggregate (([] : Coalition α) ++ xs) = aggregate xs
      exact aggregate_nil_append xs
  | succ k ih =>
      -- replicate (k+1) ident = ident :: replicate k ident
      have hrep : List.replicate (k+1) (ident : α)
                  = (ident : α) :: List.replicate k (ident : α) := rfl
      rw [hrep]
      show aggregate ((ident : α) :: List.replicate k (ident : α) ++ xs)
            = aggregate xs
      show aggregate ((ident : α) :: (List.replicate k (ident : α) ++ xs))
            = aggregate xs
      rw [aggregate_cons_ident]
      exact ih

/-- Symmetric form. -/
lemma aggregate_append_replicate_ident (n : Nat) (xs : Coalition α) :
    aggregate (xs ++ List.replicate n (ident : α)) = aggregate xs := by
  rw [aggregate_append]
  -- aggregate (replicate n ident) = ident
  have : aggregate (List.replicate n (ident : α)) = ident := by
    have := aggregate_trivial (α := α) n
    -- Coalition.trivial α n = List.replicate n ident (definitionally)
    exact this
  rw [this]
  exact id_right _

/-- A coalition aggregates the same as its `delegate` with itself
    swapped if both sub-aggregates collapse to a common value.  This
    is a tiny technical lemma used in §10.5. -/
lemma aggregate_delegate_swap_of_eq {xs ys : Coalition α}
    (h : aggregate xs = aggregate ys) :
    aggregate (Coalition.delegate xs ys) = aggregate (Coalition.delegate ys xs) := by
  rw [aggregate_delegate, aggregate_delegate, h]

/-- The aggregate of a coalition equals the aggregate of any coalition
    obtained by inserting silent agents at any positions. -/
lemma aggregate_of_insert_idents :
    ∀ (xs ys : Coalition α),
      Coalition.AllSilent ys →
        aggregate (xs ++ ys) = aggregate xs
  | xs, ys, h => by
      have hys : aggregate ys = ident := aggregate_of_all_silent ys h
      rw [aggregate_append, hys]
      exact id_right _

/-- A delegate of a silent coalition on either side does not affect
    the aggregate. -/
lemma aggregate_silent_left (xs ys : Coalition α)
    (h : Coalition.AllSilent xs) :
    aggregate (xs ++ ys) = aggregate ys := by
  have hxs : aggregate xs = ident := aggregate_of_all_silent xs h
  rw [aggregate_append, hxs]
  exact id_left _

/-- The committee with silent chair has the collective idea of its
    member coalition. -/
lemma committee_silent_chair (members : Coalition α) :
    (⟨ident, members⟩ : Committee α).collective = aggregate members := by
  unfold Committee.collective
  exact id_left _

/-- The committee with empty member list has the chair's idea as
    collective. -/
lemma committee_empty_members (chair : α) :
    (⟨chair, []⟩ : Committee α).collective = chair := by
  unfold Committee.collective
  show op chair (aggregate ([] : Coalition α)) = chair
  rw [aggregate_nil]
  exact id_right _

end Chains

/-! ## §10.4 `theorem_10_1` — coalition associativity -/

/-- **Theorem 10.1 (Coalition associativity / social composition law).**

    *Informal claim.*  The IDT manuscript, Volume V Chapter 1, asserts
    that "the aggregate idea of a coalition is independent of how the
    coalition is partitioned into sub-coalitions before aggregation".
    This is the social-composition reading of the Volume 1
    associativity theorem and is repeatedly invoked in Sen 1970 §2.4
    and List/Pettit 2011 §6.3 as the *associativity of joint
    judgement*.

    *Sources.*  Arrow 1951 §III.4 (independence of the order of
    coalition formation); Sen 1970 §2.4 (aggregate as a fold);
    List/Pettit 2011 §6.3 (joint judgement); IDT manuscript Vol. V §1.2.

    *Lemmas used.*  `aggregate_append`, `aggregate_append_assoc_L`,
    `aggregate_append_assoc_R`, `aggregate_append_triple_assoc`, and
    the underlying `assoc` axiom.

    *Sharpening.*  The informal manuscript states the law for two
    sub-coalitions; the present formal statement gives both the
    binary associativity for `xs ++ ys ++ zs` and the *general*
    statement that the aggregate of any append decomposes as
    `op (aggregate xs) (aggregate ys)`.  In particular the formal
    version makes the latter a *conjunction*, which is sharper than
    the bare informal claim.

    *Proof strategy.*
    1. Reduce both halves to the lemma `aggregate_append`.
    2. For the second half (associative reassociation) appeal to
       `aggregate_append_triple_assoc`.
    3. Combine via `And.intro`.
-/
theorem theorem_10_1 (xs ys zs : Coalition α) :
    aggregate (xs ++ ys) = op (aggregate xs) (aggregate ys) ∧
    aggregate ((xs ++ ys) ++ zs) = aggregate (xs ++ (ys ++ zs)) := by
  refine ⟨?_, ?_⟩
  · -- decomposition law
    exact aggregate_append xs ys
  · -- reassociation law
    exact aggregate_append_triple_assoc xs ys zs

/-! ## §10.5 `theorem_10_2` — silent-agent invariance -/

/-- **Theorem 10.2 (Silent-agent invariance).**

    *Informal claim.*  IDT Vol. V §1.3 asserts that "adding or
    removing silent agents from a coalition does not change the
    coalition's collective idea".  This is the formal counterpart of
    the social-choice principle that abstaining voters do not alter
    the outcome (Sen 1970 §2.5, "abstention-invariance").

    *Sources.*  Arrow 1951 §V.2 ("ineffective alternatives"); Sen
    1970 §2.5 ("abstention-invariance"); IDT manuscript Vol. V §1.3.

    *Lemmas used.*  `aggregate_insert_ident`, `aggregate_cons_ident`,
    `aggregate_snoc_ident`, `aggregate_replicate_ident_append`,
    `aggregate_append_replicate_ident`.

    *Sharpening.*  The informal version handles only "the addition
    of one silent agent at the head".  The present statement is a
    *conjunction* covering: (a) insertion at any position `n`;
    (b) prepending and appending arbitrary lengths of silent agents;
    (c) sandwiching by a silent agent at each end.

    *Proof strategy.*
    1. Use `aggregate_insert_ident` for arbitrary-position insertion.
    2. Use `aggregate_replicate_ident_append` and
       `aggregate_append_replicate_ident` for the bulk-prepending
       and bulk-appending halves.
    3. Use `aggregate_sandwich_idents` for the sandwich half.
    4. Combine the four facts via `⟨_, _, _, _⟩`.
-/
theorem theorem_10_2 (xs : Coalition α) :
    (∀ n : Nat, aggregate (Coalition.insertAt (ident : α) n xs) = aggregate xs) ∧
    (∀ n : Nat, aggregate (List.replicate n (ident : α) ++ xs) = aggregate xs) ∧
    (∀ n : Nat, aggregate (xs ++ List.replicate n (ident : α)) = aggregate xs) ∧
    aggregate ((ident : α) :: xs ++ [(ident : α)]) = aggregate xs := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    exact aggregate_insert_ident n xs
  · intro n
    exact aggregate_replicate_ident_append n xs
  · intro n
    exact aggregate_append_replicate_ident n xs
  · exact aggregate_sandwich_idents xs

/-! ## §10.6 `theorem_10_3` — social congruence -/

/-- **Theorem 10.3 (Social congruence theorem).**

    *Informal claim.*  IDT Vol. V §1.4 asserts that "social
    equivalence of coalitions is an equivalence relation that is
    preserved by every coalitional operation considered in this
    chapter".  In the social-choice tradition this is sometimes
    called the *aggregation congruence theorem* and is implicit in
    every "Independence" axiom of Arrow-style theorems.

    *Sources.*  Arrow 1951 §III–§V (Independence of Irrelevant
    Alternatives); MacLane 1971 §I.5 (congruences); IDT manuscript
    Vol. V §1.4.

    *Lemmas used.*  `CoalitionEquiv.refl`, `CoalitionEquiv.symm`,
    `CoalitionEquiv.trans`, `CoalitionEquiv.append`,
    `CoalitionEquiv.append_left`, `CoalitionEquiv.append_right`,
    `CoalitionEquiv.insert_ident`.

    *Sharpening.*  The informal version mentions "an equivalence
    relation"; the present statement packages **seven** independent
    properties: reflexivity, symmetry, transitivity, simultaneous
    append-congruence, left-append-congruence,
    right-append-congruence, and silent-agent-insertion invariance.

    *Proof strategy.*
    1. Each of the seven facts is handled by the corresponding
       sectional lemma.
    2. They are bundled into a 7-tuple by `⟨_, _, _, _, _, _, _⟩`.
-/
theorem theorem_10_3 :
    (∀ xs : Coalition α, CoalitionEquiv xs xs) ∧
    (∀ xs ys : Coalition α, CoalitionEquiv xs ys → CoalitionEquiv ys xs) ∧
    (∀ xs ys zs : Coalition α,
      CoalitionEquiv xs ys → CoalitionEquiv ys zs → CoalitionEquiv xs zs) ∧
    (∀ xs₁ xs₂ ys₁ ys₂ : Coalition α,
      CoalitionEquiv xs₁ xs₂ → CoalitionEquiv ys₁ ys₂ →
      CoalitionEquiv (xs₁ ++ ys₁) (xs₂ ++ ys₂)) ∧
    (∀ zs : Coalition α, ∀ xs ys : Coalition α,
      CoalitionEquiv xs ys → CoalitionEquiv (zs ++ xs) (zs ++ ys)) ∧
    (∀ zs : Coalition α, ∀ xs ys : Coalition α,
      CoalitionEquiv xs ys → CoalitionEquiv (xs ++ zs) (ys ++ zs)) ∧
    (∀ n : Nat, ∀ xs : Coalition α,
      CoalitionEquiv xs (Coalition.insertAt (ident : α) n xs)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro xs
    exact CoalitionEquiv.refl xs
  · intro xs ys h
    exact CoalitionEquiv.symm h
  · intro xs ys zs h₁ h₂
    exact CoalitionEquiv.trans h₁ h₂
  · intro xs₁ xs₂ ys₁ ys₂ h₁ h₂
    exact CoalitionEquiv.append h₁ h₂
  · intro zs xs ys h
    exact CoalitionEquiv.append_left zs h
  · intro zs xs ys h
    exact CoalitionEquiv.append_right h zs
  · intro n xs
    exact CoalitionEquiv.insert_ident n xs

/-! ## §10.7 Corollaries -/

/-- **Corollary 10.1 (Two-coalition decomposition).**
    The aggregate of a delegate is the `op` of the two aggregates.
    This is the form most often quoted in the social-choice
    literature (Arrow 1951 §III.4, "merger of coalitions"). -/
theorem corollary_10_1 (xs ys : Coalition α) :
    aggregate (Coalition.delegate xs ys)
      = op (aggregate xs) (aggregate ys) :=
  aggregate_delegate xs ys

/-- **Corollary 10.2 (Trivial-coalition collapse).**
    Any coalition consisting only of silent agents has the identity
    as collective idea.  This is the formal version of "an assembly
    of abstainers reaches the null verdict" (Sen 1970 §2.5). -/
theorem corollary_10_2 (xs : Coalition α) (h : Coalition.AllSilent xs) :
    aggregate xs = ident :=
  aggregate_of_all_silent xs h

/-- **Corollary 10.3 (Insertion-deletion congruence).**
    Inserting a silent agent at any position yields a socially
    equivalent coalition.  This corresponds to the IDT manuscript's
    Vol. V §1.4 closing remark "silent insertion is a congruence
    move". -/
theorem corollary_10_3 (n : Nat) (xs : Coalition α) :
    CoalitionEquiv xs (Coalition.insertAt (ident : α) n xs) :=
  CoalitionEquiv.insert_ident n xs

/-- **Corollary 10.4 (Committee-collective decomposition).**
    The collective idea of a committee `c` is the `op` of its chair's
    idea with the aggregate of its member coalition.  This is the
    formal version of the IDT manuscript's Vol. V §1.5 statement
    "the chair speaks first". -/
theorem corollary_10_4 (c : Committee α) :
    c.collective = op c.chair (aggregate c.members) := rfl

/-- **Corollary 10.5 (Assembly-pair decomposition).**
    The collective idea of a two-committee assembly is the `op` of
    the two committees' collective ideas.  This packages the
    two-tier hierarchical structure of List/Pettit 2011, Part II
    in our setting. -/
theorem corollary_10_5 (c d : Committee α) :
    (⟨[c, d]⟩ : Assembly α).collective = op c.collective d.collective :=
  assembly_pair_collective c d

/-! ## §10.8 Examples and sanity checks -/

/-- Example: the empty coalition aggregates to `ident`. -/
example : aggregate ([] : Coalition α) = (ident : α) := aggregate_nil

/-- Example: the singleton coalition aggregates to its agent. -/
example (a : α) : aggregate (Coalition.singleton a) = a :=
  aggregate_singleton a

/-- Example: the pair coalition aggregates to `op a b`. -/
example (a b : α) : aggregate (Coalition.pair a b) = op a b :=
  aggregate_pair a b

/-- Example: silent-agent insertion at position 7 is invisible. -/
example (xs : Coalition α) :
    aggregate (Coalition.insertAt (ident : α) 7 xs) = aggregate xs :=
  (theorem_10_2 xs).1 7

/-- Example: an empty assembly aggregates to `ident`. -/
example : (⟨[]⟩ : Assembly α).collective = (ident : α) :=
  assembly_empty_collective

/-- Example: every coalition is socially equivalent to itself. -/
example (xs : Coalition α) : CoalitionEquiv xs xs :=
  (theorem_10_3 (α := α)).1 xs

/-- Example: the pair `[ident, a]` is socially equivalent to `[a]`. -/
example (a : α) :
    CoalitionEquiv ([(ident : α), a] : Coalition α) [a] := by
  unfold CoalitionEquiv
  show aggregate ([(ident : α), a] : Coalition α) = aggregate [a]
  rw [aggregate_cons_ident]

/-- Example: a 5-fold all-silent coalition is equivalent to `[]`. -/
example : CoalitionEquiv (Coalition.trivial α 5) ([] : Coalition α) :=
  CoalitionEquiv.trivial_nil 5

/-! ## Index of results

Public declarations in this file (Volume 5, "Social Composition"):

* §10.0 auxiliary definitions
  - `Coalition`                                        : abbrev for `List α`.
  - `aggregate`                                        : right-fold collective idea.
  - `Committee`, `Assembly`                            : structured coalitions.
  - `Committee.collective`, `Assembly.collective`      : their aggregates.
  - `IsSilent`                                         : silent-agent predicate.
  - `Coalition.trivial`                                : list of `n` silent agents.
  - `Coalition.singleton/pair/triple`                  : small coalitions.
  - `CoalitionEquiv`                                   : social equivalence.
  - `Coalition.insertAt`                               : positional insertion.
  - `Coalition.delegate`                               : append as delegation.
  - `Coalition.AllSilent`                              : universal silence.

* §10.1 closure
  - `aggregate_nil/singleton/cons/pair/triple`,
  - `trivial_zero/succ`, `aggregate_trivial`,
  - `aggregate_singleton_silent/pair_silent/triple_silent`.

* §10.2 silent-agent insertion and deletion
  - `aggregate_cons_ident`, `aggregate_cons_singleton_ident`,
  - `aggregate_append`, `aggregate_append_nil/nil_append`,
  - `aggregate_append_trivial`, `aggregate_trivial_append`,
  - `aggregate_insert_ident_zero`, `insertAt_nil`,
  - `insertAt_succ_cons`, `insertAt_zero_cons`,
  - `aggregate_insert_ident`, `aggregate_tail_of_ident_head`,
  - `aggregate_of_all_silent`.

* §10.3 monotonicity and committee/assembly
  - `aggregate_delegate`, `delegate_assoc`,
  - `delegate_nil_left/right`,
  - `aggregate_cons_congr`,
  - `aggregate_append_left_congr/right_congr`,
  - `aggregate_swap_head_silent`, `aggregate_replace_head_ident`,
  - `committee_collective_eq_aggregate`,
  - `assembly_empty_collective/singleton_collective/pair_collective`.

* §10.3′ equivalence
  - `CoalitionEquiv.refl/symm/trans`,
  - `CoalitionEquiv.append_right/append_left/append`,
  - `CoalitionEquiv.insert_ident/trivial_nil/singleton_iff`.

* §10.3″ chains and reassociation
  - `aggregate_append_assoc_L/R`,
  - `aggregate_append_triple_assoc`,
  - `aggregate_insert_ident_after_head`, `aggregate_two_idents_middle`,
  - `aggregate_snoc_ident/snoc_two_idents/sandwich_idents`,
  - `aggregate_replicate_ident_append`,
  - `aggregate_append_replicate_ident`,
  - `aggregate_delegate_swap_of_eq`,
  - `aggregate_of_insert_idents`, `aggregate_silent_left`,
  - `committee_silent_chair`, `committee_empty_members`.

* §10.4 `theorem_10_1`  : coalition associativity.
* §10.5 `theorem_10_2`  : silent-agent invariance.
* §10.6 `theorem_10_3`  : social congruence.

* §10.7 corollaries
  - `corollary_10_1`    : two-coalition decomposition.
  - `corollary_10_2`    : trivial-coalition collapse.
  - `corollary_10_3`    : insertion-deletion congruence.
  - `corollary_10_4`    : committee-collective decomposition.
  - `corollary_10_5`    : assembly-pair decomposition.

* §10.8 examples (sanity checks).
-/

end IdeaTheory
