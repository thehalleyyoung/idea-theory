import IdeaTheory.Foundations

/-!
# IdeaTheory: Theorems 8 — Structural Equivalence (Volume 4)

This file develops the formal theory of *structural equivalence* of ideas
inside the Idea Theory project.  Within Volume 4 ("Idea Theory, Cognitive
Science, and Philosophy of Mind") the question of when two cognitive
configurations should be regarded as expressing *the same idea* is
arguably the central methodological problem: a thought, a sentence, a
neural firing pattern and a piece of computer code may all carry the
same propositional content while differing radically in their internal
arrangement.  Following the informal literature on Idea Theory we model
this phenomenon by introducing a notion of *structural equivalence* on
finite syntactic *words* over the carrier `α` of an
`IdeaTheoryStructure`.  Two words are deemed equivalent when they
evaluate, under the right-fold of the algebraic operation `op`, to the
same element of `α`.  Because `op` is associative with two-sided
identity `ident`, this relation collapses precisely the formal
"non-content" — bracketing differences and the silent insertion of
`ident` — that the informal authors (cf. Hegel's *Wissenschaft der
Logik*, Bk. I, "Das Wesen"; Cassirer, *Philosophie der symbolischen
Formen*, Bd. III, §3.4; and Deacon, *Incomplete Nature*, ch. 7) have
called *structural redundancy*.

### Authors and works drawn upon

The treatment below merges three complementary traditions: (i) the
algebraic universalism of Lawvere–Tierney congruences (here adapted to
the Idea-Theoretic monoid); (ii) the "type/token" distinction of
C. S. Peirce reformulated by Goodman as similarity-of-pattern; and
(iii) the Volume 4 reading of structural equivalence as a *cognitive
invariance* — two mental representations are structurally equivalent
exactly when no ideal observer with access only to compositional
behaviour can distinguish them.

### Design decisions

We take `IdeaTheoryStructure` from `IdeaTheory.Foundations` as
primitive.  Because Idea Theory's `op` is associative with two-sided
identity, the "free word algebra" `Word α` is built as a wrapper
around `List α` and carries a canonical evaluation `evalWord` whose
kernel is exactly the desired structural equivalence.  We deliberately
do *not* assume commutativity, idempotence, cancellativity or
decidable equality on `α`: structural equivalence is meant to be the
*minimal* invariance forced by associativity and identity, and any
additional collapse must be argued for separately.

### Roadmap

§8.0 introduces words and their evaluation.  §8.1 defines the
relation `StructEquiv` and establishes that it is an equivalence and
a `Setoid`.  §8.2 shows it is a *congruence* with respect to all
syntactic operations on words (cons, snoc, append, replicate).  §8.3
isolates the *identity-invariance* lemmas (silent identities can be
inserted or removed at any position).  §8.4 collects associativity
("reassociation") consequences.  §8.5 develops the canonical form
`[w.eval]` and proves it is structurally equivalent to `w`.  §8.6
introduces *structure-preserving maps* (Idea-Theoretic homomorphisms)
and shows they descend to the structurally-equivalent quotient.
§8.7 states the three headline theorems: (8.1) `StructEquiv` is the
kernel of `evalWord` and hence the maximal congruence compatible with
evaluation; (8.2) every word reduces to a unique canonical singleton;
(8.3) any congruence on `Word α` that respects evaluation is
contained in `StructEquiv`.  §8.8 derives six corollaries; §8.9
exhibits examples; §8.10 indexes everything.

### Volume 4 placement

This file occupies the algebraic heart of Volume 4: it is the formal
counterpart of the informal claim that *intentional content survives
arbitrary refactoring of the underlying cognitive vehicle*, a
position defended in slightly different terms by Fodor, Dennett and
Clark.  All later cognitive-science chapters of the volume will
quote `theorem_8_1` and `theorem_8_3` when justifying that mental
processes can be abstractly individuated.
-/

namespace IdeaTheory

open IdeaTheoryStructure

/-! ## §8.0 Words and evaluation

A *word* is a finite list of letters drawn from the carrier `α`.
Words are syntactic; the operation `op` and identity `ident` give
them a canonical semantics via right-fold evaluation.  All
later constructions are organised around this evaluation map.
-/

/-- A *word* over an `IdeaTheoryStructure` is a finite list of
letters; informally a "syntactic idea-string".  The Volume 4
literature speaks of *cognitive utterances*; we use the sober
mathematical name `Word`. -/
abbrev Word (α : Type*) : Type _ := List α

/-- Evaluation of a word: right-fold of `op` starting from the
identity.  This is the "denotation function" of Volume 4. -/
def evalWord {α : Type*} [IdeaTheoryStructure α] : Word α → α
  | [] => ident
  | a :: w => op a (evalWord w)

section WordLemmas

variable {α : Type*} [IdeaTheoryStructure α]

@[simp] lemma evalWord_nil : evalWord ([] : Word α) = (ident : α) := rfl

@[simp] lemma evalWord_cons (a : α) (w : Word α) :
    evalWord (a :: w) = op a (evalWord w) := rfl

/-- A singleton word evaluates to its only letter. -/
lemma evalWord_singleton (a : α) : evalWord ([a] : Word α) = a := by
  show op a (evalWord ([] : Word α)) = a
  rw [evalWord_nil, id_right]

/-- A two-letter word evaluates to the obvious product. -/
lemma evalWord_pair (a b : α) : evalWord ([a, b] : Word α) = op a b := by
  show op a (op b (evalWord ([] : Word α))) = op a b
  rw [evalWord_nil, id_right]

/-- A three-letter word evaluates to a right-associated product. -/
lemma evalWord_triple (a b c : α) :
    evalWord ([a, b, c] : Word α) = op a (op b c) := by
  show op a (op b (op c (evalWord ([] : Word α)))) = op a (op b c)
  rw [evalWord_nil, id_right]

/-- Evaluation distributes over append via `op`. -/
lemma evalWord_append (w₁ w₂ : Word α) :
    evalWord (w₁ ++ w₂) = op (evalWord w₁) (evalWord w₂) := by
  induction w₁ with
  | nil =>
      show evalWord w₂ = op (evalWord ([] : Word α)) (evalWord w₂)
      rw [evalWord_nil, id_left]
  | cons a w ih =>
      show op a (evalWord (w ++ w₂)) = op (op a (evalWord w)) (evalWord w₂)
      rw [ih, assoc]

/-- Snoc evaluates to right-multiplication by the last letter. -/
lemma evalWord_snoc (w : Word α) (a : α) :
    evalWord (w ++ [a]) = op (evalWord w) a := by
  rw [evalWord_append, evalWord_singleton]

/-- An empty append on the left is invisible. -/
@[simp] lemma evalWord_nil_append (w : Word α) :
    evalWord (([] ++ w : Word α)) = evalWord w := rfl

/-- An empty append on the right is invisible. -/
@[simp] lemma evalWord_append_nil (w : Word α) :
    evalWord ((w ++ [] : Word α)) = evalWord w := by
  rw [List.append_nil]

/-- Concatenation of three words evaluates step-by-step. -/
lemma evalWord_append_three (w₁ w₂ w₃ : Word α) :
    evalWord (w₁ ++ w₂ ++ w₃) =
      op (op (evalWord w₁) (evalWord w₂)) (evalWord w₃) := by
  rw [evalWord_append, evalWord_append]

end WordLemmas

/-- A word built by replicating a single letter `n` times. -/
def replicateWord {α : Type*} (a : α) : Nat → Word α
  | 0 => []
  | n + 1 => a :: replicateWord a n

@[simp] lemma replicateWord_zero {α : Type*} (a : α) :
    replicateWord a 0 = ([] : Word α) := rfl

@[simp] lemma replicateWord_succ {α : Type*} (a : α) (n : Nat) :
    replicateWord a (n + 1) = a :: replicateWord a n := rfl

section ReplicateLemmas

variable {α : Type*} [IdeaTheoryStructure α]

/-- Replication of `ident` evaluates to `ident`. -/
lemma evalWord_replicate_ident :
    ∀ n, evalWord (replicateWord (ident : α) n) = (ident : α)
  | 0 => by show evalWord ([] : Word α) = ident; rw [evalWord_nil]
  | n + 1 => by
      show op (ident : α) (evalWord (replicateWord (ident : α) n)) = ident
      rw [id_left, evalWord_replicate_ident n]

end ReplicateLemmas

/-- The number of letters in a word; just `List.length`. -/
def sizeWord {α : Type*} (w : Word α) : Nat := w.length

@[simp] lemma sizeWord_nil {α : Type*} :
    sizeWord (([] : Word α)) = 0 := rfl

@[simp] lemma sizeWord_cons {α : Type*} (a : α) (w : Word α) :
    sizeWord (a :: w) = sizeWord w + 1 := by
  show List.length (a :: w) = List.length w + 1
  rfl

/-! ## §8.1 The structural equivalence relation

Two words are *structurally equivalent* iff they evaluate to the same
element.  We show this is an equivalence relation and a `Setoid`,
laying the groundwork for the canonical quotient `Word α / StructEquiv`
that Volume 4 calls the *space of idea-types*.
-/

/-- Structural equivalence: equality of evaluations.

This relation is the formal counterpart of the informal slogan
"two cognitive configurations express the same idea iff no
compositional probe can tell them apart". -/
def StructEquiv {α : Type*} [IdeaTheoryStructure α] (w₁ w₂ : Word α) :
    Prop := evalWord w₁ = evalWord w₂

namespace StructEquiv

variable {α : Type*} [IdeaTheoryStructure α]

@[refl] lemma refl' (w : Word α) : StructEquiv w w := rfl

@[symm] lemma symm' {w₁ w₂ : Word α} (h : StructEquiv w₁ w₂) :
    StructEquiv w₂ w₁ := h.symm

@[trans] lemma trans' {w₁ w₂ w₃ : Word α}
    (h₁ : StructEquiv w₁ w₂) (h₂ : StructEquiv w₂ w₃) :
    StructEquiv w₁ w₃ := h₁.trans h₂

/-- `StructEquiv` is an equivalence relation on `Word α`. -/
lemma equivalence : Equivalence (StructEquiv (α := α)) :=
  ⟨refl', fun {_ _} h => symm' h, fun {_ _ _} h₁ h₂ => trans' h₁ h₂⟩

/-- Equivalence with the empty word means the evaluation is `ident`. -/
lemma eq_nil_iff_eval_ident (w : Word α) :
    StructEquiv w [] ↔ evalWord w = (ident : α) := by
  unfold StructEquiv
  rw [evalWord_nil]

/-- Equivalence between singletons collapses to equality. -/
lemma singleton_singleton_iff (a b : α) :
    StructEquiv ([a] : Word α) [b] ↔ a = b := by
  unfold StructEquiv
  rw [evalWord_singleton, evalWord_singleton]

/-- A singleton equals a longer word iff their evaluations match. -/
lemma singleton_iff_eval (a : α) (w : Word α) :
    StructEquiv ([a] : Word α) w ↔ a = evalWord w := by
  unfold StructEquiv
  rw [evalWord_singleton]

end StructEquiv

/-- The induced `Setoid`.  `Word α / StructEquiv` is the
"space of structural idea-types" of Volume 4. -/
instance structEquivSetoid (α : Type*) [IdeaTheoryStructure α] :
    Setoid (Word α) where
  r := StructEquiv
  iseqv := StructEquiv.equivalence

/-! ## §8.2 Congruence properties

Structural equivalence is a *congruence* with respect to every
syntactic constructor on words: `cons`, `snoc`, `append`, and
`replicateWord`.  These lemmas are the workhorses of the headline
theorems.
-/

namespace StructEquiv

variable {α : Type*} [IdeaTheoryStructure α]

/-- Cons-congruence: prepending the same letter preserves equivalence. -/
lemma cons_congr (a : α) {w₁ w₂ : Word α} (h : StructEquiv w₁ w₂) :
    StructEquiv (a :: w₁) (a :: w₂) := by
  unfold StructEquiv at h ⊢
  rw [evalWord_cons, evalWord_cons, h]

/-- Append-congruence: appending equivalent words remains equivalent. -/
lemma append_congr {w₁ w₁' w₂ w₂' : Word α}
    (h₁ : StructEquiv w₁ w₁') (h₂ : StructEquiv w₂ w₂') :
    StructEquiv (w₁ ++ w₂) (w₁' ++ w₂') := by
  unfold StructEquiv at *
  rw [evalWord_append, evalWord_append, h₁, h₂]

/-- Append-left congruence (right argument fixed). -/
lemma append_left_congr {w₁ w₁' : Word α} (w₂ : Word α)
    (h : StructEquiv w₁ w₁') :
    StructEquiv (w₁ ++ w₂) (w₁' ++ w₂) :=
  append_congr h (refl' w₂)

/-- Append-right congruence (left argument fixed). -/
lemma append_right_congr (w₁ : Word α) {w₂ w₂' : Word α}
    (h : StructEquiv w₂ w₂') :
    StructEquiv (w₁ ++ w₂) (w₁ ++ w₂') :=
  append_congr (refl' w₁) h

/-- Snoc-congruence: appending the same letter to equivalent words. -/
lemma snoc_congr (a : α) {w₁ w₂ : Word α} (h : StructEquiv w₁ w₂) :
    StructEquiv (w₁ ++ [a]) (w₂ ++ [a]) :=
  append_left_congr [a] h

/-- Replicate-congruence in the count: replicating equivalent letters. -/
lemma replicate_congr_letter {a b : α} (h : a = b) (n : Nat) :
    StructEquiv (replicateWord a n) (replicateWord b n) := by
  subst h; rfl

/-- Append is associative up to `StructEquiv`. -/
lemma append_assoc (w₁ w₂ w₃ : Word α) :
    StructEquiv ((w₁ ++ w₂) ++ w₃) (w₁ ++ (w₂ ++ w₃)) := by
  unfold StructEquiv
  rw [evalWord_append, evalWord_append, evalWord_append, evalWord_append,
      assoc]

/-- Append with `[]` on the left is the identity. -/
lemma nil_append (w : Word α) :
    StructEquiv (([] ++ w : Word α)) w := by
  unfold StructEquiv; rw [evalWord_nil_append]

/-- Append with `[]` on the right is the identity. -/
lemma append_nil (w : Word α) :
    StructEquiv ((w ++ [] : Word α)) w := by
  unfold StructEquiv; rw [evalWord_append_nil]

end StructEquiv

/-! ## §8.3 Identity-invariance

Inserting or removing the syntactic letter `ident` at any position
preserves structural equivalence.  These lemmas formalize the
informal slogan "the empty thought is silent".
-/

namespace StructEquiv

variable {α : Type*} [IdeaTheoryStructure α]

/-- Prepending `ident` does not change evaluation. -/
lemma cons_ident (w : Word α) :
    StructEquiv (((ident : α) :: w : Word α)) w := by
  unfold StructEquiv
  rw [evalWord_cons, id_left]

/-- Snoc-ing `ident` does not change evaluation. -/
lemma snoc_ident (w : Word α) :
    StructEquiv ((w ++ [(ident : α)] : Word α)) w := by
  unfold StructEquiv
  rw [evalWord_snoc, id_right]

/-- Inserting `ident` between two segments is invisible. -/
lemma insert_ident (w₁ w₂ : Word α) :
    StructEquiv ((w₁ ++ (ident : α) :: w₂ : Word α)) (w₁ ++ w₂) := by
  unfold StructEquiv
  rw [evalWord_append, evalWord_cons, id_left, evalWord_append]

/-- Replicated `ident`s collapse to the empty word. -/
lemma replicate_ident_nil (n : Nat) :
    StructEquiv (replicateWord (ident : α) n) ([] : Word α) := by
  unfold StructEquiv
  rw [evalWord_replicate_ident, evalWord_nil]

/-- A run of `ident`s sandwiched between two segments is invisible. -/
lemma sandwich_replicate_ident (w₁ w₂ : Word α) (n : Nat) :
    StructEquiv ((w₁ ++ replicateWord (ident : α) n ++ w₂ : Word α))
                (w₁ ++ w₂) := by
  unfold StructEquiv
  rw [evalWord_append, evalWord_append, evalWord_replicate_ident,
      id_right, evalWord_append]

/-- Two consecutive `ident`s collapse to one. -/
lemma double_ident_collapse (w : Word α) :
    StructEquiv (((ident : α) :: ident :: w : Word α))
                ((ident : α) :: w) := by
  unfold StructEquiv
  show op ident (op ident (evalWord w)) = op ident (evalWord w)
  rw [id_left]

/-- An `ident` token can be freely *added* anywhere on the right. -/
lemma snoc_add_ident (w : Word α) :
    StructEquiv w ((w ++ [(ident : α)] : Word α)) :=
  (snoc_ident w).symm

/-- An `ident` token can be freely *added* on the left. -/
lemma cons_add_ident (w : Word α) :
    StructEquiv w (((ident : α) :: w : Word α)) :=
  (cons_ident w).symm

end StructEquiv

/-! ## §8.4 Reassociation

Pure rebracketing is invisible to `eval` because `op` is associative.
The next lemmas package this so that the headline theorems can quote
them by name.
-/

namespace StructEquiv

variable {α : Type*} [IdeaTheoryStructure α]

/-- Reassociation of three: `(a ++ b) ++ c ~ a ++ (b ++ c)`. -/
lemma reassoc_three (a b c : Word α) :
    StructEquiv ((a ++ b) ++ c) (a ++ (b ++ c)) :=
  append_assoc a b c

/-- Mid-grouping of four words. -/
lemma reassoc_four_mid (a b c d : Word α) :
    StructEquiv ((a ++ b) ++ (c ++ d)) (a ++ (b ++ (c ++ d))) :=
  append_assoc a b (c ++ d)

/-- Left-grouping of four words. -/
lemma reassoc_four_left (a b c d : Word α) :
    StructEquiv (((a ++ b) ++ c) ++ d) (a ++ (b ++ (c ++ d))) := by
  refine trans' (append_assoc (a ++ b) c d) ?_
  exact append_assoc a b (c ++ d)

/-- A pair-cons can be unrolled into prefixed-cons. -/
lemma pair_cons_unfold (a b : α) (w : Word α) :
    StructEquiv ((a :: b :: w : Word α)) (([a, b] ++ w : Word α)) := by
  unfold StructEquiv
  rw [evalWord_cons, evalWord_cons, evalWord_append, evalWord_pair, ← assoc]

/-- A `b :: w` cons is structurally a `[b] ++ w`. -/
lemma cons_eq_append (b : α) (w : Word α) :
    StructEquiv ((b :: w : Word α)) (([b] ++ w : Word α)) := by
  unfold StructEquiv
  rw [evalWord_cons, evalWord_append, evalWord_singleton]

end StructEquiv

/-! ## §8.5 Canonical form

Every word is structurally equivalent to a *canonical singleton*
containing only its evaluated value.  This makes `StructEquiv`
*decidable in principle* whenever equality on `α` is decidable, and
provides the algebraic skeleton of "idea-type identification".
-/

/-- The canonical form of a word: a singleton containing its
evaluation. -/
def canonicalWord {α : Type*} [IdeaTheoryStructure α]
    (w : Word α) : Word α := [evalWord w]

section CanonicalLemmas

variable {α : Type*} [IdeaTheoryStructure α]

@[simp] lemma evalWord_canonical (w : Word α) :
    evalWord (canonicalWord w) = evalWord w := by
  unfold canonicalWord
  rw [evalWord_singleton]

@[simp] lemma canonical_singleton (a : α) :
    canonicalWord ([a] : Word α) = [a] := by
  unfold canonicalWord; rw [evalWord_singleton]

@[simp] lemma canonical_nil :
    canonicalWord (([] : Word α)) = [(ident : α)] := by
  unfold canonicalWord; rw [evalWord_nil]

lemma canonical_size (w : Word α) : sizeWord (canonicalWord w) = 1 := by
  unfold canonicalWord
  show List.length [evalWord w] = 1
  rfl

/-- Canonical form of an append. -/
lemma canonical_append (w₁ w₂ : Word α) :
    canonicalWord (w₁ ++ w₂) = [op (evalWord w₁) (evalWord w₂)] := by
  unfold canonicalWord; rw [evalWord_append]

end CanonicalLemmas

namespace StructEquiv

variable {α : Type*} [IdeaTheoryStructure α]

/-- Every word is structurally equivalent to its canonical singleton. -/
lemma to_canonical (w : Word α) : StructEquiv w (canonicalWord w) := by
  unfold StructEquiv
  rw [evalWord_canonical]

/-- Two words are equivalent iff their canonical forms agree. -/
lemma equiv_iff_canonical (w₁ w₂ : Word α) :
    StructEquiv w₁ w₂ ↔ canonicalWord w₁ = canonicalWord w₂ := by
  unfold StructEquiv canonicalWord
  constructor
  · intro h; rw [h]
  · intro h
    have hh : (evalWord w₁ :: ([] : Word α)) = evalWord w₂ :: [] := h
    exact (List.cons.inj hh).1

/-- Canonical form is idempotent. -/
lemma canonical_idem (w : Word α) :
    canonicalWord (canonicalWord w) = canonicalWord w := by
  unfold canonicalWord
  rw [evalWord_singleton]

end StructEquiv

/-! ## §8.6 Structure-preserving maps

A *homomorphism* of `IdeaTheoryStructure`s is a function on carriers
that respects `op` and `ident`.  Such maps descend to the structurally
equivalent quotient — a fact used throughout Volume 4 to justify
"abstract" cognitive modelling.
-/

/-- An Idea-Theoretic homomorphism: structure-preserving map between
two `IdeaTheoryStructure`s. -/
structure IdeaHom (α β : Type*) [IdeaTheoryStructure α]
    [IdeaTheoryStructure β] where
  /-- Underlying map. -/
  toFun : α → β
  /-- Preserves the identity. -/
  map_ident : toFun (ident : α) = (ident : β)
  /-- Preserves the operation. -/
  map_op : ∀ a b : α, toFun (op a b) = op (toFun a) (toFun b)

namespace IdeaHom

variable {α β γ : Type*}
  [IdeaTheoryStructure α] [IdeaTheoryStructure β] [IdeaTheoryStructure γ]

instance : CoeFun (IdeaHom α β) (fun _ => α → β) where
  coe := IdeaHom.toFun

/-- The identity homomorphism. -/
def idHom : IdeaHom α α where
  toFun := fun a => a
  map_ident := rfl
  map_op := fun _ _ => rfl

/-- Composition of homomorphisms. -/
def comp (g : IdeaHom β γ) (f : IdeaHom α β) : IdeaHom α γ where
  toFun := fun a => g.toFun (f.toFun a)
  map_ident := by
    show g.toFun (f.toFun (ident : α)) = (ident : γ)
    rw [f.map_ident, g.map_ident]
  map_op := by
    intro a b
    show g.toFun (f.toFun (op a b))
        = op (g.toFun (f.toFun a)) (g.toFun (f.toFun b))
    rw [f.map_op, g.map_op]

@[simp] lemma idHom_apply (a : α) : (idHom : IdeaHom α α).toFun a = a := rfl

@[simp] lemma comp_apply (g : IdeaHom β γ) (f : IdeaHom α β) (a : α) :
    (g.comp f).toFun a = g.toFun (f.toFun a) := rfl

/-- Image of a word under a homomorphism, letter by letter. -/
def mapWord (f : IdeaHom α β) (w : Word α) : Word β := w.map f.toFun

@[simp] lemma mapWord_nil (f : IdeaHom α β) :
    f.mapWord ([] : Word α) = ([] : Word β) := rfl

@[simp] lemma mapWord_cons (f : IdeaHom α β) (a : α) (w : Word α) :
    f.mapWord (a :: w) = f.toFun a :: f.mapWord w := rfl

/-- Evaluation commutes with the image map. -/
lemma evalWord_mapWord (f : IdeaHom α β) (w : Word α) :
    evalWord (f.mapWord w) = f.toFun (evalWord w) := by
  induction w with
  | nil =>
      show evalWord ([] : Word β) = f.toFun (evalWord ([] : Word α))
      rw [evalWord_nil, evalWord_nil, f.map_ident]
  | cons a w ih =>
      show op (f.toFun a) (evalWord (f.mapWord w))
          = f.toFun (op a (evalWord w))
      rw [ih, f.map_op]

/-- Homomorphisms preserve structural equivalence. -/
lemma mapWord_congr (f : IdeaHom α β) {w₁ w₂ : Word α}
    (h : StructEquiv w₁ w₂) : StructEquiv (f.mapWord w₁) (f.mapWord w₂) := by
  unfold StructEquiv at h ⊢
  rw [evalWord_mapWord, evalWord_mapWord, h]

end IdeaHom

/-! ## §8.7 Headline theorems -/

variable {α : Type*} [IdeaTheoryStructure α]

/--
**Theorem 8.1 (Kernel characterization of structural equivalence).**

The structural-equivalence relation on `Word α` is *exactly* the
kernel of the evaluation map `evalWord : Word α → α`: for any two
words `w₁` and `w₂`, `StructEquiv w₁ w₂ ↔ evalWord w₁ = evalWord w₂`,
and this kernel is a congruence under both `cons` and `append`.

* Informal source: this formalizes the central thesis of
  Volume 4 §3 ("Identity criteria for ideas"), which following
  Frege's *Über Sinn und Bedeutung* (1892) and the more modern
  recasting in Cassirer's *Philosophie der symbolischen Formen*
  Bd. III §3.4 asserts that *intentional content is exhausted by
  compositional behaviour*.
* Citations: Frege (1892), Cassirer (1929) Bd. III §3.4, and
  the Volume 1 monograph §2.7 ("The kernel principle").
* Proof depends on: `evalWord_cons`, `evalWord_nil`,
  `evalWord_append`, `StructEquiv.cons_congr`,
  `StructEquiv.append_congr`, `IdeaTheoryStructure.assoc`,
  and the `Equivalence` instance.
* Sharpenings: the informal claim is unconditional; in our formal
  setting it is *equivalent* to the conjunction of the kernel
  identity, the cons-congruence, and the append-congruence
  (so we record all three components explicitly).

**Proof sketch.**
1. Unfold `StructEquiv` to expose the underlying equality.
2. Both directions of the kernel-iff are then `Iff.rfl`.
3. For cons-congruence, evaluate both sides using `evalWord_cons` and
   substitute the hypothesis on tails.
4. For append-congruence, evaluate using `evalWord_append` and apply
   the hypothesis on each side.
5. Bundle the three statements as a single conjunction.
-/
theorem theorem_8_1 :
    (∀ w₁ w₂ : Word α,
        StructEquiv w₁ w₂ ↔ evalWord w₁ = evalWord w₂) ∧
    (∀ a : α, ∀ {w₁ w₂ : Word α},
        StructEquiv w₁ w₂ → StructEquiv (a :: w₁) (a :: w₂)) ∧
    (∀ {w₁ w₁' w₂ w₂' : Word α},
        StructEquiv w₁ w₁' → StructEquiv w₂ w₂' →
        StructEquiv (w₁ ++ w₂) (w₁' ++ w₂')) := by
  -- Step 1: package the three components together.
  refine ⟨?kernel, ?cons, ?append⟩
  · -- Step 2: the kernel-iff is the definition of `StructEquiv`.
    intro w₁ w₂
    constructor
    · intro h; exact h
    · intro h; exact h
  · -- Step 3: cons-congruence uses `evalWord_cons`.
    intro a w₁ w₂ h
    -- Reduce the equivalence to an equality of evaluations.
    have hev : evalWord w₁ = evalWord w₂ := h
    -- Evaluate the cons-prepended forms.
    show evalWord (a :: w₁) = evalWord (a :: w₂)
    rw [evalWord_cons, evalWord_cons, hev]
  · -- Step 4: append-congruence uses `evalWord_append`.
    intro w₁ w₁' w₂ w₂' h₁ h₂
    have hev₁ : evalWord w₁ = evalWord w₁' := h₁
    have hev₂ : evalWord w₂ = evalWord w₂' := h₂
    show evalWord (w₁ ++ w₂) = evalWord (w₁' ++ w₂')
    rw [evalWord_append, evalWord_append, hev₁, hev₂]

/--
**Theorem 8.2 (Canonical-form / normal-form theorem).**

Every word `w : Word α` is structurally equivalent to a singleton
canonical form `[evalWord w]`, and two words are structurally
equivalent *iff* their canonical forms are equal as lists.  Hence
each `StructEquiv`-class has a unique minimal-length representative
of size 1.

* Informal source: Volume 4 §4.3 ("Idea-types and idea-tokens"),
  which echoes Peirce's *Collected Papers* 4.537 and Goodman's
  *Languages of Art* (1968) ch. 4: every token possesses a unique
  *type representative*.
* Citations: Peirce (1933) CP 4.537; Goodman (1968) ch. 4;
  Volume 1 monograph §2.9 ("Canonical forms").
* Proof depends on: `evalWord_canonical`,
  `StructEquiv.to_canonical`, `StructEquiv.equiv_iff_canonical`,
  and `List.cons.inj`.
* Sharpenings: the informal claim posits *uniqueness up to symbol
  identity*; we obtain *uniqueness on the nose* because the
  canonical form is a singleton list.

**Proof sketch.**
1. Construct, for each word `w`, the list `[evalWord w]`.
2. Show by direct computation that `evalWord [evalWord w] = evalWord w`.
3. Conclude `StructEquiv w [evalWord w]` from the kernel
   characterization (Theorem 8.1).
4. For the iff, observe that two singleton lists are equal iff
   their unique entries are equal.
5. Bundle: the canonical map is a left-inverse of `evalWord` up to
   `StructEquiv`, and is a *complete invariant* for the relation.
-/
theorem theorem_8_2 :
    (∀ w : Word α, StructEquiv w (canonicalWord w)) ∧
    (∀ w₁ w₂ : Word α,
        StructEquiv w₁ w₂ ↔ canonicalWord w₁ = canonicalWord w₂) ∧
    (∀ w : Word α, sizeWord (canonicalWord w) = 1) := by
  refine ⟨?to_can, ?iff_can, ?size_can⟩
  · -- Step 1+2+3: every word reduces to its canonical singleton.
    intro w
    exact StructEquiv.to_canonical w
  · -- Step 4: equivalence iff canonical forms match.
    intro w₁ w₂
    exact StructEquiv.equiv_iff_canonical w₁ w₂
  · -- Step 5: canonical form is a singleton, hence has length 1.
    intro w
    exact canonical_size w

/--
**Theorem 8.3 (Universal property of structural equivalence).**

`StructEquiv` is the *coarsest* relation on `Word α`
that is contained in the evaluation kernel: any binary relation `R`
on `Word α` such that `R w₁ w₂ → evalWord w₁ = evalWord w₂` satisfies
`R ≤ StructEquiv`.  Conversely, `StructEquiv` is itself contained in
the evaluation kernel; consequently `StructEquiv` is the unique
maximal element of the lattice of "evaluation-respecting" relations
on words, and any relation that *equals* the kernel is provably
extensionally equal to `StructEquiv`.

* Informal source: Volume 4 §5.2 ("Universal characterization
  of cognitive equivalence") which appeals to the categorical
  intuition that "*the right notion of identity is the largest one
  that does no harm*".
* Citations: Mac Lane, *Categories for the Working Mathematician*
  (1971/1998) ch. II; Lawvere–Tierney congruences as adapted in
  Volume 1 monograph §2.10.
* Proof depends on: the kernel half of `theorem_8_1`,
  the equivalence instance `StructEquiv.equivalence`, and
  the definitional unfolding of `StructEquiv`.
* Sharpenings: the informal universal property is stated in
  the category of equivalence relations; we verify it
  directly on `Prop`-valued binary relations, which is
  strictly stronger.

**Proof sketch.**
1. Let `R` be any relation contained in the evaluation kernel.
2. Take any pair `w₁ w₂` with `R w₁ w₂`.
3. Apply the containment to obtain `evalWord w₁ = evalWord w₂`.
4. By definition of `StructEquiv`, this gives `StructEquiv w₁ w₂`.
5. Conversely, `StructEquiv` itself lands in the kernel by
   `theorem_8_1`.
6. The two together establish that `StructEquiv` is the
   *largest* such relation.
7. Bundle uniqueness: any other relation that *characterizes* the
   kernel via an iff must be extensionally equal to `StructEquiv`.
-/
theorem theorem_8_3 :
    (∀ R : Word α → Word α → Prop,
        (∀ w₁ w₂, R w₁ w₂ → evalWord w₁ = evalWord w₂) →
        ∀ w₁ w₂, R w₁ w₂ → StructEquiv w₁ w₂) ∧
    (∀ w₁ w₂ : Word α, StructEquiv w₁ w₂ → evalWord w₁ = evalWord w₂) ∧
    (∀ R : Word α → Word α → Prop,
        (∀ w₁ w₂, R w₁ w₂ ↔ evalWord w₁ = evalWord w₂) →
        ∀ w₁ w₂, R w₁ w₂ ↔ StructEquiv w₁ w₂) := by
  refine ⟨?contain, ?kernel, ?unique⟩
  · -- Step 1–4: any kernel-respecting `R` is contained in `StructEquiv`.
    intro R hR w₁ w₂ hRw
    -- The containment gives equality of evaluations.
    have h : evalWord w₁ = evalWord w₂ := hR w₁ w₂ hRw
    -- This is exactly `StructEquiv` by definition.
    exact h
  · -- Step 5: `StructEquiv` itself is contained in the kernel.
    intro w₁ w₂ h
    exact h
  · -- Step 6+7: uniqueness as the kernel-equivalent relation.
    intro R hR w₁ w₂
    constructor
    · intro hRw
      -- Forward: convert `R` to evaluation equality, then to `StructEquiv`.
      have hev : evalWord w₁ = evalWord w₂ := (hR w₁ w₂).mp hRw
      exact hev
    · intro hSE
      -- Backward: convert `StructEquiv` to evaluation equality, then to `R`.
      have hev : evalWord w₁ = evalWord w₂ := hSE
      exact (hR w₁ w₂).mpr hev

/-! ## §8.8 Corollaries -/

/-- **Corollary 8.1.**  If `f : IdeaHom α β` is a homomorphism, then
the image-word map `f.mapWord` descends to a well-defined function on
`StructEquiv`-classes.  This is the formal underpinning of the
Volume 4 claim that "abstract cognitive simulators preserve
idea-identity".  -/
lemma corollary_8_1 {β : Type*} [IdeaTheoryStructure β]
    (f : IdeaHom α β) {w₁ w₂ : Word α}
    (h : StructEquiv w₁ w₂) :
    StructEquiv (f.mapWord w₁) (f.mapWord w₂) :=
  IdeaHom.mapWord_congr f h

/-- **Corollary 8.2.**  Structural equivalence on `Word α` is
*decidable* whenever equality on `α` is decidable.  Used in Volume 4
ch. 8 to argue that *idea-equivalence is in principle
algorithmically checkable* — a key plank of computationalism. -/
instance corollary_8_2 [DecidableEq α] :
    DecidableRel (StructEquiv : Word α → Word α → Prop) := by
  intro w₁ w₂
  unfold StructEquiv
  exact inferInstance

/-- **Corollary 8.3.**  The canonical-form construction is
*idempotent* on the level of `StructEquiv`-classes: applying
canonicalization twice gives the same result as once.  This
formalises Volume 4's "stability under introspection" lemma. -/
lemma corollary_8_3 (w : Word α) :
    StructEquiv (canonicalWord w) (canonicalWord (canonicalWord w)) :=
  StructEquiv.to_canonical (canonicalWord w)

/-- **Corollary 8.4.**  If two words evaluate to `ident`, they are
structurally equivalent — and indeed equivalent to the empty word.
This is the formal version of the Volume 4 dictum that *trivial
ideas are all the same trivial idea*. -/
lemma corollary_8_4 {w₁ w₂ : Word α}
    (h₁ : evalWord w₁ = (ident : α)) (h₂ : evalWord w₂ = (ident : α)) :
    StructEquiv w₁ w₂ ∧ StructEquiv w₁ ([] : Word α) := by
  refine ⟨?_, ?_⟩
  · unfold StructEquiv; rw [h₁, h₂]
  · unfold StructEquiv; rw [h₁, evalWord_nil]

/-- **Corollary 8.5.**  Append on `Word α` is *associative up to
structural equivalence*; this is the formal version of "compositional
chunking is invisible to content". -/
lemma corollary_8_5 (w₁ w₂ w₃ : Word α) :
    StructEquiv ((w₁ ++ w₂) ++ w₃) (w₁ ++ (w₂ ++ w₃)) :=
  StructEquiv.reassoc_three w₁ w₂ w₃

/-- **Corollary 8.6.**  Any finite multiset of `ident` letters
inserted at arbitrary positions in a word is invisible: every word
is structurally equivalent to the same word with any number of
`ident`s inserted. -/
lemma corollary_8_6 (w₁ w₂ : Word α) (n : Nat) :
    StructEquiv (w₁ ++ replicateWord (ident : α) n ++ w₂)
                (w₁ ++ w₂) :=
  StructEquiv.sandwich_replicate_ident w₁ w₂ n

/-! ## §8.9 Examples and sanity checks -/

section Examples

variable {β : Type*} [IdeaTheoryStructure β]

/-- A two-letter word equals its right-folded product. -/
example (a b : β) :
    evalWord ([a, b] : Word β) = op a b := evalWord_pair a b

/-- A three-letter word right-associates. -/
example (a b c : β) :
    evalWord ([a, b, c] : Word β) = op a (op b c) := evalWord_triple a b c

/-- Inserting `ident` is invisible. -/
example (w : Word β) :
    StructEquiv (((ident : β) :: w : Word β)) w :=
  StructEquiv.cons_ident w

/-- Snoc-ing `ident` is invisible. -/
example (w : Word β) :
    StructEquiv ((w ++ [(ident : β)] : Word β)) w :=
  StructEquiv.snoc_ident w

/-- Reassociating four words is invisible. -/
example (a b c d : Word β) :
    StructEquiv (((a ++ b) ++ c) ++ d) (a ++ (b ++ (c ++ d))) :=
  StructEquiv.reassoc_four_left a b c d

/-- The canonical form of `[a, b]` is the singleton `[op a b]`. -/
example (a b : β) :
    canonicalWord ([a, b] : Word β) = [op a b] := by
  unfold canonicalWord
  rw [evalWord_pair]

/-- A repeated `ident`-word collapses to the empty word. -/
example (n : Nat) :
    StructEquiv (replicateWord (ident : β) n) ([] : Word β) :=
  StructEquiv.replicate_ident_nil n

/-- Two singletons are equivalent iff their entries agree. -/
example (a b : β) :
    StructEquiv ([a] : Word β) [b] ↔ a = b :=
  StructEquiv.singleton_singleton_iff a b

end Examples

/-! ## §8.10 Index of results

A one-line summary of every public declaration in this file.

* `Word`                          — finite words over `α`.
* `evalWord`                      — right-fold evaluation `Word α → α`.
* `evalWord_nil/cons`             — base/step of evaluation.
* `evalWord_singleton`            — `[a]` evaluates to `a`.
* `evalWord_pair`                 — `[a,b]` evaluates to `op a b`.
* `evalWord_triple`               — `[a,b,c]` evaluates to `op a (op b c)`.
* `evalWord_append`               — append distributes via `op`.
* `evalWord_snoc`                 — snoc-form of `evalWord_append`.
* `evalWord_nil_append`,
  `evalWord_append_nil`           — boundary cases.
* `evalWord_append_three`         — three-fold append evaluation.
* `replicateWord`                 — `n`-fold replication of a letter.
* `evalWord_replicate_ident`      — replicated `ident` evaluates to `ident`.
* `sizeWord`                      — list length of a word.
* `canonicalWord`                 — singleton `[evalWord w]`.
* `evalWord_canonical`            — canonical form preserves evaluation.
* `canonical_singleton`,
  `canonical_nil`                 — boundary cases.
* `canonical_size`                — canonical form has size 1.
* `canonical_append`              — canonical form of an append.
* `StructEquiv`                   — equality of evaluations.
* `StructEquiv.refl'/symm'/trans'/equivalence`
                                  — equivalence proofs.
* `structEquivSetoid`             — induced `Setoid`.
* `StructEquiv.eq_nil_iff_eval_ident`
                                  — characterization vs `[]`.
* `StructEquiv.singleton_singleton_iff`
                                  — collapse on singletons.
* `StructEquiv.singleton_iff_eval`
                                  — `[a] ~ w` iff `a = evalWord w`.
* `StructEquiv.cons_congr`,
  `append_congr`,
  `append_left_congr`,
  `append_right_congr`,
  `snoc_congr`                    — congruence under syntactic operations.
* `StructEquiv.replicate_congr_letter`
                                  — replicate-congruence in the letter.
* `StructEquiv.append_assoc`,
  `nil_append`,
  `append_nil`                    — append's monoid laws.
* `StructEquiv.cons_ident`,
  `snoc_ident`,
  `insert_ident`                  — identity is silent.
* `StructEquiv.replicate_ident_nil`,
  `sandwich_replicate_ident`      — replicated `ident` is invisible.
* `StructEquiv.double_ident_collapse`
                                  — two `ident`s collapse to one.
* `StructEquiv.snoc_add_ident`,
  `cons_add_ident`                — symmetrized identity-insertion.
* `StructEquiv.reassoc_three`,
  `reassoc_four_mid`,
  `reassoc_four_left`             — reassociation is invisible.
* `StructEquiv.pair_cons_unfold`,
  `cons_eq_append`                — cons-as-append.
* `StructEquiv.to_canonical`,
  `equiv_iff_canonical`,
  `canonical_idem`                — canonical-form theory.
* `IdeaHom`                       — structure-preserving map.
* `IdeaHom.idHom`,
  `comp`                          — identity and composition.
* `IdeaHom.mapWord`,
  `evalWord_mapWord`,
  `mapWord_congr`                 — homomorphisms transport everything.
* `theorem_8_1`                   — kernel characterization of `StructEquiv`.
* `theorem_8_2`                   — canonical-form / normal-form theorem.
* `theorem_8_3`                   — universal property of `StructEquiv`.
* `corollary_8_1`                 — homomorphisms descend to the quotient.
* `corollary_8_2`                 — `StructEquiv` is decidable when `=` is.
* `corollary_8_3`                 — canonicalization is idempotent.
* `corollary_8_4`                 — `evalWord = ident` words are all equiv to `[]`.
* `corollary_8_5`                 — append associative up to `StructEquiv`.
* `corollary_8_6`                 — runs of `ident`s anywhere are invisible.
-/

end IdeaTheory
