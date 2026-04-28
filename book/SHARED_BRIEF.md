# SHARED BRIEF — Idea Theory monograph project

You are part of a parallel team building a monograph (PDF book) called
**"Idea Theory: A Mathematical Formalism for the Zoo of Ideas About Ideas"**,
together with a companion website and Lean 4 extensions. This brief is the
single source of truth for the formalism. **Read it before doing anything.**

---

## 1. The formalism (use this notation everywhere)

An **idea algebra** is a tuple $(\Ideas,\compose,\unit,\rho,\sigma,\nu,\eta,\omega,\deg)$:

* $\Ideas$ — the carrier set; elements are *ideas*.
* $\compose : \Ideas\times\Ideas \to \Ideas$ — **composition**, with a two-sided
  identity $\unit$ and associativity. So $(\Ideas,\compose,\unit)$ is a monoid.
* $\rho : \Ideas\times\Ideas \to \mathbb{R}$ — the **resonance pairing**;
  bilinear after extending $\Ideas$ to its free $\mathbb{R}$-vector space.
  In general $\rho$ is **not symmetric**; the antisymmetric part defines the
  **meaning curvature** $\kappa$.
* $\sigma,\nu,\eta : \Ideas\times\Ideas \to \Ideas$ — the **Aufhebung
  decomposition**: $a\compose b = \sigma(a,b) + \nu(a,b) + \eta(a,b)$
  (preservation, negation, elevation/synthesis), unique up to the kernel of $\rho$.
* $\omega : \Ideas\times\Ideas \to A$ — the **emergence 2-cocycle** (with $A$
  abelian); satisfies the cocycle identity $\partial\omega = 0$ and is normalized:
  $\omega(\unit,a)=\omega(a,\unit)=0$. Measures the failure of a valuation
  $v:\Ideas\to A$ to be a homomorphism: $v(a\compose b) = v(a)+v(b)+\omega(a,b)$.
* $\deg : \Ideas \to G$ — a **grading** into a totally ordered abelian group $G$.

A **bare** idea algebra means just $(\Ideas,\compose,\unit)$.

## 2. The nine foundational theorems (already proven in Lean)

| # | Name                          | Statement                                                                                      |
|---|-------------------------------|------------------------------------------------------------------------------------------------|
| 1 | Composition                   | $(\Ideas,\compose,\unit)$ is a monoid; identity unique; cancellation for invertibles.          |
| 2 | Resonance Pairing             | $\rho$ extends uniquely to a bilinear form; non-degeneracy preserved by composition.           |
| 3 | Aufhebung Decomposition       | $a\compose b=\sigma+\nu+\eta$ exists and is unique mod $\ker\rho$.                            |
| 4 | Emergence Cocycle             | $\omega$ is a normalized 2-cocycle: $\partial\omega=0$, $\omega(\unit,\cdot)=0$.              |
| 5 | Curvature                     | The antisymmetric part of $\rho$ is closed; its cohomology class is a structural invariant.   |
| 6 | Conjugation                   | Invertible ideas act by inner automorphism preserving $\rho$, the Aufhebung data, $\omega$.   |
| 7 | Transmission Chain            | Iterated composition telescopes via $\omega$.                                                  |
| 8 | Structural Equivalence        | Two algebras are isomorphic iff there is a graded monoid iso preserving $\rho,\sigma,\nu,\omega$. |
| 9 | Grading                       | $\deg$ extends to a hom into $G$ compatible with $\rho$, Aufhebung, $\omega$.                 |

(Proofs are machine-checked under `lean/IdeaTheory/Foundations.lean` and
`lean/IdeaTheory/Theorems{1..12}.lean`. Cite them; do **not** reproduce Lean
code in any prose document.)

## 3. The "ideas zoo"

The book is **centered on the formalism**, but every chapter contextualizes
the math through entries from the *zoo* — historical/scientific positions
about ideas. Each zoo entry has the structure:

> **Original claim.** Faithful reconstruction of the position, with citations.
>
> **Formal restatement.** Translate into the vocabulary of §1.
>
> **Status.** Which of the nine theorems (or new theorems below) makes it
> true / false / contingent. If a corollary is needed, prove it in math prose.
>
> **Commentary.** Where the formalization is faithful, where it diverges,
> what new predictions emerge.

Sample zoo populations (chapters subset and elaborate these):

* **Ancient/medieval.** Plato (Forms as fixed points of composition), Aristotle
  (universals as $\sigma$-invariants), Augustine, Aquinas (species
  intelligibilis).
* **Early modern.** Descartes (innate vs. adventitious), Locke (simple/complex
  ideas as monoid generators), Berkeley, Hume (association as resonance),
  Spinoza, Leibniz (monads as graded atoms).
* **German idealism.** Kant (categories as schematic operators), Fichte,
  Schelling, Hegel (Aufhebung literally), Schopenhauer.
* **Phenomenology / hermeneutics.** Husserl (noema), Heidegger, Merleau-Ponty,
  Gadamer (fusion of horizons as $\eta$), Ricoeur.
* **Post-structuralism.** Deleuze (virtual problems), Derrida (différance as
  curvature), Foucault (épistémè as graded substructure), Kristeva
  (intertextuality as chain), Bakhtin (heteroglossia as non-symmetry of $\rho$).
* **Analytic.** Frege (sense), Russell, Wittgenstein I (picture / $\rho$ as
  isomorphism), Wittgenstein II (family resemblance as quotient), Quine,
  Putnam, Kripke, Fodor (LOT atoms), Davidson, Brandom (inferential commitment).
* **Cognitive science.** Classical theory, Rosch prototypes, theory-theory,
  Barsalou perceptual symbols, Fauconnier–Turner blending (literally $\eta$),
  Lakoff metaphor, Fillmore frames, Gärdenfors conceptual spaces, Smith &
  Osherson concept combination.
* **Connectionist / VSA.** Smolensky tensor binding, Plate HRR, Mikolov word
  embeddings, modern transformers (latent ideas as activation patterns).
* **Cultural evolution.** Dawkins memes, Sperber attractors, Boyd & Richerson
  dual inheritance, Henrich cultural ratchet, Mesoudi.
* **Sociology of ideas.** Lovejoy unit-ideas, Rogers diffusion, Granovetter
  weak ties, Bourdieu fields/habitus, Latour ANT, Skinner contextualism,
  Koselleck Begriffsgeschichte.
* **Economics.** Arrow (information as commodity), Hayek (dispersed
  knowledge), Romer (nonrival ideas as growth driver), Weitzman (recombinant
  growth), Jones, attention economy.
* **Game theory of ideas.** Ideas as strategies, mixed strategies as convex
  combinations in the free vector space, equilibria as resonance fixed
  points, evolutionary stability of memes.
* **Emergence.** Mill, Broad, Anderson "More is different", Bedau weak
  emergence (= $\omega$-bounded), Kim downward causation, Chalmers strong vs.
  weak (= cohomology nontriviality of $\omega$), O'Connor.

## 4. Style requirements

* **Math first**: definitions and theorems are first-class; prose justifies
  them. State results crisply (Theorem / Lemma / Proposition / Corollary).
* **Math-prose proofs only.** Absolutely no Lean code in the body. When
  citing a Lean-verified result, write *e.g.* "(verified as
  `IdeaTheory.theorem_3_1`)" — no listings.
* **Heavy citation.** Every chapter cites at least 8 distinct works from
  `references.bib` (extend the bib as needed; use real publications).
* **No filler.** Hit the word target; substance only.
* **Cross-references.** Use `\cref` / `\label`. Number theorems by chapter.
* **English math style** (American): "we have", "it follows", "without loss of
  generality".

## 5. Deliverables and locations

| Track       | Output                                                                    |
|-------------|----------------------------------------------------------------------------|
| Book        | Self-contained `chapters/chXX_name.tex` under `~/.copilot/session-state/b8a6ed3e-3900-442c-adca-240775c77216/files/book/chapters/` |
| Lean ext.   | New file `lean/IdeaTheory/Extensions/Name.lean` under `/Users/halleyyoung/Documents/formalize/idea-theory/lean/`. Must build with `lake build IdeaTheory.Extensions.Name`. **No `sorry`, no `admit`.** |
| Website     | Replace contents of `/Users/halleyyoung/Documents/formalize/idea-theory/docs/` |

`references.bib` lives at `~/.copilot/session-state/.../files/book/references.bib`.

## 6. Output rules per chapter file

* Begin with `\chapter{…}` followed by `\label{ch:…}`.
* Do **not** include `\documentclass`, preamble, or `\end{document}`.
* The master `book.tex` will set up the preamble (already at
  `~/.copilot/session-state/.../files/book/preamble.tex`) and `\input` your file.
* Hit the assigned word count (count math display equations as ~10 words each).
