# Idea Theory --- shared framework brief (read this before writing any chapter)

This brief defines the formal vocabulary used throughout the monograph
**"The Ideas About Ideas Zoo: A Formal Reconstruction"**. Every chapter must
use these axioms and notation when formalizing claims from the literature.

## 1. Primitive structure

An **idea algebra** is a tuple $(\Ideas,\compose,\unit,\rho,\preserve,\negate,\emerg,\deg)$ where:

- $\Ideas$ is a set, the **carrier**; its elements are *ideas*.
- $\compose:\Ideas\times\Ideas\to\Ideas$ is the **composition** operation,
  satisfying associativity and a two-sided identity $\unit$ ("the empty idea").
  Thus $(\Ideas,\compose,\unit)$ is a monoid.
- $\rho:\Ideas\times\Ideas\to\RR$ is the **resonance pairing**: a bilinear
  form measuring the affinity (positive) or tension (negative) between two
  ideas. In general $\rho$ is **not symmetric**; its antisymmetric part is
  the **meaning curvature**.
- $\preserve,\negate:\Ideas\to\Ideas$ are the **preservation** and
  **negation** projections, supplying the **Aufhebung decomposition**
  $a\compose b = \preserve(a,b)+\negate(a,b)+\elevate(a,b)$
  where $\elevate$ is the **elevation** (synthesis / sublation) term.
- $\emerg:\Ideas\times\Ideas\to A$ is the **emergence 2-cocycle** valued in
  some abelian group $A$ (typically $\RR$ or $\ZZ$); it satisfies the
  cocycle identity $\dcoc\emerg=0$ and measures the failure of a chosen
  valuation $v:\Ideas\to A$ to be a homomorphism:
  $v(a\compose b) = v(a)+v(b)+\emerg(a,b)$.
- $\deg:\Ideas\to G$ is a **grading** into a totally ordered abelian group $G$,
  compatible with $\compose$ when defined.

When only some of this data is needed, the relevant *sub-structure* is named.
For example a **bare** idea algebra means just $(\Ideas,\compose,\unit)$.

## 2. The nine foundational theorems (proved in Lean; cite, do not re-prove)

| # | Name                          | One-line statement                                                                                                                |
|---|-------------------------------|-----------------------------------------------------------------------------------------------------------------------------------|
| 1 | Composition Theorem           | $(\Ideas,\compose,\unit)$ is a monoid; identity is unique; cancellation holds for invertible ideas.                              |
| 2 | Resonance Pairing Theorem     | $\rho$ extends uniquely to a bilinear form on the free vector space on $\Ideas$; non-degeneracy is preserved by composition.    |
| 3 | Aufhebung Theorem             | The decomposition $a\compose b = \preserve+\negate+\elevate$ exists and is unique modulo the kernel of $\rho$.                  |
| 4 | Emergence Cocycle Theorem     | $\emerg$ is a normalized 2-cocycle: $\dcoc\emerg=0$ and $\emerg(\unit,a)=\emerg(a,\unit)=0$.                                    |
| 5 | Curvature Theorem             | The antisymmetric part of $\rho$ is a closed 2-form whose cohomology class is invariant under structural equivalence.            |
| 6 | Conjugation Theorem           | Invertible ideas act by inner automorphism preserving $\rho$, the Aufhebung decomposition, and $\emerg$.                         |
| 7 | Transmission Chain Theorem    | Iterated composition along a chain $a_1,\dots,a_n$ admits a closed-form telescoping in $\emerg$.                                |
| 8 | Structural Equivalence Theorem| Two idea algebras are isomorphic iff there is a graded monoid iso preserving $\rho$, the Aufhebung data, and $\emerg$.          |
| 9 | Grading Theorem               | $\deg$ extends to a homomorphism into $G$; the resulting grading respects $\rho$, the Aufhebung decomposition, and $\emerg$.    |

## 3. Style requirements for every zoo chapter

Each chapter formalizes a cluster of historical / scientific positions about ideas.
For **every** entry produce:

1. **Original claim.** A faithful 1--3 paragraph reconstruction of the thinker's
   position about ideas/concepts/representations, *with citations* to
   `references.bib`.
2. **Formal restatement.** Express the claim using the vocabulary of §1. Be
   precise: every informal noun ("synthesis", "association", "blending",
   "spillover") must be tied to an operator ($\compose$, $\rho$, $\preserve$,
   $\elevate$, etc.) or to a derived predicate.
3. **Status in Idea Theory.** State which of the nine foundational theorems
   (or their corollaries) makes the formalized claim true / false / contingent.
   When proving a corollary is needed, give the *math-prose* proof. Do **not**
   include any Lean code in the body --- write proofs as ordinary mathematics.
4. **Commentary.** A short paragraph noting where the formalization is
   faithful, where it diverges, and what it predicts that the original did
   not.

## 4. Bibliography

Add new BibTeX entries to `references.bib` as you go. Use real citations.
Cite at least 6 distinct works per chapter.

## 5. Output

Each chapter is a self-contained `.tex` file in `chapters/`, beginning with
`\chapter{...}` and ending with no `\end{document}`. It will be `\input`'d
from `book.tex`.

## 6. Length

Word target per chapter is given in the dispatch prompt. **Hit the target.**
No filler --- substance only.
