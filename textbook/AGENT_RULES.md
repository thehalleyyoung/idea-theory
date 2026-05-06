# Strict rules for all chapter-writing agents

These rules apply to every chapter file you produce.

## TTS-friendliness — strict

1. **No LaTeX, no math delimiters at all.** Do not use `\(` `\)` `\[` `\]` `$` `$$` or `&` `&lt;` `&gt;` markup. The output must be plain markdown that reads aloud cleanly.
2. **No mathematical symbols.** Do not use `→` `↦` `⊆` `∈` `∉` `∀` `∃` `∧` `∨` `¬` `≠` `≤` `≥` `≡` `≅` `⊗` `⊕` `∘` `≃` `↔` etc. Spell out the relation in English: "is mapped to," "is contained in," "is an element of," "for all," "there exists," "and," "or," "not," "is not equal to," etc.
3. **Greek letters: introduce once by role, then use the role name.**
   - On first reference within a chapter, write: "the horizon functor — the rule mathematicians label with the Greek letter xi —" once, then refer to it as "the horizon functor" thereafter.
   - For the standard core: composition, identity, **resonance pairing**, **preservation part** (instead of sigma), **suppression part** (instead of nu), **emergence part** (instead of eta), **emergence cocycle** (instead of omega), **degree** or **grading** (instead of deg), **horizon category** (instead of script H), **horizon functor** (instead of xi).
   - **Meaning curvature** (instead of kappa) — never confuse with horizon functor.
   - Derived primitives: **temporality, intentionality, perspective, affect (or conatus), differentiation, rigid reference, potentiality, schema (or paradigm), credence, signed valence, reflexion**.
4. **Theorems are stated in three voices, in this order**, with no symbols anywhere:
   - **Headline** (one sentence, italicized in markdown using single asterisks).
   - **Paragraph form** (one paragraph explaining what the theorem rules out and what it predicts).
   - **Careful semi-formal restatement** (one paragraph naming every structural element by its English role-name).
5. **Repetition is welcomed.** Open each chapter with a brief reminder of the operating definitions you need; close with a one-paragraph summary.
6. **Figures are described, not drawn.** Where you would otherwise show a diagram, describe it in words.
7. **Pronunciation glosses.** First time a non-English name appears, give a phonetic English approximation in italics.

## Length

Each chapter must be approximately **1000 to 1600 words** of substantive prose (excluding the H1 title). Aim for the higher end on chapters about major figures or theorems; the lower end on small structural chapters.

## Format — strict

Every chapter file is a single markdown file with this skeleton:

```markdown
# Chapter NN — Title

(opening paragraph, no fluff, hooks the listener)

## Section heading one

(prose)

## Section heading two

(prose)

(optional further sections)

## Chapter summary

(one short paragraph)
```

Use H1 for the chapter title, H2 for sections, H3 sparingly. No tables. No bullet lists in the body unless needed for genuine enumeration; even then keep them short and TTS-friendly.

## Voice and style

- Warm, intellectually generous, second person occasional ("you", "the listener").
- Avoid academic hedging chains.
- Concrete examples wherever possible.
- For thinker chapters, the biographical preamble is one short paragraph including: dates of life, place, tradition, a single sentence in their own translated words.

## What you must NOT do

- Do not write meta-commentary about the chapter's role in the book.
- Do not put XML or HTML in the markdown.
- Do not use code blocks, tables, or images.
- Do not refer to "Chapter X above" or "Chapter Y below" — use "as we discussed when we introduced resonance" or "as we will see when we come to Hegel."
- Do not include any `\(`, `$`, mathematical symbols, or arrows.
