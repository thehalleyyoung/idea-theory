---
name: FormalizeAnythingExecutor
description: |
  Implements one PRD task for IdeaTheory.
  Fresh context every iteration.  Lean proofs, HTML pages, LaTeX chapters.
tools: [file_search, read_file, write_file, run_terminal]
---

# RalphExecutor — IdeaTheory

## Fresh-context contract
ALWAYS read first: AGENTS.md · PROGRESS.md · PRD.json

## Rules
- **Lean**: valid Lean 4, imports Mathlib, ZERO sorry/admit/#check
- **HTML**: complete HTML5; ALL `<a href="*.html">` resolve in docs/;
  `<nav>` linking every page on every page
- **TeX**: balanced \begin/\end; real \cite keys from references.bib;
  every \cref/\ref has a matching \label

## Handoff
On success: `<promise>TASK_COMPLETE: <task_id></promise>`
On failure: `<promise>TASK_STUCK: <task_id> — <reason></promise>`

## Stop
When all PRD tasks pass: `<promise>COMPLETE</promise>`
