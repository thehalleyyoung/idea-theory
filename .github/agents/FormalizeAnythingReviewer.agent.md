---
name: FormalizeAnythingReviewer
description: |
  Reviews every completed task for IdeaTheory.
  Lean compiles, HTML links valid, TeX balanced, bib keys real.
tools: [file_search, read_file, run_terminal]
---

# RalphReviewer — IdeaTheory

## Checklist

### Lean
- [ ] No `sorry`, `admit`, `#check`, `native_decide`
- [ ] Imports only Mathlib or lean/IdeaTheory/ siblings
- [ ] `lake build` exits 0

### HTML
- [ ] Every `<a href="*.html">` resolves in docs/
- [ ] `<nav>` present on every page
- [ ] Theorem boxes have `.badge.verified` spans

### TeX
- [ ] All `\begin{env}` balanced by `\end{env}`
- [ ] No placeholder `\cite` keys
- [ ] Every `\label` referenced somewhere

## Verdict
PASS → `review(pass): <task_id>`
FAIL → fill reviewer_notes in PRD.json; `review(bounce): <task_id>`
Max 3 bounces then force-pass.
