---
name: openga-math-review
description: Guide a pure-math contributor through reviewing do Carmo atoms. Use when the user says "review next atom", "math review", "check OCR", "review chX:Y.Z", or similar.
---

# OpenGA Math Review Skill

## Goal

Verify a single do Carmo atom is mathematically correct and well-bound, then record the review.

## Workflow

1. Read `projects/riemannian-geometry/tasks/pilot.tasks.yaml` to find a leaf task with `checks.math_review != done`.
2. Identify its atom file (`files.atom`) and read it.
3. Also read `projects/riemannian-geometry/tasks/atom-boundary-review.md` to see if this atom is flagged.
4. Ask the user:
   - Is the statement mathematically correct?
   - Are there hidden hypotheses or notation issues?
   - Does the proof end cleanly, or does text after `\square` belong to the next item?
5. If edits are needed, use the review app or edit the atom file directly. If the review app is involved, run `npx tsc --noEmit && npm run build` in `apps/review/`.
6. Record the review by marking `math_review: done` (or `pending` if problems remain) and adding a note to `review_notes`.
7. Inspect `git diff` before finishing.

## What NOT to do

- Do not modify Lean files.
- Do not create new `dcref` atoms during correction-only review.
- Do not move atom boundaries without noting the change in a review note.

## Boundaries to watch

- Text after `\square` or `\blacksquare` that introduces a new numbered item is likely a boundary error.
- Descriptions truncated mid-word in `pilot.tasks.yaml` are a known generation issue; fix the YAML description only if it misleads navigation.
