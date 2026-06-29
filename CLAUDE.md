# OpenGA — Claude Code Project Instructions

## Project Overview

OpenGA is a public initiative to turn Riemannian geometry into a living, machine-verified textbook. The repo has four main areas:

- `OpenGALib/` — Lean 4 library (Algebraic, Tensor, MetricGeometry, Riemannian, Comparison, GMT).
- `web/` — Astrolabe knowledge-network visualizer (Next.js + React). Also read `web/CLAUDE.md` when working here.
- `apps/review/` — Local pilot review app for task/atom review (Vite + Express).
- `projects/riemannian-geometry/` — do Carmo atoms, chapter docs, and the task roadmap.
- `tools/` — Python / Lean scripts for store management, extraction, audit, and graph registration.

## Communication

Respond to the user in Chinese unless they explicitly ask for another language.

## Safety & Workflow Rules

1. Do NOT run `git commit`, `git push`, `git rebase`, or any destructive git mutation unless the user explicitly asks.
2. Treat the user's fork (`origin`, e.g. `LehengChen/OpenGA`) as the sandbox; `upstream` (`MathNetwork/OpenGA`) is only for reviewed PRs.
3. Do NOT commit binary artifacts, API keys, `.env`, or the `doCarmo-*.zip` archive.
4. Do NOT add AI attribution lines such as `Co-Authored-By`.
5. On a fresh clone, activate the commit-msg hook: `git config core.hooksPath .githooks`.
6. When working in `web/`, also read and follow `web/CLAUDE.md`.

## Per-Subsystem Validation

### Review app (`apps/review/`)

- Install: `cd apps/review && npm install`
- Dev: `cd apps/review && npm run dev` (Vite on http://localhost:5173, API on http://localhost:3001)
- Check: `npx tsc --noEmit && npm run build`

### Lean library (`OpenGALib/`)

- Needs `elan` (Lean toolchain manager).
- Build: `lake exe cache get && lake build`
- Keep CI counts stable: `sorry` = 35, `axiom` = 0 (see `.github/workflows/ci.yml`). If you add/close a `sorry`, update the `EXPECTED` constant and `docs/SORRY_CATALOG.md`, and add a closure plan in the docstring.

### Astrolabe store (`projects/riemannian-geometry/.astrolabe/`)

- Validate after edits:
  ```bash
  python3 -c "import sys; sys.path.insert(0,'tools'); from astrolabe_store import AstrolabeStorage, validate_store; validate_store(AstrolabeStorage('projects/riemannian-geometry').all_entries())"
  ```
- Preserve `dcref` identities during correction-only runs. Do not regenerate hashes unless you are intentionally migrating the graph.

## Role Routing

Use the built-in skills when the user asks for these tasks:

- "review app", "review task", "atom edit", "pilot app" → type `/openga-review-app`
- "math review", "review atom", "check OCR" → type `/openga-math-review`
- "Lean", "formalize", "sorry" → type `/openga-lean-formalize` (create if missing)
- "next task", "what should I do" → type `/openga-task-router` (create if missing)

If the repository has not been cloned yet, install the bootstrap skill and run `/openga-bootstrap`:

```bash
bash <(curl -fsSL https://raw.githubusercontent.com/LehengChen/OpenGA/main/tools/openga/install-skills.sh) claude
```

Then ask Claude: "setup OpenGA".
