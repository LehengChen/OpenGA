# OpenGA — Agent Instructions

## Project Overview

OpenGA is a public initiative to turn Riemannian geometry into a living, machine-verified textbook. Main areas:

- `OpenGALib/` — Lean 4 library.
- `web/` — Astrolabe visualizer (Next.js). Also read `web/AGENTS.md` when working here.
- `apps/review/` — Local pilot review app (Vite + Express).
- `projects/riemannian-geometry/` — do Carmo atoms, chapter docs, task roadmap.
- `tools/` — Python / Lean scripts for store management and audit.

## Communication

Respond to the user in Chinese unless they explicitly ask for another language.

## Safety Rules

1. Do NOT run `git commit`, `git push`, `git rebase`, or destructive git mutations unless the user explicitly asks.
2. Treat the user's fork (`origin`) as the sandbox; `upstream` (`LehengChen/OpenGA`) is the public working fork. Do not clone or fork from `MathNetwork/OpenGA` for day-to-day work.
3. Do NOT commit binary artifacts, API keys, `.env`, or the `doCarmo-*.zip` archive.
4. Do NOT add AI attribution lines such as `Co-Authored-By`.
5. On a fresh clone, activate the commit-msg hook: `git config core.hooksPath .githooks`.

## Validation Commands

- Review app (`apps/review/`): `npm install` → `npm run dev` → check with `npx tsc --noEmit && npm run build`.
- Lean (`OpenGALib/`): `lake exe cache get && lake build`. Keep CI `sorry` = 35 and `axiom` = 0 stable.
- Astrolabe store: validate with `tools/astrolabe_store.py` after edits.

## Newcomer Onboarding

If the user has not cloned the repo yet, follow the copy-paste prompt in `docs/OPENGA_SETUP_PROMPT.md` to clone and set everything up.
