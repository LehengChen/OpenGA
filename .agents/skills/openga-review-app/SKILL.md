---
name: openga-review-app
description: Work with the OpenGA pilot review app in apps/review/. Use when the user wants to run, modify, or debug the review app, task views, atom editor, or review state.
---

# OpenGA Review App Skill

## Project context

- Source: `apps/review/`
- Dev command: `cd apps/review && npm run dev` (Vite on http://localhost:5173, API on http://localhost:3001)
- Build / typecheck: `npx tsc --noEmit && npm run build`
- Canonical task list: `projects/riemannian-geometry/tasks/pilot.tasks.yaml`
- Generated JSON for the build: `apps/review/src/data/pilot.tasks.json` — do NOT hand-edit; the backend writes it.
- Atoms: `projects/riemannian-geometry/.astrolabe/atoms/<hash>.md`
- Schema / helpers: `apps/review/src/lib/taskSchema.ts`, `apps/review/src/lib/progress.ts`

## Common tasks

### Start the app
```bash
cd apps/review && npm run dev
```

### Review a task by ID
1. Read `projects/riemannian-geometry/tasks/pilot.tasks.yaml` and find the leaf task.
2. Read its atom file.
3. Guide the user through the math review; optionally edit the atom source.
4. Submit via the UI or API `POST /api/tasks/:id/review`.
5. After a successful submit, the backend writes the atom (if edited) and updates YAML/JSON. Inspect `git diff`.

### Add a feature or fix a bug
1. Edit TypeScript / CSS in `apps/review/src/` or server code in `apps/review/server/`.
2. Run `npx tsc --noEmit && npm run build`.
3. Run `npm run dev` and verify in the browser.
4. Do NOT commit unless the user explicitly asks.

## Safety

- Only write files inside `apps/review/` or task-whitelisted atom/docs paths.
- Do not edit `apps/review/src/data/pilot.tasks.json` directly.
- Do not write to `.astrolabe/edges/`, `.astrolabe/docs/`, or arbitrary repo files.
