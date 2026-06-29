# Riemannian Geometry Agent Collaboration Pilot

This document describes a small pilot for turning the do Carmo Riemannian
Geometry project into a collaborative workflow between:

- mathematics contributors who review natural-language meaning;
- Lean contributors who formalize statements and proofs;
- AI/tooling contributors who maintain task routing, progress reporting, and
  repository automation.

The goal of the pilot is not to formalize the whole book immediately. The
workflow goal is to prove that a single task can eventually move through the
whole loop:

```text
task card
-> math review
-> math verification
-> Lean statement/proof work
-> graph/formalizes integration
-> progress dashboard update
```

Once this loop is easy to repeat, we can scale it chapter by chapter.

The first roadmap/review-app milestone is narrower: build a trusted display of
tasks, hierarchy, dependencies, and progress from repository data. Do not require
the first version to complete the full closed loop or write source changes.

## Current Starting Point

The OCR cleanup pass for `projects/riemannian-geometry/.astrolabe` produced a
content-only branch:

```text
docarmo-ocr-astrolabe-revision
```

The branch updates existing do Carmo `.astrolabe` files. It does not add new do
Carmo atoms or change `dcref` identities.

For collaboration testing, use the personal fork first:

```text
https://github.com/LehengChen/OpenGA
```

The fork should be treated as a safe sandbox for issue templates, pilot task
cards, GitHub Projects, and agent skills.

## Decision: Build A Dedicated Review App

Do not modify the existing `web/` application for the pilot. The current web app
is the Astrolabe reader/visualizer. The review workflow should be developed as a
separate local application dedicated to task review, source editing, and progress
tracking:

```text
apps/review/
```

The review app is the main working surface for the pilot. GitHub remains the
collaboration ledger, but contributors should not need to begin by navigating the
full GitHub interface.

The app should expose the same task data through multiple views:

```text
List        flat queue for day-to-day task selection
Tree        chapter/section/task hierarchy
Dependency  prerequisite and blocked-by relationships
```

The first roadmap view should prioritize trustworthy read-only presentation over
closed-loop completion. It should make it obvious which data came from
`pilot.tasks.yaml`, which tasks are blocked, and which higher-level topic each
task belongs to.

The app should support a simple local loop:

```text
open review app
-> choose or receive a task
-> read the relevant atom/docs-src text
-> write a review note
-> optionally edit the source text directly
-> inspect the git diff
-> save progress
```

This app should use React with CSS Modules. A lightweight local Vite app is
preferred for the pilot because it is only a local workflow tool and does not
need server-side rendering.

## Decision: Source Edits Are Allowed, But Guarded

Directly editing the source data is allowed in the pilot. The repository is
already plain text, and Git is the right mechanism for tracking revisions.

However, the review app must not become an unrestricted file editor. Every task
card must declare its editable scope explicitly. The app may only edit files
listed in that task card.

Allowed pilot edit targets:

```text
projects/riemannian-geometry/.astrolabe/atoms/*.md
projects/riemannian-geometry/.astrolabe/docs-src/*.mdx
projects/riemannian-geometry/tasks/*.yaml
projects/riemannian-geometry/tasks/*.json
```

Disallowed in the first pilot:

```text
projects/riemannian-geometry/.astrolabe/edges/*
projects/riemannian-geometry/.astrolabe/docs/*
OpenGALib/**/*.lean
arbitrary repository files
```

The app should distinguish two editing modes:

```text
Review Note
  Writes a contributor's mathematical review to the task review data.

Source Edit
  Writes directly to the task's whitelisted atom/docs-src files.
```

Source edits must show a diff after saving. The first version should not
auto-commit. A human maintainer or agent should inspect the diff and commit with
normal Git.

Minimum safety checks after source edits:

```text
git diff --check
```

Later checks can add `.astrolabe` structural validation and atom/docs-src
synchronization checks.

## Pilot Principle

Start with a narrow, observable loop.

Do not begin by creating hundreds of issues. Do not ask contributors to learn the
whole repository. Do not require a pure math contributor to understand Lean or
Git internals before they can help.

Instead, each contributor should be able to answer:

```text
What is my next task?
What file or statement should I read?
What exact output should I produce?
Who takes the task after me?
How do we know the loop is complete?
```

## Roles

### Math Reviewer

The math reviewer checks the natural-language statement and proof.

Expected output:

- confirm whether the statement is mathematically correct;
- explain the mathematical idea in a short paragraph;
- identify hidden hypotheses or notation that Lean contributors need to know;
- flag whether the task is routine or conceptually valuable.

The math reviewer is not expected to write Lean.

### Lean Formalizer

The Lean formalizer starts from a math-verified task.

Expected output:

- create or update a Lean statement;
- identify relevant Mathlib/OpenGA APIs;
- either prove the result or add a documented `sorry` with a repair plan;
- connect the Lean declaration to the do Carmo atom when appropriate.

### AI/Tooling Maintainer

The AI/tooling maintainer keeps the loop repeatable.

Expected output:

- maintain task cards;
- generate or synchronize GitHub issues;
- maintain agent skills and one-line commands;
- generate progress summaries;
- detect stale or blocked tasks.

### Project Maintainer

The maintainer decides whether a task is accepted and when it moves to the next
stage.

Expected output:

- triage tasks;
- assign labels and project fields;
- merge PRs;
- prevent duplicate or conflicting work.

## Minimal Workflow

Each task should move through these statuses:

```text
Backlog
-> Math Review
-> Math Verified
-> Formalizing
-> Lean Review
-> Integrated
-> Done
```

A task is only `Done` when:

- math review is accepted;
- Lean work is merged or deliberately deferred with a documented reason;
- any `formalizes` edge or graph update is handled when applicable;
- progress data reflects the completed state.

## First Pilot Scope

Use three tasks that are mathematically meaningful and already well understood
from the OCR cleanup pass:

```text
RG-PILOT-001  ch5:2.4   Jacobi fields and the differential of exp
RG-PILOT-002  ch8:5.3   Isometries of H^2 and Mobius transformations
RG-PILOT-003  ch13:4.2  Radius estimates in the sphere theorem
```

These tasks are good pilot candidates because they are not merely typographical.
Each one exposes a mathematical idea that should eventually inform the
formalization strategy.

## Task Card Model

The repository should contain a machine-readable task list:

```text
projects/riemannian-geometry/tasks/pilot.tasks.yaml
```

Suggested schema:

```yaml
tasks:
  - id: RG-PILOT-001
    dcref: ch5:2.4
    atom: projects/riemannian-geometry/.astrolabe/atoms/c944a1ee39aa.md
    docs_src: projects/riemannian-geometry/.astrolabe/docs-src/05-jacobi.mdx
    chapter: 5
    title: Jacobi field from variation of exp map
    status: Backlog
    next_role: math
    difficulty: Medium
    insight: High
    formalization_risk: ExpMapAPI
    hierarchy:
      parent: RG-CH05-JACOBI
      order: 1
    dependencies:
      depends_on: []
      blocks:
        - RG-PILOT-001-LEAN
    github:
      issue: null
      pr: null
    editable:
      atoms:
        - projects/riemannian-geometry/.astrolabe/atoms/c944a1ee39aa.md
      docs_src:
        - projects/riemannian-geometry/.astrolabe/docs-src/05-jacobi.mdx
      task_data:
        - projects/riemannian-geometry/tasks/pilot.tasks.yaml
        - projects/riemannian-geometry/tasks/pilot.reviews.json
    checklist:
      math_review_claimed: false
      math_review_submitted: false
      math_verified: false
      lean_statement_pr: false
      lean_proof_or_sorry_plan: false
      formalizes_edge_checked: false
      audit_passed: false
```

## Task Hierarchy And Dependency Model

Task cards support both a hierarchy and a dependency graph. These are separate
models:

```text
Hierarchy   where the task lives in the book/project structure
Dependency  what must be understood, reviewed, or built before another task
```

The hierarchy should be used for roadmap navigation and Tree view grouping. A
task may have a parent topic such as a chapter, section, theorem cluster, or
Lean milestone. Parent nodes may be represented as normal task cards when they
need status, ownership, or progress, but they can also begin as display-only
grouping IDs.

The dependency graph should be used for handoff and blocked-state explanation.
`depends_on` lists prerequisites for the current task. `blocks` lists downstream
tasks that cannot sensibly proceed until the current task is handled. A task can
appear in the hierarchy without dependencies, and it can have dependencies that
cross chapter or role boundaries.

The main repository source data is the task YAML file:

```text
projects/riemannian-geometry/tasks/pilot.tasks.yaml
```

Review app views, roadmap displays, scripts, GitHub issues, and AI/subagent
workflows should read from or synchronize against this file. AI agents and
subagents may provide different workflow surfaces for math review, Lean
formalization, progress reporting, or task routing, but they must not introduce
a second source of truth for task structure.

Review outputs should be stored separately from task definitions:

```text
projects/riemannian-geometry/tasks/pilot.reviews.json
```

Example review record:

```json
{
  "RG-PILOT-001": {
    "verdict": "accept",
    "math_review": "The scaling v'(0)=aw is forced by the parametrization.",
    "lean_hints": "The Lean task will need the differential of exp and Jacobi fields.",
    "updated_at": "2026-06-29T00:00:00Z"
  }
}
```

## Review App Shape

The pilot review app should live at:

```text
apps/review/
```

Suggested structure:

```text
apps/review/
  package.json
  vite.config.ts
  tsconfig.json
  src/
    main.tsx
    App.tsx
    App.module.css
    components/
      TaskList.tsx
      TaskDetail.tsx
      SourceEditor.tsx
      ReviewEditor.tsx
      ProgressPanel.tsx
      DiffPanel.tsx
    lib/
      taskSchema.ts
      progress.ts
      api.ts
  server/
    index.ts
```

The first UI should be simple:

```text
top:    current branch, dirty status, progress
left:   List / Tree / Dependency task navigation
middle: atom/docs-src preview or editor
right:  review note, checklist, diff
```

The local server should expose a narrow API:

```text
GET  /api/tasks
GET  /api/reviews
GET  /api/source?task=RG-PILOT-001
POST /api/review
POST /api/source
GET  /api/git/status
GET  /api/git/diff?task=RG-PILOT-001
POST /api/validate
```

The server must enforce path allow-lists from the task card. It must reject
absolute-path escape, `..` traversal, symlink escape, and writes outside the
task's editable scope.

## GitHub Issue Shape

A generated issue for a math-review task should contain:

```md
## Task

Review `ch5:2.4`.

## Read

- `projects/riemannian-geometry/.astrolabe/atoms/c944a1ee39aa.md`
- corresponding chapter source in `docs-src/05-jacobi.mdx`

## Questions

1. Is the statement mathematically correct?
2. What is the geometric meaning?
3. What hidden dependencies should Lean formalizers know?
4. Is this task routine, medium, or conceptually important?

## Expected Output

Write a comment with:

- verdict: accept / needs correction / unclear;
- mathematical explanation;
- formalization hints;
- suggested next status.

## Completion Checklist

- [ ] Math review claimed
- [ ] Math review submitted
- [ ] Maintainer accepted math review
- [ ] Lean task opened or linked
```

## GitHub Project Fields

Use a GitHub Project for visualization. Suggested fields:

```text
Status
Role
Chapter
dcref
Difficulty
Insight
Formalization Risk
Owner
Reviewer
Linked PR
Blocked Reason
```

Suggested views:

- `Board by Status`: day-to-day collaboration.
- `Table by Chapter`: full-book coverage.
- `Math Queue`: tasks whose next role is math.
- `Lean Queue`: tasks whose next role is Lean.
- `High Insight`: conceptually valuable tasks.
- `Blocked`: tasks needing maintainer decision.

## Progress Metrics

Do not use a single progress number as the only signal. Track at least four
separate percentages:

```text
Math reviewed:        math_review_submitted / total_tasks
Math verified:        math_verified / total_tasks
Lean statements:      lean_statement_pr / total_tasks
Lean proof/plans:     lean_proof_or_sorry_plan / total_tasks
Graph integrated:     formalizes_edge_checked / total_tasks
```

An optional weighted overall progress can be:

```text
overall =
  0.20 * math_review_submitted
+ 0.20 * math_verified
+ 0.25 * lean_statement_pr
+ 0.25 * lean_proof_or_sorry_plan
+ 0.10 * formalizes_edge_checked
```

For the pilot, success means that `RG-PILOT-001` reaches `Done` and the progress
report visibly changes from `0/3` to `1/3`.

## One-Line Commands

The eventual contributor-facing interface should be simple.

For a math reviewer:

```bash
python tools/openga/start_review.py --role math --level starter
```

Expected output:

```text
Recommended task: RG-PILOT-001
dcref: ch5:2.4
Review app: http://localhost:5173/?task=RG-PILOT-001
```

For a Lean formalizer:

```bash
python tools/openga/start_review.py --role lean --level starter
```

For maintainers:

```bash
python tools/openga/progress.py
```

Expected output:

```text
Pilot progress
Math reviewed:        1/3  33%
Math verified:        1/3  33%
Lean statements:      0/3   0%
Lean proof/plans:     0/3   0%
Graph integrated:     0/3   0%
Overall:             13%
```

## Agent Skills

Start with local repo skills rather than a packaged plugin.

Suggested structure:

```text
.agent-skills/
  openga-task-router/
    SKILL.md
  openga-math-review/
    SKILL.md
  openga-lean-formalize/
    SKILL.md
  openga-progress-reporter/
    SKILL.md
```

### openga-task-router

Purpose: choose the next task for a contributor.

The router may use AI/subagent-specific prompts for different roles, but its
task structure, hierarchy, and dependencies should come from `pilot.tasks.yaml`.

Inputs:

- role: `math`, `lean`, `tooling`, or `maintainer`;
- level: `starter`, `medium`, `advanced`;
- optional chapter or topic preference.

Output:

- one task;
- why this task is appropriate;
- exact files to read;
- expected deliverable;
- next command.

### openga-math-review

Purpose: guide a pure math contributor through semantic review.

It should avoid asking the contributor to understand Lean. It should ask for
mathematical correctness, intuition, hidden hypotheses, and handoff notes.

### openga-lean-formalize

Purpose: guide a Lean contributor from a math-verified task to a Lean statement,
proof, or documented `sorry`.

It should use existing OpenGA conventions, `docs/LEAN_TEX_WORKFLOW.md`, and
`docs/SORRY_CATALOG.md`.

### openga-progress-reporter

Purpose: scan task cards and produce a progress summary.

It should be deterministic and script-backed.

## Plugin Path

Do not package a Codex or Claude plugin until the local skills work on the pilot.

Recommended path:

```text
Phase 1: repo-local skills and scripts
Phase 2: install script for Codex and Claude Code
Phase 3: Codex plugin / Claude Code skill bundle
Phase 4: team onboarding guide
```

The first install script can be:

```bash
./tools/openga/install_agent_skills.sh codex
./tools/openga/install_agent_skills.sh claude
```

## Branch Plan

Use separate branches for separate concerns:

```text
docarmo-ocr-astrolabe-revision      content cleanup PR
pilot/agent-collaboration           pilot docs, skills, task cards, scripts
pilot/math-review-rg-pilot-001      sample math review task
pilot/lean-rg-pilot-001             sample Lean task
```

The pilot branch should be pushed to the fork first:

```bash
git push -u fork pilot/agent-collaboration
```

Only after the workflow is understandable should it be proposed upstream.

## Pilot TODO

### Phase 0: Repository Setup

- [ ] Confirm fork remote exists: `git remote -v`.
- [ ] Push `pilot/agent-collaboration` to the fork.
- [ ] Keep OCR zip files out of commits.
- [ ] Keep process-only experiments separate from the content cleanup PR.
- [ ] Keep the existing `web/` app unchanged during the review-app pilot.

### Phase 1: Task Schema And Static Roadmap Data

- [ ] Create `projects/riemannian-geometry/tasks/pilot.tasks.yaml`.
- [ ] Create `projects/riemannian-geometry/tasks/pilot.reviews.json`.
- [ ] Define hierarchy fields for parent topic and display order.
- [ ] Define dependency fields for `depends_on` and `blocks`.
- [ ] Add `RG-PILOT-001` for `ch5:2.4`.
- [ ] Add `RG-PILOT-002` for `ch8:5.3`.
- [ ] Add `RG-PILOT-003` for `ch13:4.2`.
- [ ] Include atom paths, chapter paths, status, difficulty, insight, and
      checklist fields.
- [ ] Include explicit `editable` scopes for every task.
- [ ] Validate that the YAML can drive List, Tree, and Dependency views without
      GitHub data.

### Phase 2: Trusted Roadmap Display

- [ ] Create `apps/review`.
- [ ] Use React with CSS Modules.
- [ ] Add a local server with read-only task, review, and source APIs.
- [ ] Render List view for the flat task queue.
- [ ] Render Tree view for chapter/topic/task hierarchy.
- [ ] Render Dependency view for prerequisites and blocked downstream tasks.
- [ ] Render task detail, source preview, and progress.
- [ ] Confirm the app can open `RG-PILOT-001`.
- [ ] Confirm roadmap state is visibly sourced from `pilot.tasks.yaml`.

### Phase 3: Review Note Writing

- [ ] Add `ReviewEditor`.
- [ ] Save review notes to `pilot.reviews.json`.
- [ ] Update task checklist/status through the app.
- [ ] Show progress changes after saving a review.

### Phase 4: Guarded Source Editing

- [ ] Add source edit mode for task-whitelisted atom/docs-src files.
- [ ] Save source edits only inside the task's editable scope.
- [ ] Show task-specific git diff after saving.
- [ ] Run `git diff --check` after source edits.
- [ ] Warn when atom and docs-src are likely out of sync.

### Phase 5: One-Line Task Routing

- [ ] Create `tools/openga/task_next.py`.
- [ ] Create `tools/openga/start_review.py`.
- [ ] Support `--role math`.
- [ ] Support `--role lean`.
- [ ] Print exact files to read and expected deliverable.
- [ ] Start the review app and open the selected task.

### Phase 6: Progress Reporting

- [ ] Create `tools/openga/progress.py`.
- [ ] Print per-stage percentages.
- [ ] Print an overall weighted progress number.
- [ ] Confirm initial pilot progress is `0/3`.
- [ ] Manually mark one checklist item complete and confirm progress changes.

### Phase 7: GitHub Issues

- [ ] Create `.github/ISSUE_TEMPLATE/math-review.yml`.
- [ ] Create `.github/ISSUE_TEMPLATE/formalization.yml`.
- [ ] Generate or manually create one issue for `RG-PILOT-001`.
- [ ] Add tasklist checkboxes to the issue.
- [ ] Confirm issue progress is visible in GitHub.

### Phase 8: Local Agent Skills

- [ ] Create `.agent-skills/openga-task-router/SKILL.md`.
- [ ] Create `.agent-skills/openga-math-review/SKILL.md`.
- [ ] Create `.agent-skills/openga-lean-formalize/SKILL.md`.
- [ ] Create `.agent-skills/openga-progress-reporter/SKILL.md`.
- [ ] Forward-test one skill with a fresh agent or separate session.

### Phase 9: First Closed Loop

- [ ] Math reviewer claims `RG-PILOT-001`.
- [ ] Math reviewer submits a semantic review.
- [ ] Maintainer marks the task `Math Verified`.
- [ ] If needed, reviewer makes a guarded source edit and inspects the diff.
- [ ] Lean contributor opens a statement or skeleton PR.
- [ ] Lean contributor documents proof plan or completes proof.
- [ ] Maintainer checks whether a `formalizes` edge is needed.
- [ ] `progress.py` reports `1/3` pilot tasks complete.

### Phase 10: Scale Decision

- [ ] Decide whether the pilot is understandable for a pure math contributor.
- [ ] Decide whether the task card schema needs changes.
- [ ] Decide whether guarded source editing is safe enough to keep.
- [ ] Decide whether GitHub Project fields are sufficient.
- [ ] Decide whether to package repo-local skills into Codex/Claude plugins.
- [ ] If successful, generate the first chapter-sized task batch.

## Non-Goals For The Pilot

- Do not generate hundreds of issues.
- Do not require all contributors to install Lean.
- Do not require all contributors to understand `.astrolabe` internals.
- Do not modify the existing `web/` app for the pilot.
- Do not turn the review app into an unrestricted repository editor.
- Do not package plugins before local skills and scripts have been validated.

## Success Criteria

The pilot succeeds when:

1. a pure math contributor can run one command and receive a clear task;
2. the contributor can complete the task by reading a small number of files;
3. a Lean contributor can take over from the same task card;
4. progress is visible both in the terminal and in GitHub;
5. the maintainer can see exactly which stage is blocked.
