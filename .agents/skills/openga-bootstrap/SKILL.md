---
name: openga-bootstrap
description: Bootstrap a fresh OpenGA workspace. Use when the user says "setup OpenGA", "clone OpenGA", "开始 OpenGA", "初始化 OpenGA", or before any OpenGA work when no repo exists.
---

# OpenGA Bootstrap

Goal: get the user from "I have Codex CLI installed" to a working OpenGA workspace with the review app running.

## Before you start

Confirm the user has a GitHub account and has (or will) fork https://github.com/MathNetwork/OpenGA to their account. If they have not forked it yet, tell them to do it and then give you their GitHub username.

## Steps

1. Ask for the user's GitHub username (`<user>`).
2. Choose a directory (e.g. `~/projects` or the current directory) and clone:
   ```bash
   git clone git@github.com:<user>/OpenGA.git OpenGA
   cd OpenGA
   ```
3. Add upstream and activate the commit-msg hook:
   ```bash
   git remote add upstream git@github.com:MathNetwork/OpenGA.git
   git config core.hooksPath .githooks
   ```
4. Install review app dependencies:
   ```bash
   cd apps/review && npm install
   ```
5. (Optional) If the user wants to do Lean work, verify `elan` is installed and run:
   ```bash
   lake exe cache get && lake build
   ```
6. Start the review app:
   ```bash
   cd apps/review && npm run dev
   ```
7. Tell the user to open http://localhost:5173 in a browser.
8. After the clone, the project-level `AGENTS.md` / `CLAUDE.md` and the skills in `.agents/skills/` and `.claude/skills/` take over.

## Notes

- Do NOT commit or push during bootstrap unless the user explicitly asks.
- If `git@github.com` SSH fails, fall back to `https://github.com/<user>/OpenGA.git` and note that HTTPS requires a personal access token or GitHub CLI.
