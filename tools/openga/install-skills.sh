#!/usr/bin/env bash
# Install OpenGA agent skills globally so a user can bootstrap before cloning.
# Usage:
#   bash <(curl -fsSL https://raw.githubusercontent.com/LehengChen/OpenGA/main/tools/openga/install-skills.sh) claude
#   bash <(curl -fsSL https://raw.githubusercontent.com/LehengChen/OpenGA/main/tools/openga/install-skills.sh) codex
#   bash install-skills.sh all

set -euo pipefail

REPO_RAW="https://raw.githubusercontent.com/LehengChen/OpenGA/main"

install_claude() {
  local dir="$HOME/.claude/skills/openga-bootstrap"
  mkdir -p "$dir"
  curl -fsSL "$REPO_RAW/.claude/skills/openga-bootstrap/SKILL.md" -o "$dir/SKILL.md"
  echo "Installed Claude Code bootstrap skill to $dir"
}

install_codex() {
  local dir="$HOME/.agents/skills/openga-bootstrap"
  mkdir -p "$dir"
  curl -fsSL "$REPO_RAW/.agents/skills/openga-bootstrap/SKILL.md" -o "$dir/SKILL.md"
  echo "Installed Codex CLI bootstrap skill to $dir"
}

case "${1:-all}" in
  claude)
    install_claude
    ;;
  codex)
    install_codex
    ;;
  all)
    install_claude
    install_codex
    ;;
  *)
    echo "Usage: $0 {claude|codex|all}"
    exit 1
    ;;
esac

echo "Done. Now you can run your agent and say: setup OpenGA"
