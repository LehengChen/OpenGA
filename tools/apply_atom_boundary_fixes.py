#!/usr/bin/env python3
"""Apply atom boundary fixes identified by subagent review.

Reads `projects/riemannian-geometry/tasks/atom-boundary-subagent-report.json`,
trims the 14 confirmed boundary errors, migrates content-addressed hashes in
batches, and stashes trimmed transitional prose into docs-src.

Usage:
    python3 tools/apply_atom_boundary_fixes.py [--dry-run]
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import sys
from pathlib import Path

import yaml

PROJECT_DIR = Path(__file__).resolve().parents[1] / "projects" / "riemannian-geometry"
REPORT_PATH = PROJECT_DIR / "tasks" / "atom-boundary-subagent-report.json"
ATOMS_DIR = PROJECT_DIR / ".astrolabe" / "atoms"
EDGES_DIR = PROJECT_DIR / ".astrolabe" / "edges"
DOCS_SRC_DIR = PROJECT_DIR / ".astrolabe" / "docs-src"
CHECKLIST_PATH = PROJECT_DIR / "tasks" / "atom-boundary-review.md"

CHAPTER_TO_DOCSRC = {
    0: "00-manifolds.mdx",
    1: "01-metrics.mdx",
    2: "02-connections.mdx",
    3: "03-geodesics.mdx",
    4: "04-curvature.mdx",
    5: "05-jacobi.mdx",
    6: "06-immersions.mdx",
    7: "07-hopf-rinow.mdx",
    8: "08-constant-curvature.mdx",
    9: "09-variations.mdx",
    10: "10-rauch.mdx",
    11: "11-morse.mdx",
    12: "12-fundamental-group.mdx",
    13: "13-sphere-theorem.mdx",
}


def compute_atom_hash(record: str) -> str:
    """SHA256('__self__' + 0x00 + record)[:12 hex]."""
    buf = b"__self__\x00" + record.encode("utf-8")
    return hashlib.sha256(buf).hexdigest()[:12]


def compute_edge_hash(ref: list[str], record: str) -> str:
    """SHA256(ref[0] + 0x00 + ref[1] + 0x00 + ... + record)[:12 hex]."""
    buf = bytearray()
    for h in ref:
        buf.extend(h.encode("utf-8"))
        buf.append(0x00)
    buf.extend(record.encode("utf-8"))
    return hashlib.sha256(bytes(buf)).hexdigest()[:12]


def load_atoms() -> dict[str, tuple[Path, dict, str]]:
    atoms: dict[str, tuple[Path, dict, str]] = {}
    for f in sorted(ATOMS_DIR.glob("*.md")):
        text = f.read_text(encoding="utf-8")
        if not text.startswith("---\n"):
            continue
        end = text.index("\n---\n", 3)
        front = yaml.safe_load(text[4 : end + 1]) or {}
        body = text[end + 5 :]
        atoms[f.stem] = (f, front, body)
    return atoms


def load_edges() -> dict[str, tuple[Path, dict, str]]:
    edges: dict[str, tuple[Path, dict, str]] = {}
    if not EDGES_DIR.exists():
        return edges
    for f in sorted(EDGES_DIR.glob("*.md")):
        text = f.read_text(encoding="utf-8")
        if not text.startswith("---\n"):
            continue
        end = text.index("\n---\n", 3)
        front = yaml.safe_load(text[4 : end + 1]) or {}
        body = text[end + 5 :]
        edges[f.stem] = (f, front, body)
    return edges


def find_atom_by_dcref(atoms: dict, dcref: str) -> tuple[str, Path, dict, str] | None:
    for h, (p, front, body) in atoms.items():
        if front.get("dcref") == dcref:
            return h, p, front, body
    return None


def build_atom_record(front: dict, body: str) -> str:
    rec = dict(front)
    if body.strip():
        rec["notes"] = body
    elif "notes" in rec:
        del rec["notes"]
    return json.dumps(rec, sort_keys=True, ensure_ascii=False)


def build_edge_record(front: dict, body: str) -> str:
    rec = dict(front)
    if body.strip():
        rec["notes"] = body
    elif "notes" in rec:
        del rec["notes"]
    return json.dumps(rec, sort_keys=True, ensure_ascii=False)


def find_trim_index(body: str, trim_after: str) -> int:
    idx = body.find(trim_after)
    if idx != -1:
        return idx + len(trim_after)
    for marker in ("\\blacksquare", "\\square"):
        idx = body.find(marker)
        if idx != -1:
            return idx + len(marker)
    return -1


def trim_body(body: str, trim_after: str) -> tuple[str, str]:
    idx = find_trim_index(body, trim_after)
    if idx == -1:
        raise ValueError(f"Could not find trim marker: {trim_after!r}")
    kept = body[:idx].rstrip()
    trimmed = body[idx:].lstrip()
    return kept, trimmed


def write_atom(path: Path, front: dict, body: str) -> None:
    fm = yaml.safe_dump(front, sort_keys=True, allow_unicode=True, default_flow_style=False)
    path.write_text(f"---\n{fm}---\n{body}", encoding="utf-8")


def write_edge(path: Path, front: dict, body: str) -> None:
    fm = yaml.safe_dump(front, sort_keys=True, allow_unicode=True, default_flow_style=False)
    path.write_text(f"---\n{fm}---\n{body}", encoding="utf-8")


def update_checklist(report: dict) -> None:
    lines = [
        "# Atom Boundary Review Checklist",
        "",
        "All previously flagged items have been reviewed by subagents and fixed where a boundary error was confirmed.",
        "See `atom-boundary-subagent-report.json` and `atom-boundary-fix-plan.md` for details.",
        "",
        "## Status",
        "",
        f"- Total candidates reviewed: {report['summary']['total_reviewed']}",
        f"- Confirmed and fixed: {report['summary']['confirmed_errors']}",
        f"- No error found: {report['summary']['total_reviewed'] - report['summary']['confirmed_errors']}",
        "",
        "## No-error items",
        "",
    ]
    for finding in report["findings"]:
        if not finding.get("has_boundary_error"):
            lines.append(f"- `{finding['dcref']}` — {finding['notes']}")

    lines.append("")
    lines.append("## Fixed items")
    lines.append("")
    for finding in report["findings"]:
        if finding.get("has_boundary_error"):
            lines.append(
                f"- `{finding['dcref']}` — {finding['error_kind']} "
                f"(trimmed content belongs to: {finding['trimmed_content_belongs']})"
            )

    lines.append("")
    CHECKLIST_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--dry-run", action="store_true", help="Preview changes without writing")
    args = parser.parse_args()

    if not REPORT_PATH.exists():
        print(f"error: report not found: {REPORT_PATH}", file=sys.stderr)
        return 1

    with REPORT_PATH.open() as f:
        report = json.load(f)

    atoms = load_atoms()
    edges = load_edges()

    trimmed_by_chapter: dict[int, list[tuple[str, str]]] = {}
    fixed: list[str] = []
    skipped: list[str] = []
    hash_remap: dict[str, str] = {}  # old_hash -> new_hash

    # Phase 1: compute all new atom bodies and hashes.
    for finding in report["findings"]:
        dcref = finding["dcref"]
        if not finding.get("has_boundary_error"):
            skipped.append(dcref)
            continue

        atom = find_atom_by_dcref(atoms, dcref)
        if atom is None:
            print(f"warning: atom not found for {dcref}", file=sys.stderr)
            skipped.append(dcref)
            continue

        old_hash, path, front, body = atom
        try:
            new_body, trimmed = trim_body(body, finding["trim_after"])
        except ValueError as e:
            print(f"warning: {dcref}: {e}", file=sys.stderr)
            skipped.append(dcref)
            continue

        if not trimmed.strip():
            skipped.append(dcref)
            continue

        new_record = build_atom_record(front, new_body)
        new_hash = compute_atom_hash(new_record)

        if old_hash in hash_remap:
            print(f"warning: duplicate old hash {old_hash} for {dcref}", file=sys.stderr)
            skipped.append(dcref)
            continue

        hash_remap[old_hash] = new_hash
        fixed.append(dcref)
        chapter = int(front.get("chapter", dcref.split(":")[0].replace("ch", "")))
        trimmed_by_chapter.setdefault(chapter, []).append((dcref, trimmed))

    if args.dry_run:
        print(f"Would fix: {len(fixed)}")
        for dcref in fixed:
            print(f"  - {dcref}")
        print(f"Would skip: {len(skipped)}")
        for dcref in skipped:
            print(f"  - {dcref}")
        return 0

    # Phase 2: write new atoms and delete old ones.
    for finding in report["findings"]:
        dcref = finding["dcref"]
        if dcref not in fixed:
            continue
        atom = find_atom_by_dcref(atoms, dcref)
        assert atom is not None
        old_hash, path, front, body = atom
        new_body, _ = trim_body(body, finding["trim_after"])
        new_hash = hash_remap[old_hash]

        new_front = dict(front)
        new_front["ref"] = [new_hash]
        new_path = ATOMS_DIR / f"{new_hash}.md"
        write_atom(new_path, new_front, new_body)
        path.unlink()

    # Phase 3: migrate edges.
    old_to_new = {old: new for old, new in hash_remap.items()}
    edges_to_delete: list[Path] = []
    edges_to_write: list[tuple[Path, dict, str]] = []

    for old_hash, (path, front, body) in edges.items():
        new_ref = [old_to_new.get(r, r) for r in front.get("ref", [])]
        new_body = body
        new_record_text = build_edge_record(front, body)
        for old, new in old_to_new.items():
            new_body = new_body.replace(old, new)
            new_record_text = new_record_text.replace(old, new)

        # Reconstruct front with updated ref and no notes (notes go into record).
        new_front = dict(front)
        new_front["ref"] = new_ref
        if "notes" in new_front:
            del new_front["notes"]

        new_record = build_edge_record(new_front, new_body)
        new_hash = compute_edge_hash(new_ref, new_record)

        if new_hash == old_hash and new_body == body:
            continue  # unchanged

        edges_to_delete.append(path)
        edges_to_write.append((EDGES_DIR / f"{new_hash}.md", new_front, new_body))

    for p in edges_to_delete:
        p.unlink()
    for p, front, body in edges_to_write:
        write_edge(p, front, body)

    # Phase 4: write trimmed prose to docs-src.
    DOCS_SRC_DIR.mkdir(parents=True, exist_ok=True)
    for chapter, items in sorted(trimmed_by_chapter.items()):
        filename = CHAPTER_TO_DOCSRC.get(chapter, f"{chapter:02d}-chapter.mdx")
        doc_path = DOCS_SRC_DIR / filename
        sections = [f"## Trimmed from {dcref}\n\n{trimmed}\n" for dcref, trimmed in items]
        if doc_path.exists():
            existing = doc_path.read_text(encoding="utf-8")
            if "## Boundary-trimmings" not in existing:
                existing += "\n\n## Boundary-trimmings\n\n"
            existing += "\n".join(sections)
            doc_path.write_text(existing, encoding="utf-8")
        else:
            header = f"# Chapter {chapter} — boundary trimmings\n\n"
            header += "_This file was seeded by `tools/apply_atom_boundary_fixes.py` with content removed from atoms during boundary correction._\n\n"
            doc_path.write_text(header + "## Boundary-trimmings\n\n" + "\n".join(sections), encoding="utf-8")

    # Phase 5: update checklist.
    update_checklist(report)

    print(f"Fixed atoms: {len(fixed)}")
    for dcref in fixed:
        print(f"  - {dcref}")
    print(f"Skipped / no error: {len(skipped)}")
    for dcref in skipped:
        print(f"  - {dcref}")
    print(f"Migrated edges: {len(edges_to_write)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
