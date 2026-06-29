#!/usr/bin/env python3
"""Regenerate do Carmo atoms from the original OCR markdown archive.

This tool rebuilds the do Carmo atom bodies from
`doCarmo-RiemannianGeometry-20260628093607.zip`, using the statement-boundary
rules documented in `docs/RIEMANNIAN_GEOMETRY_OCR_REVISION_WORKFLOW.md`.

It preserves:
- atom identities (12-hex hash filenames),
- YAML front-matter (`dcref`, `source`, `src`, `chapter`, `sort`, `title`, `ref`),
- non-do Carmo atoms,
- existing edges.

Run in report mode (default) to preview changes:

    python3 tools/regenerate_docarmo_atoms.py --report > /tmp/atom-regen-report.md

Run with `--write` to rewrite atom bodies in place (recommended only after
reviewing the report and with a clean git worktree):

    python3 tools/regenerate_docarmo_atoms.py --write

Run with `--diff dcref` to see the proposed diff for a single dcref:

    python3 tools/regenerate_docarmo_atoms.py --diff ch0:5.3
"""
from __future__ import annotations

import argparse
import difflib
import json
import os
import re
import sys
import zipfile
from pathlib import Path
from typing import Dict, List, Optional, Tuple

import yaml

PROJECT_DIR = Path(__file__).resolve().parents[1] / "projects" / "riemannian-geometry"
ATOMS_DIR = PROJECT_DIR / ".astrolabe" / "atoms"
EDGES_DIR = PROJECT_DIR / ".astrolabe" / "edges"
ZIP_PATH = Path(__file__).resolve().parents[1] / "doCarmo-RiemannianGeometry-20260628093607.zip"

# Kinds that begin a numbered statement in do Carmo.
STATEMENT_KINDS = "Definition|Theorem|Proposition|Lemma|Corollary|Remark|Example"

# Chapter title fixtures for body chapters whose OCR heading has no "## CHAPTER N" prefix.
# Each entry is (chapter_number, title_pattern, section_after_title_re).
CHAPTER_FIXTURES: List[Tuple[int, str, re.Pattern]] = [
    # Chapter 10 — body title appears as a bare line; TOC version has page number.
    (10, "THE RAUCH COMPARISON THEOREM", re.compile(r"^##\s+1\.\s+Introduction", re.I)),
    # Chapter 12 — body title appears as a bare line; TOC version has page number.
    (12, "THE FUNDAMENTAL GROUP OF MANIFOLDS OF NEGATIVE CURVATURE", re.compile(r"^##\s+1\.\s+Introduction", re.I)),
]


class ChapterDetector:
    """Find body chapter start positions in the OCR markdown."""

    def __init__(self, text: str):
        self.text = text
        self.lines = text.splitlines()
        self.line_offsets = []
        off = 0
        for line in self.lines:
            self.line_offsets.append(off)
            off += len(line) + 1  # include '\n'

    def _offset(self, line_idx: int) -> int:
        return self.line_offsets[line_idx]

    def detect(self) -> List[Tuple[int, int]]:
        """Return list of (chapter_number, byte_offset) sorted by offset."""
        chapters: List[Tuple[int, int]] = []

        # Explicit "## CHAPTER N" headings.
        for i, line in enumerate(self.lines):
            m = re.match(r"^##\s+CHAPTER\s+(.+)$", line, re.I)
            if not m:
                continue
            ch_text = m.group(1).strip()
            if ch_text.startswith("("):
                ch = 0
            else:
                dm = re.match(r"(\d+)", ch_text)
                ch = int(dm.group(1)) if dm else 0
            chapters.append((ch, self._offset(i)))

        # Named fixtures for chapters whose heading lacks the "## CHAPTER" prefix.
        for ch, title, next_section_re in CHAPTER_FIXTURES:
            for i, line in enumerate(self.lines):
                if title not in line:
                    continue
                # Reject table-of-contents lines that contain a trailing page number.
                if re.search(r"\d+\s*$", line):
                    continue
                # Accept only if nearby following lines look like body content.
                body_like = False
                for j in range(i + 1, min(i + 12, len(self.lines))):
                    if next_section_re.match(self.lines[j]):
                        body_like = True
                        break
                if body_like:
                    chapters.append((ch, self._offset(i)))
                    break

        chapters.sort(key=lambda x: x[1])
        return chapters


class StatementParser:
    """Find numbered statement boundaries in the OCR markdown."""

    def __init__(self, text: str, chapters: List[Tuple[int, int]]):
        self.text = text
        self.chapters = chapters  # sorted (chapter, offset)

    def _chapter_at(self, pos: int) -> int:
        ch = 0
        for chapter, offset in self.chapters:
            if offset <= pos:
                ch = chapter
            else:
                break
        return ch

    def _heading_patterns(self) -> List[re.Pattern]:
        """Return patterns ordered by precedence."""
        kinds = STATEMENT_KINDS
        # Standard: "2.1 Definition. Title" (and "2.1. Definition.")
        standard = re.compile(
            r"^(?P<section>\d+)\.(?P<item>\d+)\s*\.?\s*(?P<kind>" + kinds + r")\s*\.\s*(?P<title>.*)$",
            re.MULTILINE | re.IGNORECASE,
        )
        # Named-heading form where the kind word appears later in the title.
        named = re.compile(
            r"^(?P<section>\d+)\.(?P<item>\d+)\s+(?P<title>.*?(?:Theorem|Proposition|"
            r"Lemma|Corollary|Definition|Example|Remark)\..*)$",
            re.MULTILINE | re.IGNORECASE,
        )
        return [standard, named]

    def parse(self) -> List[Dict]:
        # Collect matches from all patterns, keeping only the first match at each position.
        seen: Dict[int, re.Match] = {}
        for pattern in self._heading_patterns():
            for m in pattern.finditer(self.text):
                if m.start() not in seen:
                    seen[m.start()] = m
        matches = sorted(seen.values(), key=lambda x: x.start())

        statements = []
        for i, m in enumerate(matches):
            section, item, kind, title = self._unpack_match(m)
            if section is None:
                continue
            start = m.start()
            chapter = self._chapter_at(start)
            end = matches[i + 1].start() if i + 1 < len(matches) else len(self.text)
            dcref = f"ch{chapter}:{section}.{item}"
            body = self.text[start:end].strip()
            statements.append(
                {
                    "dcref": dcref,
                    "chapter": chapter,
                    "section": section,
                    "item": item,
                    "kind": kind.lower() if kind else "",
                    "title": (title or "").strip(),
                    "start": start,
                    "end": end,
                    "body": body,
                }
            )
        return statements

    def _unpack_match(self, m: re.Match) -> Tuple[Optional[int], Optional[int], Optional[str], Optional[str]]:
        section = m.group("section") if "section" in m.groupdict() and m.group("section") else None
        item = m.group("item") if "item" in m.groupdict() and m.group("item") else None
        kind = m.group("kind") if "kind" in m.groupdict() and m.group("kind") else None
        title = m.group("title") if "title" in m.groupdict() and m.group("title") else None
        if section is None:
            return None, None, None, None
        return int(section), int(item), kind, title


def load_current_docarmo_atoms(atoms_dir: Path) -> Dict[str, Tuple[Path, Dict, str]]:
    """Return {dcref: (path, frontmatter, body)} for src==docarmo atoms."""
    result: Dict[str, Tuple[Path, Dict, str]] = {}
    for f in sorted(atoms_dir.glob("*.md")):
        text = f.read_text(encoding="utf-8")
        if not text.startswith("---\n"):
            continue
        end = text.index("\n---\n", 3)
        front = yaml.safe_load(text[4 : end + 1]) or {}
        body = text[end + 5 :]
        if front.get("src") == "docarmo" and front.get("dcref"):
            result[front["dcref"]] = (f, front, body)
    return result


def load_all_atoms(atoms_dir: Path) -> Dict[str, Tuple[Path, Dict, str]]:
    """Return {hash: (path, frontmatter, body)} for all atoms."""
    result: Dict[str, Tuple[Path, Dict, str]] = {}
    for f in sorted(atoms_dir.glob("*.md")):
        text = f.read_text(encoding="utf-8")
        if not text.startswith("---\n"):
            continue
        end = text.index("\n---\n", 3)
        front = yaml.safe_load(text[4 : end + 1]) or {}
        body = text[end + 5 :]
        result[f.stem] = (f, front, body)
    return result


def load_edges(edges_dir: Path) -> Dict[str, Tuple[Path, Dict, str]]:
    """Return {hash: (path, frontmatter, body)} for all edges."""
    result: Dict[str, Tuple[Path, Dict, str]] = {}
    if not edges_dir.exists():
        return result
    for f in sorted(edges_dir.glob("*.md")):
        text = f.read_text(encoding="utf-8")
        if not text.startswith("---\n"):
            continue
        end = text.index("\n---\n", 3)
        front = yaml.safe_load(text[4 : end + 1]) or {}
        body = text[end + 5 :]
        result[f.stem] = (f, front, body)
    return result


def build_atom_record(front: Dict, body: str) -> str:
    """Build the canonical record string used for hashing."""
    rec = dict(front)
    if body:
        rec["notes"] = body
    return json.dumps(rec, sort_keys=True, ensure_ascii=False)


def main() -> int:
    parser = argparse.ArgumentParser(description="Regenerate do Carmo atoms from OCR source")
    parser.add_argument("--report", action="store_true", help="Print a markdown report (default)")
    parser.add_argument("--write", action="store_true", help="Rewrite atom bodies in place")
    parser.add_argument("--diff", metavar="DCREF", help="Show unified diff for one dcref")
    parser.add_argument("--zip", type=Path, default=ZIP_PATH, help="Path to OCR zip archive")
    args = parser.parse_args()

    if not args.zip.exists():
        print(f"error: zip not found: {args.zip}", file=sys.stderr)
        return 1

    with zipfile.ZipFile(args.zip) as z:
        original = z.read("doCarmo-RiemannianGeometry.md").decode("utf-8")

    detector = ChapterDetector(original)
    chapters = detector.detect()
    parser_ = StatementParser(original, chapters)
    statements = parser_.parse()
    by_dcref: Dict[str, Dict] = {s["dcref"]: s for s in statements}

    current = load_current_docarmo_atoms(ATOMS_DIR)

    if args.diff:
        if args.diff not in current:
            print(f"error: dcref {args.diff} not found in current atoms", file=sys.stderr)
            return 1
        if args.diff not in by_dcref:
            print(f"error: dcref {args.diff} not found in OCR source", file=sys.stderr)
            return 1
        _, front, old_body = current[args.diff]
        new_body = by_dcref[args.diff]["body"]
        old_lines = (front.get("title", "") + "\n\n" + old_body).splitlines(keepends=True)
        new_lines = (by_dcref[args.diff]["title"] + "\n\n" + new_body).splitlines(keepends=True)
        sys.stdout.writelines(
            difflib.unified_diff(old_lines, new_lines, fromfile=f"{args.diff} current", tofile=f"{args.diff} OCR")
        )
        return 0

    missing = sorted(set(current.keys()) - set(by_dcref.keys()))
    extra = sorted(set(by_dcref.keys()) - set(current.keys()))
    shared = sorted(set(current.keys()) & set(by_dcref.keys()))

    changes: List[Tuple[str, int, int, str]] = []  # dcref, old_len, new_len, reason
    for dcref in shared:
        _, front, old_body = current[dcref]
        new_body = by_dcref[dcref]["body"]
        if old_body.strip() == new_body.strip():
            continue
        reason = "body differs"
        # Detect likely boundary swallowing of the next statement.
        next_dcref = next_dcref_in_book(dcref, list(by_dcref.keys()))
        if next_dcref and next_dcref in by_dcref:
            next_title = by_dcref[next_dcref]["title"]
            if next_title and next_title[:60] in new_body and next_title[:60] not in old_body:
                reason = "current atom may be missing trailing text"
            elif next_title[:60] in old_body and next_title[:60] not in new_body:
                reason = "current atom appears to swallow next statement"
        changes.append((dcref, len(old_body), len(new_body), reason))

    if args.write:
        all_atoms = load_all_atoms(ATOMS_DIR)
        edges = load_edges(EDGES_DIR)
        old_hash_to_dcref = {Path(p).stem: dcref for dcref, (p, _, _) in current.items()}

        for dcref in shared:
            path, front, _ = current[dcref]
            new_body = by_dcref[dcref]["body"]
            old_record = build_atom_record(front, current[dcref][2])
            new_front = dict(front)
            new_front["title"] = by_dcref[dcref]["title"]
            new_front["sort"] = by_dcref[dcref]["kind"]
            new_record = build_atom_record(new_front, new_body)
            old_hash = path.stem
            new_hash = hash_record(new_record)

            if old_hash == new_hash:
                continue

            new_path = ATOMS_DIR / f"{new_hash}.md"
            new_path.write_text(
                f"---\n{yaml.safe_dump(new_front, sort_keys=True, allow_unicode=True, default_flow_style=False)}---\n{new_body}",
                encoding="utf-8",
            )
            path.unlink()

            # Propagate hash change in edges that reference this atom.
            for e_hash, (e_path, e_front, e_body) in edges.items():
                if old_hash in e_front.get("ref", []) or old_hash in e_body:
                    new_e_front = dict(e_front)
                    new_e_front["ref"] = [new_hash if r == old_hash else r for r in e_front.get("ref", [])]
                    new_e_body = e_body.replace(old_hash, new_hash)
                    new_e_hash = hash_record({**new_e_front, **({"notes": new_e_body} if new_e_body else {})})
                    (EDGES_DIR / f"{new_e_hash}.md").write_text(
                        f"---\n{yaml.safe_dump(new_e_front, sort_keys=True, allow_unicode=True, default_flow_style=False)}---\n{new_e_body}",
                        encoding="utf-8",
                    )
                    e_path.unlink()

        print(f"Rewrote {len([c for c in changes if c[0] in by_dcref])} atoms; see git diff for details.")
        return 0

    # Default report mode.
    print("# do Carmo atom regeneration report")
    print()
    print(f"- OCR zip: `{args.zip}`")
    print(f"- OCR chapters detected: {len(chapters)} — {sorted([c[0] for c in chapters])}")
    print(f"- OCR statements detected: {len(statements)}")
    print(f"- Current do Carmo atoms: {len(current)}")
    print()

    print("## Current atoms not found in OCR source")
    print()
    if missing:
        print(f"**{len(missing)} missing.** These are either synthetic atoms or their chapter heading was not detected.")
        for dcref in missing[:40]:
            print(f"- `{dcref}`")
        if len(missing) > 40:
            print(f"- ... and {len(missing) - 40} more")
    else:
        print("None.")
    print()

    print("## OCR statements without a current atom")
    print()
    if extra:
        print(f"**{len(extra)} extra.** These would be new atoms if the scope were expanded.")
        for dcref in extra[:40]:
            print(f"- `{dcref}`: {by_dcref[dcref]['title'][:80]}")
        if len(extra) > 40:
            print(f"- ... and {len(extra) - 40} more")
    else:
        print("None.")
    print()

    print("## Proposed body changes")
    print()
    if changes:
        print("| dcref | current len | OCR len | reason |")
        print("|-------|-------------|---------|--------|")
        for dcref, old_len, new_len, reason in changes:
            print(f"| `{dcref}` | {old_len} | {new_len} | {reason} |")
    else:
        print("No body changes proposed.")
    print()

    print("## Priority boundary fixes")
    print()
    flagged = [c for c in changes if "swallow" in c[3] or "missing trailing" in c[3]]
    if flagged:
        print("| dcref | reason |")
        print("|-------|--------|")
        for dcref, _, _, reason in flagged:
            print(f"| `{dcref}` | {reason} |")
    else:
        print("None detected automatically.")
    print()

    print("## Next steps")
    print()
    print("1. Inspect a single diff: `python3 tools/regenerate_docarmo_atoms.py --diff ch0:5.3`")
    print("2. Review the full report above.")
    print("3. Apply changes: `python3 tools/regenerate_docarmo_atoms.py --write`")
    print("4. Validate: `python3 tools/astrolabe_store.py` or run the review-app backend tests.")
    return 0


def next_dcref_in_book(dcref: str, all_dcrefs: List[str]) -> Optional[str]:
    """Return the lexicographically next dcref ( crude book-order proxy)."""
    sorted_dcrefs = sorted(all_dcrefs)
    try:
        idx = sorted_dcrefs.index(dcref)
        return sorted_dcrefs[idx + 1] if idx + 1 < len(sorted_dcrefs) else None
    except ValueError:
        return None


def hash_record(record: str) -> str:
    """SHA256(record)[:12 hex], matching AstrolabeStorage._compute_hash for atoms."""
    import hashlib

    return hashlib.sha256(record.encode("utf-8")).hexdigest()[:12]


if __name__ == "__main__":
    sys.exit(main())
