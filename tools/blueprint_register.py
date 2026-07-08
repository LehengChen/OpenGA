#!/usr/bin/env python3
"""Register a leanblueprint LaTeX file into the Astrolabe store (the text side).

Companion to `lean_register.py`. Where that tool walks the Lean environment and
registers `source: lean` atoms, this one parses a leanblueprint `content.tex`
(`\\begin{theorem}` / `lemma` / `definition` blocks carrying `\\label{}`,
`\\lean{}`, `\\uses{}`) and:

  - registers/updates each blueprint node as a `source: tex` atom, identity-
    hashed by `H({source, label})` so re-runs are idempotent (statement edits, a
    newly added `\\lean{}` tag, etc. update in place without orphaning edges);
  - rebuilds the blueprint `\\uses{}` dependency edges as `(tex, tex)` edges;
  - links each node to its Lean formalization with a `(tex, lean)` `formalizes`
    bridge edge — but ONLY when the target Lean atom already exists in the store,
    so referential closure stays valid even when the blueprint references decls
    that live in a larger Lean library than this project currently mirrors;
  - links each `\\dcref`'d node to the existing OCR `src: docarmo` atom with a
    `(blueprint, docarmo)` `restates` bridge — dedup by linking, not duplicating.

Provenance is `provenance: docarmo | horizon`, driven by the `\\dcref{chX:Y.Z}`
macro: a node that cites a do Carmo location is `docarmo` (and bridges back to its
OCR atom); a node Horizon adds with no `\\dcref` is `horizon`. This tool never
modifies the existing `src: docarmo` OCR atoms — it only adds blueprint atoms and
edges. Use `tools/atoms_to_blueprint.py` to bootstrap the chapter skeleton first.

    python3 tools/blueprint_register.py \
        --blueprint projects/riemannian-geometry/blueprint/src \
        --project   projects/riemannian-geometry

Re-running is safe and idempotent. Pass --dry-run to preview counts only.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import sys

# Blueprint theorem-like environments → atom `sort`.
ENVIRONMENTS = (
    "theorem", "lemma", "definition", "proposition",
    "corollary", "remark", "example", "conjecture",
)

HERE = os.path.dirname(os.path.abspath(__file__))
REPO_ROOT = os.path.dirname(HERE)
DEFAULT_BLUEPRINT = os.path.normpath(
    os.path.join(REPO_ROOT, "..", "OpenGA", "blueprint", "src", "content.tex")
)
DEFAULT_PROJECT = os.path.join(REPO_ROOT, "projects", "riemannian-geometry")


def canon(record: dict) -> str:
    return json.dumps(record, sort_keys=True, ensure_ascii=False)


def strip_line_comments(tex: str) -> str:
    """Drop whole-line TeX comments; leave escaped \\% and inline math alone."""
    out = []
    for line in tex.splitlines():
        if line.lstrip().startswith("%"):
            continue
        out.append(line)
    return "\n".join(out)


def find_blocks(tex: str):
    """Yield (env, raw_inner) for each top-level theorem-like environment.

    Same-named environments do not nest in leanblueprint sources (a theorem's
    body holds a `proof`, not another `theorem`), so a non-greedy match between
    matching \\begin/\\end of the same environment is well-defined.
    """
    for env in ENVIRONMENTS:
        pattern = re.compile(
            r"\\begin\{" + env + r"\}(.*?)\\end\{" + env + r"\}",
            re.DOTALL,
        )
        for m in pattern.finditer(tex):
            yield env, m.group(1)


def parse_block(env: str, inner: str) -> dict | None:
    label_m = re.search(r"\\label\{([^}]*)\}", inner)
    if not label_m:
        return None  # unlabelled blocks are not addressable nodes
    label = label_m.group(1).strip()

    title_m = re.match(r"\s*\[([^\]]*)\]", inner)
    title = title_m.group(1).strip() if title_m else label

    lean_m = re.search(r"\\lean\{([^}]*)\}", inner)
    lean = lean_m.group(1).strip() if lean_m else None
    # A `\lean{}` tag may name several declarations (comma/space separated), e.g.
    # `\lean{Riemannian.DCIsImmersion, Riemannian.DCIsEmbedding}`; each becomes its
    # own (tex, lean) bridge.
    lean_names = [n.strip() for n in re.split(r"[,\s]+", lean) if n.strip()] if lean else []

    # `\dcref{chX:Y.Z}` is the provenance hook: present => this node states a
    # do Carmo result (and links back to the OCR atom); absent => Horizon-origin.
    dcref_m = re.search(r"\\dcref\{([^}]*)\}", inner)
    dcref = dcref_m.group(1).strip() if dcref_m else None

    uses_m = re.search(r"\\uses\{([^}]*)\}", inner, re.DOTALL)
    uses = []
    if uses_m:
        uses = [u.strip() for u in re.split(r"[,\s]+", uses_m.group(1)) if u.strip()]

    # Split off the nested proof so statement- and proof-level `\leanok` markers
    # can be told apart (statement formalized vs proof formalized).
    proof_m = re.search(r"\\begin\{proof\}(.*?)\\end\{proof\}", inner, re.DOTALL)
    proof = proof_m.group(1) if proof_m else ""

    # Statement text: strip the optional [title], the structural/status macros,
    # and the proof environment; keep the human-readable math statement.
    text = inner
    if title_m:
        text = text[title_m.end():]
    text = re.sub(r"\\begin\{proof\}.*?\\end\{proof\}", "", text, flags=re.DOTALL)
    statement_ok = bool(re.search(r"\\leanok", text))
    proof_ok = bool(re.search(r"\\leanok", proof))
    text = re.sub(r"\\label\{[^}]*\}", "", text)
    text = re.sub(r"\\lean\{[^}]*\}", "", text)
    text = re.sub(r"\\dcref\{[^}]*\}", "", text)
    text = re.sub(r"\\uses\{[^}]*\}", "", text, flags=re.DOTALL)
    text = re.sub(r"\\(leanok|mathlibok)\b", "", text)
    statement = text.strip()

    return {
        "env": env,
        "label": label,
        "title": title,
        "lean": lean,
        "lean_names": lean_names,
        "dcref": dcref,
        "uses": uses,
        "statement": statement,
        "statement_ok": statement_ok,
        "proof_ok": proof_ok,
    }


def expand_inputs(path: str, _seen: set | None = None) -> str:
    """Read a .tex file, recursively inlining `\\input{}` / `\\include{}` targets."""
    _seen = _seen if _seen is not None else set()
    rp = os.path.realpath(path)
    if rp in _seen:
        return ""
    _seen.add(rp)
    base = os.path.dirname(rp)
    text = open(rp, encoding="utf-8").read()

    def repl(m: re.Match) -> str:
        name = m.group(1).strip()
        cand = name if name.endswith(".tex") else name + ".tex"
        fp = os.path.join(base, cand)
        if os.path.exists(fp):
            return expand_inputs(fp, _seen)
        print(f"warning: \\input target not found: {cand}", file=sys.stderr)
        return ""

    return re.sub(r"\\(?:input|include)\{([^}]*)\}", repl, text)


def load_blueprint(path: str) -> str:
    """Source for `path`: a single file (following `\\input`) or every `.tex`
    under a directory (chapter-split layout)."""
    if os.path.isdir(path):
        parts = []
        for root, _dirs, files in os.walk(path):
            for f in sorted(files):
                if f.endswith(".tex"):
                    parts.append(open(os.path.join(root, f), encoding="utf-8").read())
        return "\n".join(parts)
    return expand_inputs(path)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--blueprint", default=DEFAULT_BLUEPRINT,
                    help="leanblueprint content.tex (follows \\input), or a "
                         f"directory of chapter .tex files (default: {DEFAULT_BLUEPRINT})")
    ap.add_argument("--project", default=DEFAULT_PROJECT,
                    help=f"astrolabe project dir (default: {DEFAULT_PROJECT})")
    ap.add_argument("--dry-run", action="store_true",
                    help="parse and report counts without writing the store")
    args = ap.parse_args()

    if not os.path.exists(args.blueprint):
        print(f"error: blueprint not found: {args.blueprint}", file=sys.stderr)
        return 1

    tex = strip_line_comments(load_blueprint(args.blueprint))
    nodes = []
    seen = set()
    for env, inner in find_blocks(tex):
        node = parse_block(env, inner)
        if node is None:
            continue
        if node["label"] in seen:
            print(f"warning: duplicate label {node['label']!r}, keeping first",
                  file=sys.stderr)
            continue
        seen.add(node["label"])
        nodes.append(node)

    sys.path.insert(0, HERE)
    from astrolabe_store import AstrolabeStorage, validate_store

    s = AstrolabeStorage(args.project)

    # Stable identity per blueprint node: H({source: tex, label}).
    def label_hash(label: str) -> str:
        return s._compute_hash(["__self__"], canon({"source": "tex", "label": label}))

    # Lean atom identity matches lean_register.py: H({source: lean, name}).
    def lean_hash(name: str) -> str:
        return s._compute_hash(["__self__"], canon({"source": "lean", "name": name}))

    # Existing OCR atoms, indexed by do Carmo reference, for dedup bridges. These
    # are never modified — blueprint nodes link TO them, they do not replace them.
    dcref2hash = {}
    for h, e in s.data.items():
        if len(e["ref"]) != 1:
            continue
        try:
            rec = json.loads(e["record"])
        except (json.JSONDecodeError, ValueError):
            continue
        if rec.get("src") == "docarmo" and rec.get("dcref"):
            dcref2hash[rec["dcref"]] = h

    # ── purge previous blueprint atoms + every edge touching them ──
    # Blueprint atoms are the tex atoms this tool manages: they carry `provenance`
    # and a `label`, which the OCR `src: docarmo` atoms never do.
    old_bp = set()
    for h, e in s.data.items():
        if len(e["ref"]) == 1:
            try:
                rec = json.loads(e["record"])
            except (json.JSONDecodeError, ValueError):
                continue
            if rec.get("source") == "tex" and "provenance" in rec and "label" in rec:
                old_bp.add(h)
    for h in [h for h, e in s.data.items() if any(r in old_bp for r in e["ref"])]:
        s.data.pop(h, None)

    # ── 1. register blueprint atoms ──
    label2hash = {}
    informal = 0
    for node in nodes:
        hid = label_hash(node["label"])
        lean_status = (
            "exists"
            if node["lean_names"] and all(lean_hash(n) in s.data for n in node["lean_names"])
            else "declared" if node["lean_names"]
            else "informal_only"
        )
        if lean_status == "informal_only":
            informal += 1
        record = canon({
            "source": "tex",
            "provenance": "docarmo" if node["dcref"] else "horizon",
            "dcref": node["dcref"],
            "label": node["label"],
            "sort": node["env"],
            "title": node["title"],
            "lean": node["lean"],
            "lean_status": lean_status,
            "statement_ok": node["statement_ok"],
            "proof_ok": node["proof_ok"],
            "notes": node["statement"],
        })
        s.data[hid] = {"ref": [hid], "record": record}
        label2hash[node["label"]] = hid

    # ── 2. rebuild \uses → (tex, tex) edges ──
    uses_edges = 0
    dangling = []
    for node in nodes:
        a = label2hash[node["label"]]
        for dep in node["uses"]:
            b = label2hash.get(dep)
            if b is None:
                dangling.append((node["label"], dep))
                continue
            if a == b:
                continue
            edge = canon({"sort": "(tex, tex)", "rel": "uses",
                          "notes": f"uses {dep}"})
            s.data[s._compute_hash([a, b], edge)] = {"ref": [a, b], "record": edge}
            uses_edges += 1

    # ── 3. (tex, lean) formalizes bridges — only for Lean atoms already present ──
    bridges = 0
    for node in nodes:
        for name in node["lean_names"]:
            lh = lean_hash(name)
            if lh not in s.data:
                continue  # closure-safe: skip bridges to decls not yet in the store
            a = label2hash[node["label"]]
            edge = canon({"sort": "(tex, lean)", "rel": "formalizes",
                          "notes": f"formalizes {name}"})
            s.data[s._compute_hash([a, lh], edge)] = {"ref": [a, lh], "record": edge}
            bridges += 1

    # ── 4. (blueprint, docarmo) restates bridges — dedup link to the OCR atom ──
    restates = 0
    missing_dcref = []
    for node in nodes:
        if not node["dcref"]:
            continue
        d = dcref2hash.get(node["dcref"])
        if d is None:
            missing_dcref.append((node["label"], node["dcref"]))
            continue
        a = label2hash[node["label"]]
        edge = canon({"sort": "(blueprint, docarmo)", "rel": "restates",
                      "notes": f"restates {node['dcref']}"})
        s.data[s._compute_hash([a, d], edge)] = {"ref": [a, d], "record": edge}
        restates += 1

    validate_store(s.data)
    if dangling:
        print(f"warning: {len(dangling)} dangling \\uses edge(s) skipped "
              f"(e.g. {dangling[0][0]} -> {dangling[0][1]})", file=sys.stderr)
    if missing_dcref:
        print(f"warning: {len(missing_dcref)} \\dcref(s) have no matching OCR atom "
              f"(e.g. {missing_dcref[0][0]} -> {missing_dcref[0][1]})", file=sys.stderr)
    n_docarmo = sum(1 for n in nodes if n["dcref"])
    print(f"parsed {len(nodes)} blueprint nodes "
          f"({n_docarmo} docarmo / {len(nodes) - n_docarmo} horizon; "
          f"{informal} informal_only), {uses_edges} uses edges, "
          f"{bridges} lean bridges, {restates} restates bridges")
    if args.dry_run:
        print("dry-run: store not written")
        return 0
    s._save()
    print(f"registered into {args.project}/.astrolabe")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
