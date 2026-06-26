#!/usr/bin/env python3
"""Extract a tex hypergraph from faithful do Carmo MDX transcriptions.

Each numbered statement (`### 3.5 Lemma (Gauss)`) becomes a `source: tex` node.
do Carmo numbers are *section.index within a chapter*, so identity is
`docarmo ch{C}:{N.M}` (the chapter comes from the file name `ch{C}.mdx`).
Cross-references in the prose become dependency edges:
  - "by Lemma 3.4"                  → same chapter, §3 statement 4
  - "Proposition 5.4 of Chapter 0"  → chapter 0, §5 statement 4

  python3 tools/tex_extract.py <dir-of-ch*.mdx>            # dry-run
  python3 tools/tex_extract.py <dir-of-ch*.mdx> --register # write into the store
"""
import sys, re, json, glob, os

KINDS = "Definition|Lemma|Theorem|Proposition|Corollary|Remark|Example"
HEAD = re.compile(rf"^###\s+(\d+\.\d+)\s+({KINDS})(?:\s+\((.+?)\))?\s*$", re.M)
ANYHEAD = re.compile(r"^#{2,3}\s", re.M)   # any §-section (##) or statement (###) heading
REF_CROSS = re.compile(rf"(?:{KINDS})\s+(\d+\.\d+)\s+of\s+Chapter\s+(\d+)", re.I)
REF_SAME = re.compile(rf"(?:{KINDS})\s+(\d+\.\d+)")
# Single pass for rewriting prose: "Kind N.M" optionally "of Chapter C". The
# combined form consumes each mention once, so the same-chapter case can't
# re-match text already wrapped by the cross-chapter case.
REF_LINK = re.compile(rf"(?:{KINDS})\s+(\d+\.\d+)(?:\s+of\s+Chapter\s+(\d+))?")


def linkify(text, chapter, key2hash, self_key=None):
    """Turn each cross-reference mention into `\\entryref{hash}{original text}`
    so it renders as a clickable inline link to the referenced tex card."""
    def repl(m):
        ch = m.group(2) or chapter
        key = f"ch{ch}:{m.group(1)}"
        if key == self_key:
            return m.group(0)
        h = key2hash.get(key)
        # auto mode: no baked text — the number is derived at render time
        return f"\\entryref{{{h}}}" if h else m.group(0)
    return REF_LINK.sub(repl, text)

PROJECT = "/Users/moqian/OpenGALib/projects/riemannian-geometry"


def chapter_of(text, path):
    m = re.search(r"^#\s+Chapter\s+(\d+)\b", text, re.M)
    if m:
        return m.group(1)
    m = re.search(r"ch(\d+)\.mdx$", path)
    return m.group(1) if m else None


def parse_file(path):
    text = open(path).read()
    ch = chapter_of(text, path)
    if ch is None:
        return []
    heads = list(HEAD.finditer(text))
    allheads = [h.start() for h in ANYHEAD.finditer(text)]
    out = []
    for m in heads:
        # statement body ends at the NEXT heading of any level (## or ###), so a
        # §-section heading + its intro stay in the doc, out of the node.
        nexts = [p for p in allheads if p > m.start()]
        end = min(nexts) if nexts else len(text)
        out.append({"chapter": ch, "num": m.group(1), "kind": m.group(2).lower(),
                    "name": m.group(3), "body": text[m.end():end].strip(),
                    "key": f"ch{ch}:{m.group(1)}",
                    "head_start": m.start(), "end": end, "path": path})
    return out


def deps_of(stmt):
    """Cross-references in the body → set of statement keys (ch{C}:{N.M})."""
    keys = set()
    body = stmt["body"]
    for num, ch in REF_CROSS.findall(body):
        keys.add(f"ch{ch}:{num}")
    # same-chapter refs = numbered refs that are NOT "... of Chapter N"
    body_wo_cross = REF_CROSS.sub("", body)
    for num in REF_SAME.findall(body_wo_cross):
        keys.add(f"ch{stmt['chapter']}:{num}")
    keys.discard(stmt["key"])
    return keys


def main():
    src = sys.argv[1]
    register = "--register" in sys.argv
    files = sorted(glob.glob(os.path.join(src, "*.mdx"))) if os.path.isdir(src) else [src]
    stmts = [s for f in files for s in parse_file(f)]
    known = {s["key"] for s in stmts}

    print(f"=== {len(stmts)} statements from {len(files)} chapter file(s) ===")
    edges, dangling = [], []
    for s in stmts:
        for d in deps_of(s):
            (edges if d in known else dangling).append((s["key"], d))
    by_ch = {}
    for s in stmts:
        by_ch.setdefault(s["chapter"], []).append(s)
    for ch in sorted(by_ch):
        print(f"  Ch{ch}: {len(by_ch[ch])} statements ({', '.join(s['num'] for s in by_ch[ch])})")

    print(f"\n=== dependency edges (resolved): {len(edges)} ===")
    print(f"=== dangling refs (need transcribing): {len(dangling)} ===")
    for a, b in sorted(set(dangling)):
        print(f"  {a} → {b}")

    modularize = "--modularize" in sys.argv
    if register or modularize:
        key2hash = register_nodes(stmts, edges)
        if modularize:
            print(f"\n=== modularizing {len(files)} docs → \\entryblock ===")
            modularize_docs(files, key2hash)


def register_nodes(stmts, edges):
    sys.path.insert(0, "/Users/moqian/OpenGALib/web/backend")
    from astrolabe_app.storage import AstrolabeStorage, validate_store
    s = AstrolabeStorage(PROJECT)
    def canon(r): return json.dumps(r, sort_keys=True, ensure_ascii=False)
    # purge previous docarmo extraction (idempotent re-run)
    def rec(h):
        r = s.data[h]["record"]; return json.loads(r) if isinstance(r, str) else r
    old = {h for h, e in s.data.items() if len(e["ref"]) == 1 and rec(h).get("src") == "docarmo"}
    old_e = {h for h, e in s.data.items() if len(e["ref"]) >= 2 and any(r in old for r in e["ref"])}
    for h in old | old_e:
        s.data.pop(h, None)
    # pass 1: every statement's hash (so cross-refs can resolve to any of them)
    key2hash = {}
    for st in stmts:
        ident = canon({"source": "tex", "src": "docarmo", "dcref": st["key"]})
        key2hash[st["key"]] = s._compute_hash(["__self__"], ident)
    # pass 2: linkify cross-references in the body, then store
    for st in stmts:
        hid = key2hash[st["key"]]
        title = st["name"] or f"{st['kind'].capitalize()} {st['num']}"
        notes = linkify(st["body"], st["chapter"], key2hash, self_key=st["key"])
        # NB: no "num" field — display numbers are derived from first occurrence,
        # never stored. `dcref` (ch:N.M) stays only as the stable identity.
        snap = canon({"sort": st["kind"], "source": "tex", "src": "docarmo", "dcref": st["key"],
                      "chapter": st["chapter"], "title": title, "notes": notes})
        s.put(hid, [hid], snap)
    n = 0
    for a, b in set(edges):
        if a in key2hash and b in key2hash:
            s.create_entry([key2hash[a], key2hash[b]],
                canon({"sort": "(docarmo, docarmo)", "notes": "do Carmo cross-reference."})); n += 1
    validate_store(s.data)
    print(f"\n=== registered {len(stmts)} do Carmo nodes + {n} dependency edges ===")
    return key2hash


def modularize_docs(files, key2hash):
    """Rewrite each chapter doc so every numbered statement becomes an embedded
    node `\\entryblock{hash}` — the doc keeps its §-section headings and intro
    prose, and the statement text now lives in (and is sourced from) the node."""
    for path in files:
        text = open(path).read()
        stmts = [s for s in parse_file(path)]
        if not stmts:
            continue
        ch = stmts[0]["chapter"]
        out = linkify(text[:stmts[0]["head_start"]], ch, key2hash)
        for i, st in enumerate(stmts):
            hid = key2hash.get(st["key"])
            if not hid:
                continue
            nxt = stmts[i + 1]["head_start"] if i + 1 < len(stmts) else len(text)
            out += f"\\entryblock{{{hid}}}\n\n" + linkify(text[st["end"]:nxt], ch, key2hash)
        open(path, "w").write(out)
        print(f"  modularized {os.path.basename(path)}: {len(stmts)} statements → entryblocks")


if __name__ == "__main__":
    main()
