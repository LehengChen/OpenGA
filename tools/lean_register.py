#!/usr/bin/env python3
"""Register the Lean hypergraph into the Astrolabe store (the formal side).

Pairs with `ExtractLeanGraph.lean`, which walks the whole OpenGALib environment
and writes `/tmp/lean_graph.json` (one record per `OpenGALib.*` declaration:
`name, module, kind, type, deps, sorry, line`).

This reads that file and:
  - registers/updates each Lean declaration as a `source: lean` atom, identity-
    hashed by `H({source, name})` so re-runs are idempotent (state sorry→proven,
    line moves, etc. update in place without changing the hash);
  - rebuilds the Lean→Lean dependency edges from `deps`.

Tex nodes and (lean, tex) cross-source bridges are NOT touched.

    lake env lean tools/ExtractLeanGraph.lean          # → /tmp/lean_graph.json
    web/backend/.venv/bin/python tools/lean_register.py
"""
import json, sys, os

PROJECT = "/Users/moqian/OpenGALib/projects/riemannian-geometry"
REPO = "/Users/moqian/OpenGALib"
GRAPH = "/tmp/lean_graph.json"


def main():
    data = json.load(open(GRAPH))
    sys.path.insert(0, os.path.join(REPO, "web/backend"))
    from astrolabe_app.storage import AstrolabeStorage, validate_store
    s = AstrolabeStorage(PROJECT)
    def canon(r): return json.dumps(r, sort_keys=True, ensure_ascii=False)

    # 1. register / update Lean atoms (identity hash = H({source, name}))
    name2hash = {}
    for d in data:
        name = d["name"]
        hid = s._compute_hash(["__self__"], canon({"source": "lean", "name": name}))
        rel = d["module"].replace(".", "/") + ".lean"          # OpenGALib/Riemannian/…/X.lean
        file = rel[len("OpenGALib/"):] if rel.startswith("OpenGALib/") else rel
        record = canon({
            "source": "lean", "name": name, "sort": d.get("kind", "other"),
            "state": "sorry" if d.get("sorry") else "proven",
            "file": file, "path": os.path.join(REPO, rel), "line": d.get("line", 0),
            "title": name.split(".")[-1], "content": d.get("type", ""),
        })
        s.data[hid] = {"ref": [hid], "record": record}
        name2hash[name] = hid

    # 2. rebuild Lean→Lean dependency edges (purge old, re-derive from deps)
    lean = set(name2hash.values())
    for h in [h for h, e in s.data.items()
              if len(e["ref"]) == 2 and all(r in lean for r in e["ref"])]:
        s.data.pop(h, None)
    existing, n = set(), 0
    for d in data:
        a = name2hash[d["name"]]
        for dep in d.get("deps", []):
            b = name2hash.get(dep)
            if not b or a == b or frozenset((a, b)) in existing:
                continue
            edge = canon({"sort": "(lean, lean)", "rel": "uses",
                          "notes": f"uses {dep.split('.')[-1]}"})
            s.data[s._compute_hash([a, b], edge)] = {"ref": [a, b], "record": edge}
            existing.add(frozenset((a, b))); n += 1

    validate_store(s.data)
    s._save()
    sorries = sum(1 for d in data if d.get("sorry"))
    print(f"registered {len(data)} lean nodes ({sorries} sorry), {n} dependency edges")


if __name__ == "__main__":
    main()
