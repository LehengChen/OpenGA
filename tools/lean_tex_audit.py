#!/usr/bin/env python3
"""Lean ↔ tex audit — the bidirectional gap finder of the formalization loop.

Reads the store and prints, in one place, the four signals that drive the next
iteration:

  1. Lean sorries         — the open formal gaps (what to prove next).
  2. (B) tex → lean       — low-hanging fruit: tex statements whose prerequisites
                            are already Lean-covered (the formalization frontier).
  3. (A) lean → tex       — holes: dependencies the Lean proofs require that the
                            tex concept graph is missing (informal-side repairs).
  4. under-linked tex     — long content / few edges → likely missed concepts.

    python3 tools/lean_tex_audit.py
"""
import json, sys, os
from collections import Counter, defaultdict

PROJECT = "/Users/moqian/OpenGALib/projects/riemannian-geometry"


def main():
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    from astrolabe_store import AstrolabeStorage
    s = AstrolabeStorage(PROJECT)
    def rec(h):
        r = s.data[h]["record"]; return json.loads(r) if isinstance(r, str) else r

    atoms = {h: e for h, e in s.data.items() if len(e["ref"]) == 1}
    edges = {h: e for h, e in s.data.items() if len(e["ref"]) >= 2}
    tex = {h for h in atoms if rec(h).get("src") == "docarmo"}
    lean = {h for h in atoms if rec(h).get("source") == "lean"}
    deg = {h: 0 for h in atoms}
    for e in edges.values():
        for r in e["ref"]:
            if r in deg:
                deg[r] += 1

    # 1. Lean sorries
    sor = [rec(h) for h in lean if rec(h).get("state") == "sorry"]
    print(f"=== 1. Lean sorries (开放的形式化缺口): {len(sor)} ===")
    for r in sorted(sor, key=lambda r: r.get("name", "")):
        print(f"   {r.get('file')}:{r.get('line')}  {r.get('name')}")

    # bridge: which tex concepts are Lean-covered
    covered, L2T = set(), {}
    for e in edges.values():
        if len(e["ref"]) == 2:
            a, b = e["ref"]
            if a in tex and b in lean: covered.add(a); L2T[b] = a
            if b in tex and a in lean: covered.add(b); L2T[a] = b

    # 2. (B) tex → lean fruit: uncovered tex whose deps are all covered
    texdeps = defaultdict(set)
    for h, e in edges.items():
        if len(e["ref"]) == 2 and all(r in tex for r in e["ref"]):
            if rec(h).get("rel") in ("uses", "references"):
                texdeps[e["ref"][0]].add(e["ref"][1])
    fruit = sorted(((len(rec(h).get("notes", "")), h, d) for h in tex - covered
                    if (d := texdeps[h]) and d <= covered), key=lambda x: x[0])
    print(f"\n=== 2. (B) 低垂果实 (依赖已被 lean 覆盖、未形式化): {len(fruit)} ===")
    for _, h, d in fruit[:12]:
        r = rec(h)
        print(f"   ch{r.get('chapter')}:{r.get('dcref','').split(':')[-1]:6} {r.get('sort'):11} "
              f"({(r.get('title') or '')[:34]}) ← {[rec(x).get('title') for x in d]}")

    # 3. (A) lean → tex holes: lean dep ⟹ tex edge that is missing
    leandep = {(e["ref"][0], e["ref"][1]) for h, e in edges.items()
               if len(e["ref"]) == 2 and all(r in lean for r in e["ref"])}
    texconn = {frozenset(e["ref"]) for e in edges.values()
               if len(e["ref"]) == 2 and all(r in tex for r in e["ref"])}
    implied = Counter()
    for l1, l2 in leandep:
        t1, t2 = L2T.get(l1), L2T.get(l2)
        if t1 and t2 and t1 != t2:
            implied[frozenset((t1, t2))] += 1
    holes = [(n, p) for p, n in implied.items() if p not in texconn]
    print(f"\n=== 3. (A) lean→tex 漏洞 (lean 证明要求、tex 缺失的依赖): {len(holes)} ===")
    for n, p in sorted(holes, reverse=True):
        t1, t2 = tuple(p)
        print(f"   [{n}× 证据] {rec(t1).get('title')} — {rec(t2).get('title')}")

    # 4. under-linked tex: long content, few edges
    print(f"\n=== 4. 欠链接 tex (长内容/少连通,疑似漏概念) top 8 ===")
    for h in sorted(tex, key=lambda h: len(rec(h).get("notes", "")) / (deg[h] + 1),
                    reverse=True)[:8]:
        r = rec(h)
        print(f"   len={len(r.get('notes','')):4} deg={deg[h]:2}  "
              f"ch{r.get('chapter')}:{r.get('dcref','').split(':')[-1]} ({(r.get('title') or '')[:36]})")


if __name__ == "__main__":
    main()
