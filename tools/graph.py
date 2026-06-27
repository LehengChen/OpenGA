#!/usr/bin/env python3
"""Read the Astrolabe hypergraph from the terminal.

Usage:
  python3 tools/graph.py stats        # counts by source / sort / state
  python3 tools/graph.py diff         # tex <-> lean correspondence (the progress table)
  python3 tools/graph.py sorry        # unverified lean nodes (file:line)
  python3 tools/graph.py node <title> # one node + its neighbours

Reads the live store from the Node API at localhost:3000 (run `npm run dev`).
"""
import sys, json, urllib.parse, urllib.request

API = "http://localhost:3000"
PROJECT = "/Users/moqian/OpenGALib/projects/riemannian-geometry"


def entries():
    url = f"{API}/api/astrolabe/entries?path={urllib.parse.quote(PROJECT)}"
    d = json.load(urllib.request.urlopen(url))
    out = {}
    for h, e in d.items():
        r = e["record"]
        out[h] = {"ref": e["ref"], "rec": json.loads(r) if isinstance(r, str) else r}
    return out


def atoms(g):  return {h: e for h, e in g.items() if len(e["ref"]) == 1}
def edges(g):  return {h: e for h, e in g.items() if len(e["ref"]) == 2}


def cmd_stats(g):
    a, e = atoms(g), edges(g)
    by_src, by_sort, by_state = {}, {}, {}
    for h, n in a.items():
        r = n["rec"]
        by_src[r.get("source", "?")] = by_src.get(r.get("source", "?"), 0) + 1
        by_sort[r.get("sort", "?")] = by_sort.get(r.get("sort", "?"), 0) + 1
        if r.get("source") == "lean":
            by_state[r.get("state", "?")] = by_state.get(r.get("state", "?"), 0) + 1
    print(f"{len(a)} nodes, {len(e)} edges")
    print("  by source:", by_src)
    print("  by sort:  ", by_sort)
    print("  lean state:", by_state)


def cmd_diff(g):
    a, e = atoms(g), edges(g)
    tex = {h: n["rec"] for h, n in a.items() if n["rec"].get("source") == "tex"}
    lean = {h: n["rec"] for h, n in a.items() if n["rec"].get("source") == "lean"}
    xs = [n for n in e.values() if n["rec"].get("sort") == "(tex, lean)"]
    tex_mapped, lean_mapped = set(), set()
    print("=== mapped (tex ⟷ lean) ===")
    for x in xs:
        t, l = x["ref"]
        if t in tex and l in lean:
            tex_mapped.add(t); lean_mapped.add(l)
            st = lean[l].get("state")
            mark = "✓" if st == "proven" else "✗ sorry"
            print(f"  {tex[t]['title']:28} ⟷ {lean[l]['title']:34} [{mark}]")
    print(f"\n=== tex with NO lean ({len(tex)-len(tex_mapped)}) — need formalizing ===")
    for h, r in tex.items():
        if h not in tex_mapped:
            print(f"  {r.get('title','?')}")
    n_sorry = sum(1 for h, r in lean.items() if r.get("state") == "sorry")
    print(f"\n=== lean unverified (sorry): {n_sorry}/{len(lean)} ===")
    print(f"=== lean with no tex counterpart: {len(lean)-len(lean_mapped)} (formal-internal) ===")


def cmd_sorry(g):
    rows = [(n["rec"]) for n in atoms(g).values()
            if n["rec"].get("source") == "lean" and n["rec"].get("state") == "sorry"]
    print(f"{len(rows)} unverified lean nodes:")
    for r in sorted(rows, key=lambda x: x.get("file", "")):
        print(f"  {r.get('title',''):40} {r.get('file','')}:{r.get('line','')}")


def cmd_node(g, title):
    a = atoms(g)
    match = [(h, n["rec"]) for h, n in a.items() if n["rec"].get("title") == title]
    if not match:
        print(f"no node titled {title!r}"); return
    h, r = match[0]
    print(f"{h}  [{r.get('source')}/{r.get('sort')}]  {r.get('title')}")
    if r.get("source") == "lean":
        print(f"  {r.get('file')}:{r.get('line')}  state={r.get('state')}")
    for he, ne in edges(g).items():
        if ne["ref"][0] == h:
            tgt = a.get(ne["ref"][1], {}).get("rec", {}).get("title", ne["ref"][1])
            print(f"  → [{ne['rec'].get('sort')}] {tgt}")
        elif ne["ref"][1] == h:
            src = a.get(ne["ref"][0], {}).get("rec", {}).get("title", ne["ref"][0])
            print(f"  ← [{ne['rec'].get('sort')}] {src}")


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "stats"
    g = entries()
    if cmd == "stats": cmd_stats(g)
    elif cmd == "diff": cmd_diff(g)
    elif cmd == "sorry": cmd_sorry(g)
    elif cmd == "node": cmd_node(g, sys.argv[2])
    else: print(__doc__)
