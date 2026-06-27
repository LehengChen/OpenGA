#!/usr/bin/env python3
"""
Sync an Astrolabe md store into Neo4j as a derived graph index.

The .md files stay the canonical, content-addressed source; this just projects
them into Neo4j so the graph can be queried with Cypher.

  atom   (ref = [self])      -> (:Entry {hash, source, sort, title, ...})  + source label
  edge   (ref = [a, b])      -> (a)-[:REL {hash, sort}]->(b)   REL from `rel`

Idempotent: MERGE on hash. Run again after re-extraction to refresh.

Usage:
  NEO4J_URI=bolt://localhost:7687 NEO4J_USER=neo4j NEO4J_PASSWORD=... \
    python tools/md_to_neo4j.py [project_dir] [--clear]

Defaults to the riemannian-geometry project; --clear wipes the graph first.
"""
import os
import re
import sys
from pathlib import Path

import yaml
from neo4j import GraphDatabase

REPO = Path(__file__).resolve().parent.parent
DEFAULT_PROJECT = REPO / "projects" / "riemannian-geometry"


def parse_md(path: Path):
    """Return (frontmatter dict, body str) for a `---`-delimited md file."""
    text = path.read_text(encoding="utf-8")
    m = re.match(r"^---\n(.*?)\n---\n?(.*)$", text, re.DOTALL)
    if not m:
        return None, None
    return yaml.safe_load(m.group(1)) or {}, m.group(2).strip()


def rel_type(rel: str) -> str:
    """`example-of` -> EXAMPLE_OF; safe to interpolate into Cypher."""
    t = re.sub(r"[^A-Za-z0-9]+", "_", (rel or "rel")).strip("_").upper()
    return t or "REL"


def load(project_dir: Path, clear: bool):
    store = project_dir / ".astrolabe"
    atoms_dir, edges_dir = store / "atoms", store / "edges"
    uri = os.environ.get("NEO4J_URI", "bolt://localhost:7687")
    user = os.environ.get("NEO4J_USER", "neo4j")
    pwd = os.environ.get("NEO4J_PASSWORD", "password")

    driver = GraphDatabase.driver(uri, auth=(user, pwd))
    with driver.session() as s:
        if clear:
            s.run("MATCH (n) DETACH DELETE n")
        s.run("CREATE CONSTRAINT entry_hash IF NOT EXISTS FOR (e:Entry) REQUIRE e.hash IS UNIQUE")

        # Atoms → nodes
        n_atoms = 0
        for f in sorted(atoms_dir.glob("*.md")):
            fm, body = parse_md(f)
            if fm is None:
                continue
            h = f.stem
            props = {k: v for k, v in fm.items() if k != "ref" and not isinstance(v, (list, dict))}
            props["hash"] = h
            props["body"] = body
            src = (fm.get("source") or "node").capitalize()  # Tex / Lean
            s.run(
                f"MERGE (e:Entry {{hash: $hash}}) SET e += $props SET e:{src}",
                hash=h, props=props,
            )
            n_atoms += 1

        # Edges → relationships
        n_edges = 0
        for f in sorted(edges_dir.glob("*.md")):
            fm, body = parse_md(f)
            if fm is None:
                continue
            ref = fm.get("ref") or []
            if len(ref) != 2:
                continue
            a, b = ref
            rt = rel_type(fm.get("rel"))
            s.run(
                f"MATCH (a:Entry {{hash: $a}}), (b:Entry {{hash: $b}}) "
                f"MERGE (a)-[r:{rt} {{hash: $hash}}]->(b) "
                f"SET r.sort = $sort, r.rel = $rel, r.note = $note",
                a=a, b=b, hash=f.stem, sort=fm.get("sort"), rel=fm.get("rel"), note=body,
            )
            n_edges += 1

    driver.close()
    print(f"synced {n_atoms} atoms, {n_edges} edges → {uri}")


if __name__ == "__main__":
    args = [a for a in sys.argv[1:] if a != "--clear"]
    project = Path(args[0]).resolve() if args else DEFAULT_PROJECT
    load(project, clear="--clear" in sys.argv)
