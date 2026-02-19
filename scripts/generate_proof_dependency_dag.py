#!/usr/bin/env python3

from __future__ import annotations

import argparse
import json
import re
from collections import defaultdict, deque
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Iterable, List, Set, Tuple


DECL_RE = re.compile(
    r"^\s*(?:Local\s+|Global\s+)?(Lemma|Theorem|Corollary|Proposition|Fact|Remark)\s+([A-Za-z_][A-Za-z0-9_']*)\b"
)
END_RE = re.compile(r"^\s*(Qed\.|Defined\.|Admitted\.)\s*$")
TOKEN_RE = re.compile(r"\b[A-Za-z_][A-Za-z0-9_']*\b")


@dataclass
class Decl:
    name: str
    kind: str
    file: str
    line: int
    body: str


def _coq_files(root: Path) -> Iterable[Path]:
    return sorted(root.rglob("*.v"))


def _extract_decls(path: Path, coq_root: Path) -> List[Decl]:
    lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
    rel = path.relative_to(coq_root).as_posix()
    out: List[Decl] = []
    i = 0
    while i < len(lines):
        match = DECL_RE.match(lines[i])
        if not match:
            i += 1
            continue

        kind, name = match.group(1), match.group(2)
        start = i + 1
        i += 1
        body_lines: List[str] = []
        while i < len(lines):
            body_lines.append(lines[i])
            if END_RE.match(lines[i]):
                i += 1
                break
            i += 1

        out.append(
            Decl(
                name=name,
                kind=kind,
                file=rel,
                line=start,
                body="\n".join(body_lines),
            )
        )
    return out


def _build_graph(decls: List[Decl]) -> Tuple[Dict[str, Decl], List[Tuple[str, str]]]:
    by_name: Dict[str, Decl] = {}
    for decl in decls:
        if decl.name not in by_name:
            by_name[decl.name] = decl

    names: Set[str] = set(by_name.keys())
    edges: Set[Tuple[str, str]] = set()
    for decl in decls:
        tokens = set(TOKEN_RE.findall(decl.body))
        for tok in tokens:
            if tok == decl.name:
                continue
            if tok in names:
                edges.add((decl.name, tok))

    return by_name, sorted(edges)


def _rank(by_name: Dict[str, Decl], edges: List[Tuple[str, str]]) -> Dict[str, object]:
    indeg: Dict[str, int] = {k: 0 for k in by_name}
    outdeg: Dict[str, int] = {k: 0 for k in by_name}
    for src, dst in edges:
        outdeg[src] += 1
        indeg[dst] += 1

    roots = sorted([k for k, v in indeg.items() if v == 0])
    leaves = sorted([k for k, v in outdeg.items() if v == 0])
    isolated = sorted([k for k in by_name if indeg[k] == 0 and outdeg[k] == 0])
    top_out = sorted(outdeg.items(), key=lambda kv: kv[1], reverse=True)[:25]
    top_in = sorted(indeg.items(), key=lambda kv: kv[1], reverse=True)[:25]

    file_node_count: Dict[str, int] = defaultdict(int)
    for decl in by_name.values():
        file_node_count[decl.file] += 1
    top_files = sorted(file_node_count.items(), key=lambda kv: kv[1], reverse=True)[:25]

    weak_components = _weak_components(set(by_name.keys()), edges)
    scc_components = _scc_components(set(by_name.keys()), edges)

    return {
        "rootCount": len(roots),
        "leafCount": len(leaves),
        "isolatedCount": len(isolated),
        "roots": roots,
        "leaves": leaves,
        "isolated": isolated,
        "topOutDegree": [{"name": n, "out": d} for n, d in top_out],
        "topInDegree": [{"name": n, "in": d} for n, d in top_in],
        "topFilesByDecl": [{"file": f, "declCount": c} for f, c in top_files],
        "weakComponents": {
            "count": len(weak_components),
            "largest": [
                {
                    "size": len(component),
                    "sample": component[:8],
                }
                for component in weak_components[:20]
            ],
        },
        "stronglyConnectedCycles": {
            "count": len([component for component in scc_components if len(component) > 1]),
            "largest": [
                {
                    "size": len(component),
                    "sample": component[:8],
                }
                for component in [c for c in scc_components if len(c) > 1][:20]
            ],
        },
    }


def _weak_components(names: Set[str], edges: List[Tuple[str, str]]) -> List[List[str]]:
    adjacency: Dict[str, Set[str]] = {name: set() for name in names}
    for src, dst in edges:
        adjacency[src].add(dst)
        adjacency[dst].add(src)

    seen: Set[str] = set()
    components: List[List[str]] = []
    for name in sorted(names):
        if name in seen:
            continue
        queue = deque([name])
        seen.add(name)
        comp: List[str] = []
        while queue:
            node = queue.popleft()
            comp.append(node)
            for nxt in adjacency[node]:
                if nxt not in seen:
                    seen.add(nxt)
                    queue.append(nxt)
        components.append(sorted(comp))

    components.sort(key=lambda c: (-len(c), c[0]))
    return components


def _scc_components(names: Set[str], edges: List[Tuple[str, str]]) -> List[List[str]]:
    adjacency: Dict[str, List[str]] = {name: [] for name in names}
    for src, dst in edges:
        adjacency[src].append(dst)

    index = 0
    stack: List[str] = []
    on_stack: Set[str] = set()
    indices: Dict[str, int] = {}
    lowlink: Dict[str, int] = {}
    components: List[List[str]] = []

    def strongconnect(node: str) -> None:
        nonlocal index
        indices[node] = index
        lowlink[node] = index
        index += 1
        stack.append(node)
        on_stack.add(node)

        for nxt in adjacency[node]:
            if nxt not in indices:
                strongconnect(nxt)
                lowlink[node] = min(lowlink[node], lowlink[nxt])
            elif nxt in on_stack:
                lowlink[node] = min(lowlink[node], indices[nxt])

        if lowlink[node] == indices[node]:
            comp: List[str] = []
            while True:
                w = stack.pop()
                on_stack.remove(w)
                comp.append(w)
                if w == node:
                    break
            components.append(sorted(comp))

    for name in sorted(names):
        if name not in indices:
            strongconnect(name)

    components.sort(key=lambda c: (-len(c), c[0]))
    return components


def main() -> int:
    parser = argparse.ArgumentParser(description="Generate theorem dependency DAG for Coq files")
    parser.add_argument("--coq-root", default="coq", help="Path to Coq root directory")
    parser.add_argument("--out", default="artifacts/proof_dependency_dag.json", help="Output JSON path")
    args = parser.parse_args()

    repo_root = Path(__file__).resolve().parents[1]
    coq_root = (repo_root / args.coq_root).resolve()
    out_path = (repo_root / args.out).resolve()

    decls: List[Decl] = []
    for file_path in _coq_files(coq_root):
        decls.extend(_extract_decls(file_path, coq_root))

    by_name, edges = _build_graph(decls)
    rank = _rank(by_name, edges)

    payload = {
        "meta": {
            "coqRoot": str(coq_root.relative_to(repo_root)),
            "nodeCount": len(by_name),
            "edgeCount": len(edges),
            "note": "Edges are symbol-reference dependencies inferred from proof bodies.",
        },
        "nodes": [
            {
                "name": decl.name,
                "kind": decl.kind,
                "file": f"coq/{decl.file}",
                "line": decl.line,
            }
            for decl in sorted(by_name.values(), key=lambda d: (d.file, d.line, d.name))
        ],
        "edges": [{"from": src, "to": dst} for src, dst in edges],
        "rank": rank,
    }

    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")

    print(f"Wrote {out_path.relative_to(repo_root)}")
    print(f"Nodes: {payload['meta']['nodeCount']}, Edges: {payload['meta']['edgeCount']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
