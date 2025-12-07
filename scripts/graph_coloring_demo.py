#!/usr/bin/env python3
"""Graph 3-colouring demonstration for the Thiele Machine laboratory."""

from __future__ import annotations

import argparse
import itertools
import json
import math
import os
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, Iterable, List, Mapping, Optional, Sequence, Tuple

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

import z3

from thielecpu.mu import mu_breakdown
from thielecpu.receipts import ensure_kernel_keys

try:  # matplotlib is part of the editable install, but guard for clarity.
    import matplotlib.pyplot as plt
except Exception:  # pragma: no cover - plotting is optional for headless tests.
    plt = None


COLOR_NAMES = {0: "RED", 1: "GREEN", 2: "BLUE"}


@dataclass
class GraphSpec:
    """Static description of a 3-colourable graph."""

    name: str
    nodes: Sequence[int]
    edges: Sequence[Tuple[int, int]]
    description: str
    palette: Sequence[int] = (0, 1, 2)
    strategic_claims: Sequence[Tuple[int, int]] = ()
    canonical_coloring: Optional[Mapping[int, int]] = None
    max_bruteforce_nodes: int = 9

    def adjacency(self) -> Dict[int, List[int]]:
        graph: Dict[int, List[int]] = {node: [] for node in self.nodes}
        for u, v in self.edges:
            if u == v:
                continue
            graph[u].append(v)
            graph[v].append(u)
        return graph


@dataclass
class ActResult:
    """Structured metrics recorded for an experimental act."""

    label: str
    solution: Optional[Dict[int, int]]
    candidate_checks: int
    search_states: int
    mu_cost: float
    solver_queries: int
    log: List[str] = field(default_factory=list)
    reasoning_details: Optional[Dict[str, object]] = None


class GraphColoringOracle:
    """Reasoning oracle that answers structural questions about a graph."""

    def __init__(self, spec: GraphSpec) -> None:
        self._spec = spec
        self._variables = {node: z3.Int(f"c_{node}") for node in spec.nodes}
        self._base_solver = z3.Solver()
        for var in self._variables.values():
            self._base_solver.add(z3.Or([var == colour for colour in spec.palette]))
        for u, v in spec.edges:
            if u == v:
                continue
            self._base_solver.add(self._variables[u] != self._variables[v])
        self._base_constraints = tuple(self._base_solver.assertions())
        self.query_count = 0

    def _check(self, assignments: Mapping[int, int]) -> bool:
        solver = z3.Solver()
        solver.add(self._base_constraints)
        for node, colour in assignments.items():
            solver.add(self._variables[node] == colour)
        self.query_count += 1
        return solver.check() == z3.sat

    def possible_colours(
        self, node: int, assignments: Mapping[int, int]
    ) -> List[int]:
        options: List[int] = []
        for colour in self._spec.palette:
            candidate = dict(assignments)
            candidate[node] = colour
            if self._check(candidate):
                options.append(colour)
        return options


def _format_solution(solution: Mapping[int, int]) -> str:
    ordered = sorted(solution.items())
    chunks = [f"{node}:{COLOR_NAMES[colour]}" for node, colour in ordered]
    return "{" + ", ".join(chunks) + "}"


def _act_i_bruteforce(spec: GraphSpec) -> ActResult:
    if len(spec.nodes) > spec.max_bruteforce_nodes:
        log = [
            "ACT I – Blind exhaustive search",
            (
                "Graph has %d nodes; skipping exhaustive enumeration (limit %d)."
                % (len(spec.nodes), spec.max_bruteforce_nodes)
            ),
        ]
        return ActResult(
            label="Act I",
            solution=None,
            candidate_checks=0,
            search_states=0,
            mu_cost=0.0,
            solver_queries=0,
            log=log,
        )

    index_of = {node: idx for idx, node in enumerate(spec.nodes)}
    palette = list(spec.palette)
    attempts = 0
    log: List[str] = ["ACT I – Blind exhaustive search"]
    solution: Optional[Dict[int, int]] = None
    for colouring in itertools.product(palette, repeat=len(spec.nodes)):
        attempts += 1
        valid = True
        for u, v in spec.edges:
            if colouring[index_of[u]] == colouring[index_of[v]]:
                valid = False
                break
        if valid:
            solution = {node: colouring[index_of[node]] for node in spec.nodes}
            log.append(
                f"Witness located after {attempts} assignments: {_format_solution(solution)}"
            )
            break
    else:
        log.append("No valid colouring discovered in search horizon.")

    return ActResult(
        label="Act I",
        solution=solution,
        candidate_checks=attempts,
        search_states=attempts,
        mu_cost=0.0,
        solver_queries=0,
        log=log,
    )


def _act_ii_backtracking(spec: GraphSpec) -> ActResult:
    adjacency = spec.adjacency()
    ordering = sorted(spec.nodes, key=lambda n: len(adjacency[n]), reverse=True)
    palette = list(spec.palette)
    attempts = 0
    log: List[str] = ["ACT II – Classical heuristic backtracking"]
    solution: Optional[Dict[int, int]] = None
    assignments: Dict[int, int] = {}

    def backtrack(position: int) -> bool:
        nonlocal attempts, solution
        if position == len(ordering):
            solution = dict(assignments)
            log.append(
                f"Backtracking recovered witness after {attempts} branch attempts:"
                f" {_format_solution(solution)}"
            )
            return True

        node = ordering[position]
        forbidden = {assignments[nbr] for nbr in adjacency[node] if nbr in assignments}
        for colour in palette:
            attempts += 1
            if colour in forbidden:
                continue
            assignments[node] = colour
            if backtrack(position + 1):
                return True
            del assignments[node]
        return False

    backtrack(0)
    if solution is None:
        log.append("Backtracking exhausted search space without locating a witness.")

    return ActResult(
        label="Act II",
        solution=solution,
        candidate_checks=attempts,
        search_states=attempts,
        mu_cost=0.0,
        solver_queries=0,
        log=log,
    )


def _act_iii_reasoning(spec: GraphSpec) -> ActResult:
    oracle = GraphColoringOracle(spec)
    assignments: Dict[int, int] = {}
    log: List[str] = [
        "ACT III – Strategic claims with oracle-guided propagation",
    ]

    domains = {node: set(spec.palette) for node in spec.nodes}
    mu_events: List[Dict[str, object]] = []
    mu_total = 0.0

    def record_mu(expr: str, before: int, after: int, context: str) -> None:
        nonlocal mu_total
        breakdown = mu_breakdown(expr, before, after)
        mu_total += breakdown.total
        mu_events.append(
            {
                "context": context,
                "expr": expr,
                "canonical": breakdown.canonical,
                "before": before,
                "after": after,
                "question_bits": breakdown.question_bits,
                "information_gain": breakdown.information_gain,
                "mu_total": breakdown.total,
            }
        )

    for node, colour in spec.strategic_claims:
        assignments[node] = colour
        before = max(len(domains.get(node, set(spec.palette))), 1)
        domains[node] = {colour}
        expr = f"(claim node {node} {COLOR_NAMES[colour].lower()})"
        record_mu(expr, before, 1, "strategic_claim")
        log.append(
            f"CLAIM: Node {node} := {COLOR_NAMES[colour]} (μ-cost {mu_events[-1]['mu_total']:.4f} bits)"
        )

    reasoning_summary: Dict[str, object] = {
        "claims": [
            {"node": node, "colour": COLOR_NAMES[colour]} for node, colour in spec.strategic_claims
        ],
        "propagation": [],
        "mu_events": mu_events,
    }

    changed = True
    while changed:
        changed = False
        for node in spec.nodes:
            if node in assignments:
                continue
            options = oracle.possible_colours(node, assignments)
            before = max(len(domains.get(node, set(spec.palette))), 1)
            after = max(len(options), 1)
            expr = f"(oracle node {node})"
            record_mu(expr, before, after, "oracle_query")
            reasoning_summary["propagation"].append(
                {
                    "node": node,
                    "options": [COLOR_NAMES[c] for c in options],
                    "mu_cost": mu_events[-1]["mu_total"],
                }
            )
            log.append(
                f"ORACLE: Node {node} admissible colours → "
                f"{[COLOR_NAMES[c] for c in options]} (μ-cost {mu_events[-1]['mu_total']:.4f} bits)"
            )
            if not options:
                raise RuntimeError(
                    f"Oracle detected contradiction when reasoning about node {node}."
                )
            if len(options) == 1:
                assignments[node] = options[0]
                log.append(
                    f"FORCED: Node {node} := {COLOR_NAMES[options[0]]}"
                )
                changed = True
            domains[node] = set(options)

    remaining = [node for node in spec.nodes if node not in assignments]
    targeted_checks = 0

    def targeted_search(position: int) -> Optional[Dict[int, int]]:
        nonlocal targeted_checks
        if position == len(remaining):
            return dict(assignments)

        node = remaining[position]
        options = oracle.possible_colours(node, assignments)
        before = max(len(domains.get(node, set(spec.palette))), 1)
        after = max(len(options), 1)
        expr = f"(oracle node {node})"
        record_mu(expr, before, after, "oracle_query")
        domains[node] = set(options)
        for colour in options:
            assignments[node] = colour
            targeted_checks += 1
            result = targeted_search(position + 1)
            if result is not None:
                return result
            del assignments[node]
        return None

    solution = targeted_search(0) if remaining else dict(assignments)
    if solution is None:
        raise RuntimeError("Targeted verification failed to recover a witness.")

    log.append(
        f"Witness recovered after oracle guidance: {_format_solution(solution)}"
    )

    reasoning_summary["oracle_queries"] = oracle.query_count
    reasoning_summary["forced_assignments"] = {
        str(node): COLOR_NAMES[colour]
        for node, colour in assignments.items()
    }
    reasoning_summary["targeted_checks"] = targeted_checks
    reasoning_summary["mu_total"] = mu_total

    return ActResult(
        label="Act III",
        solution=solution,
        candidate_checks=targeted_checks,
        search_states=targeted_checks,
        mu_cost=mu_total,
        solver_queries=oracle.query_count,
        log=log,
        reasoning_details=reasoning_summary,
    )


def _write_act_outputs(root: Path, spec: GraphSpec, result: ActResult) -> Dict[str, object]:
    act_dir = root / spec.name / result.label.lower().replace(" ", "_")
    act_dir.mkdir(parents=True, exist_ok=True)

    summary = {
        "act": result.label,
        "graph": spec.name,
        "candidate_checks": result.candidate_checks,
        "search_states": result.search_states,
        "mu_cost": result.mu_cost,
        "solver_queries": result.solver_queries,
        "solution": {
            str(node): COLOR_NAMES[colour]
            for node, colour in (result.solution or {}).items()
        },
    }

    (act_dir / "summary.json").write_text(json.dumps(summary, indent=2), encoding="utf-8")
    (act_dir / "step_receipts.json").write_text(
        json.dumps(result.log, indent=2), encoding="utf-8"
    )
    if result.reasoning_details is not None:
        (act_dir / "reasoning_summary.json").write_text(
            json.dumps(result.reasoning_details, indent=2), encoding="utf-8"
        )
    return summary


def _analysis_report(
    spec: GraphSpec, act_summaries: Sequence[Dict[str, object]]
) -> Dict[str, object]:
    act_lookup = {summary["act"]: summary for summary in act_summaries}
    classical_checks = float(act_lookup.get("Act I", {}).get("candidate_checks", math.nan))
    targeted_checks = float(
        act_lookup.get("Act III", {}).get("candidate_checks", math.nan)
    )
    reduction = None
    if not math.isnan(classical_checks) and not math.isnan(targeted_checks) and targeted_checks > 0:
        reduction = classical_checks / targeted_checks

    return {
        "graph": spec.name,
        "description": spec.description,
        "nodes": len(spec.nodes),
        "edges": len(spec.edges),
        "palette": [COLOR_NAMES[c] for c in spec.palette],
        "acts": act_summaries,
        "comparative": {
            "classical_candidates": classical_checks,
            "oracle_guided_candidates": targeted_checks,
            "search_reduction_factor": reduction,
        },
    }


def run_experiment(spec: GraphSpec, output_root: Path) -> Dict[str, object]:
    results = [
        _act_i_bruteforce(spec),
        _act_ii_backtracking(spec),
        _act_iii_reasoning(spec),
    ]

    summaries = [_write_act_outputs(output_root, spec, result) for result in results]
    report = _analysis_report(spec, summaries)
    graph_root = output_root / spec.name
    graph_root.mkdir(parents=True, exist_ok=True)
    report_path = graph_root / "analysis_report.json"
    report_path.write_text(json.dumps(report, indent=2), encoding="utf-8")
    return report


def build_cascade_graph(blocks: int) -> GraphSpec:
    if blocks < 1:
        raise ValueError("Cascade graphs require at least one block")

    node_count = 3 * blocks
    nodes = tuple(range(node_count))
    edges: List[Tuple[int, int]] = []

    # Anchor triangle for the first block.
    if blocks >= 1:
        edges.extend([(0, 1), (1, 2), (2, 0)])

    for block in range(1, blocks):
        base = 3 * block
        prev = 3 * (block - 1)
        attachments = [
            (prev + 1, prev + 2),
            (prev + 0, prev + 2),
            (prev + 0, prev + 1),
        ]
        for offset, (u, v) in enumerate(attachments):
            node = base + offset
            edges.append((node, u))
            edges.append((node, v))

    name = "triadic_cascade" if blocks == 3 else f"cascade_{blocks}"
    description = (
        f"{node_count}-node triadic cascade with a unique 3-colouring once two "
        "anchors are fixed."
    )

    return GraphSpec(
        name=name,
        nodes=nodes,
        edges=tuple(edges),
        description=description,
        strategic_claims=((0, 0), (1, 1)),
        canonical_coloring={i: i % 3 for i in range(node_count)},
        max_bruteforce_nodes=9,
    )


GRAPH_LIBRARY: Dict[str, GraphSpec] = {}
for blocks in (3, 5, 7, 10):
    spec = build_cascade_graph(blocks)
    GRAPH_LIBRARY[spec.name] = spec

DEFAULT_SUITE = ["triadic_cascade", "cascade_5", "cascade_7", "cascade_10"]


def _resolve_graph_specs(selection: Optional[Sequence[str]]) -> List[GraphSpec]:
    if not selection:
        selection = DEFAULT_SUITE

    specs: List[GraphSpec] = []
    for token in selection:
        if token in GRAPH_LIBRARY:
            specs.append(GRAPH_LIBRARY[token])
            continue

        candidate = token
        if token.startswith("cascade_"):
            candidate = token.split("_", 1)[1]

        if candidate.isdigit():
            blocks = int(candidate)
            spec = build_cascade_graph(blocks)
            GRAPH_LIBRARY[spec.name] = spec
            specs.append(spec)
            continue

        raise SystemExit(
            f"Unknown graph '{token}'. Available: {', '.join(sorted(GRAPH_LIBRARY))}"
        )

    seen: set[str] = set()
    ordered: List[GraphSpec] = []
    for spec in specs:
        if spec.name in seen:
            continue
        seen.add(spec.name)
        ordered.append(spec)
    return ordered


def _summarise_scaling(reports: Sequence[Dict[str, object]]) -> List[Dict[str, object]]:
    table: List[Dict[str, object]] = []
    for report in reports:
        acts = {act["act"]: act for act in report.get("acts", [])}
        act_ii = acts.get("Act II", {})
        act_iii = acts.get("Act III", {})
        table.append(
            {
                "graph": report.get("graph"),
                "nodes": report.get("nodes"),
                "edges": report.get("edges"),
                "act_ii_candidate_checks": int(act_ii.get("candidate_checks", 0) or 0),
                "act_iii_candidate_checks": int(act_iii.get("candidate_checks", 0) or 0),
                "act_iii_mu_cost": float(act_iii.get("mu_cost", 0.0) or 0.0),
            }
        )
    return table


def _plot_scaling(table: Sequence[Mapping[str, object]], output_dir: Path) -> Optional[Path]:
    if plt is None or not table:
        return None

    nodes: List[int] = [int(row.get("nodes", 0) or 0) for row in table]
    classical = [max(1, int(row.get("act_ii_candidate_checks", 0) or 0)) for row in table]
    thiele = [max(1, int(row.get("act_iii_candidate_checks", 0) or 0)) for row in table]

    plt.figure(figsize=(7, 4))
    plt.plot(nodes, [math.log10(val) for val in classical], marker="o", label="Act II log10 candidates")
    plt.plot(nodes, [math.log10(val) for val in thiele], marker="o", label="Act III log10 candidates")
    plt.xlabel("Number of nodes")
    plt.ylabel("log10(candidate checks)")
    plt.title("Graph colouring workload vs reasoning-guided workload")
    plt.grid(True, which="both", linestyle="--", alpha=0.4)
    plt.legend()

    output_dir.mkdir(parents=True, exist_ok=True)
    plot_path = output_dir / "scaling_plot.png"
    plt.tight_layout()
    plt.savefig(plot_path, dpi=200)
    plt.close()
    return plot_path


def _parse_args(argv: Optional[Sequence[str]] = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path("results/graphs"),
        help="Directory for receipts and analysis artefacts.",
    )
    parser.add_argument(
        "--graphs",
        nargs="+",
        help="Graphs to execute (names from the library or cascade sizes).",
    )
    parser.add_argument(
        "--no-plot",
        action="store_true",
        help="Skip matplotlib scaling plot generation.",
    )
    return parser.parse_args(argv)


def main(argv: Optional[Sequence[str]] = None) -> None:
    args = _parse_args(argv)
    args.output_dir.mkdir(parents=True, exist_ok=True)
    specs = _resolve_graph_specs(args.graphs)

    ensure_kernel_keys()
    reports: List[Dict[str, object]] = []
    for spec in specs:
        reports.append(run_experiment(spec, args.output_dir))

    scaling_table = _summarise_scaling(reports)
    scaling_path = args.output_dir / "scaling_summary.json"
    scaling_path.write_text(json.dumps(scaling_table, indent=2), encoding="utf-8")

    plot_path = None
    if not args.no_plot:
        plot_path = _plot_scaling(scaling_table, args.output_dir)

    print("=" * 72)
    print("Thiele Machine Graph Colouring Demonstration Suite")
    for report in reports:
        print("-" * 72)
        print(
            f"Graph: {report['graph']} ({report['nodes']} nodes, {report['edges']} edges)"
        )
        for act in report["acts"]:
            print(
                f"{act['act']}: candidates={act['candidate_checks']:,} "
                f"μ-cost={act['mu_cost']:.1f} solution={act['solution']}"
            )
    print("=" * 72)
    print("Scaling summary:")
    for row in scaling_table:
        print(
            f"  {row['graph']}: nodes={row['nodes']} Act II={row['act_ii_candidate_checks']} "
            f"Act III={row['act_iii_candidate_checks']} μ-cost={row['act_iii_mu_cost']:.1f}"
        )

    print("Receipts stored in", args.output_dir.resolve())
    print("Scaling data:", scaling_path)
    if plot_path is None and not args.no_plot:
        print("Scaling plot skipped (matplotlib unavailable).")
    elif plot_path is not None:
        print("Scaling plot:", plot_path)


if __name__ == "__main__":
    main()

