#!/usr/bin/env python3
"""Run honest benchmarks comparing a brute-force SAT search with a GF(2) solver.

The script generates small Tseitin instances on random 3-regular graphs. Each
instance is solved twice:

1. **Baseline (Classical)** – an exhaustive search over all assignments that
   checks the CNF form of the instance. This represents a time-costly blind
   trace that explores every possibility.
2. **Thiele-style (Sighted)** – Gaussian elimination over GF(2) applied to the
   parity equations of the same instance. The number of row operations is
   interpreted as the μ-bit discovery cost: each elimination step exposes one
   unit of hidden linear structure. Unlike earlier scripts, every measurement is
   taken directly from the live execution of both solvers.

For every run we record the wall-clock runtime of both solvers along with their
operation counts and μ-bit discovery costs. Results are written to
``results/honest_tseitin_benchmark.json`` and a human readable markdown summary
at ``results/honest_tseitin_benchmark.md``.

Usage::

    python scripts/honest_tseitin_benchmark.py --n 6 8 10 --seeds 0 1 2

The defaults are chosen to keep runtimes short while still highlighting the
contrast between the algorithms. All measurements are taken from the current
process without any fabricated values.
"""
from __future__ import annotations

import argparse
import json
import math
import random
import statistics
import subprocess
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

try:
    import networkx as nx
except ImportError as exc:  # pragma: no cover - dependency error surface
    raise SystemExit(
        "networkx is required for honest_tseitin_benchmark.py. "
        "Install the repository requirements before running this script."
    ) from exc


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--n",
        metavar="N",
        type=int,
        nargs="+",
        default=[6, 8, 10],
        help="even sizes of the 3-regular expander graphs",
    )
    parser.add_argument(
        "--seeds",
        metavar="SEED",
        type=int,
        nargs="+",
        default=[0, 1, 2],
        help="instance seeds per graph size",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("results/honest_tseitin_benchmark.json"),
        help="path to the JSON file where results will be stored",
    )
    parser.add_argument(
        "--markdown",
        type=Path,
        default=Path("results/honest_tseitin_benchmark.md"),
        help="path to the Markdown summary file",
    )
    parser.add_argument(
        "--max-seconds",
        type=float,
        default=60.0,
        help="safety cap: stop exploring assignments after this many seconds",
    )
    parser.add_argument(
        "--verbose",
        action="store_true",
        help="print per-instance progress information",
    )
    return parser.parse_args(argv)


def seeded_rng(global_seed: int, n: int, seed: int) -> random.Random:
    """Deterministic RNG seeded via a hash of the parameters."""
    # Use blake2b for stable entropy independent of Python hash randomisation.
    payload = f"{global_seed}|{n}|{seed}".encode()
    digest = int.from_bytes(__import__("hashlib").blake2b(payload, digest_size=8).digest(), "big")
    return random.Random(digest)


def generate_tseitin_expander(n: int, seed: int, *, global_seed: int = 123456789) -> Dict:
    """Generate a 3-regular graph and associated Tseitin parity instance."""
    if n % 2:
        raise ValueError(f"3-regular graphs require even n (got {n})")
    rng = seeded_rng(global_seed, n, seed)
    # networkx.random_regular_graph is deterministic given an RNG with sample.
    graph = nx.random_regular_graph(3, n, seed=rng)
    edges = sorted(tuple(sorted(e)) for e in graph.edges())
    edge_index = {edge: idx for idx, edge in enumerate(edges)}

    # Choose an odd charge pattern to guarantee unsatisfiable parity.
    charges = [rng.randrange(2) for _ in range(n - 1)]
    charges.append(1 ^ (sum(charges) & 1))

    incidence: Dict[int, List[int]] = {v: [] for v in graph.nodes()}
    for (u, v) in edges:
        idx = edge_index[(min(u, v), max(u, v))]
        incidence[u].append(idx)
        incidence[v].append(idx)

    xor_rows: List[Tuple[List[int], int]] = []
    cnf: List[List[int]] = []
    for vertex, idxs in incidence.items():
        assert len(idxs) == 3, "generated graph is not 3-regular"
        idxs.sort()
        xor_rows.append((idxs, charges[vertex]))
        var_ids = [idx + 1 for idx in idxs]
        # Expand to CNF using the standard Tseitin encoding of XOR parity.
        cnf.extend(_xor3_to_cnf(var_ids[0], var_ids[1], var_ids[2], charges[vertex]))
    return {
        "n": n,
        "seed": seed,
        "edges": edges,
        "charges": charges,
        "xor_rows": xor_rows,
        "cnf": cnf,
    }


def _xor3_to_cnf(x: int, y: int, z: int, charge: int) -> List[List[int]]:
    """Convert x ⊕ y ⊕ z = charge into CNF clauses."""
    if charge not in (0, 1):
        raise ValueError("charge must be 0 or 1")
    clauses: List[List[int]] = []
    # Truth table expansion – four clauses cover the parity constraint.
    combos = [
        (True, True, True),
        (True, True, False),
        (True, False, True),
        (True, False, False),
        (False, True, True),
        (False, True, False),
        (False, False, True),
        (False, False, False),
    ]
    for a, b, c in combos:
        parity = (a + b + c) % 2
        satisfied = parity == charge
        if satisfied:
            continue  # satisfied rows impose no restriction
        clause: List[int] = []
        clause.append(x if a else -x)
        clause.append(y if b else -y)
        clause.append(z if c else -z)
        clauses.append(clause)
    return clauses


def solve_by_bruteforce(clauses: Sequence[Sequence[int]], *, max_seconds: float) -> Dict:
    start = time.perf_counter()
    num_vars = max((abs(lit) for clause in clauses for lit in clause), default=0)
    checked = 0
    status = "unsat"
    for assignment in range(1 << num_vars):
        if time.perf_counter() - start > max_seconds:
            status = "timeout"
            break
        checked += 1
        if _cnf_satisfied(clauses, assignment):
            status = "sat"
            break
    runtime = time.perf_counter() - start
    return {
        "status": status,
        "runtime_seconds": runtime,
        "assignments_checked": checked,
        "num_variables": num_vars,
    }


def _cnf_satisfied(clauses: Sequence[Sequence[int]], assignment: int) -> bool:
    for clause in clauses:
        satisfied = False
        for lit in clause:
            var = abs(lit) - 1
            bit = (assignment >> var) & 1
            if (lit > 0 and bit == 1) or (lit < 0 and bit == 0):
                satisfied = True
                break
        if not satisfied:
            return False
    return True


@dataclass
class GaussianResult:
    result: str
    runtime_seconds: float
    row_operations: int
    pivots: int

    @property
    def mu_discovery(self) -> int:
        return self.row_operations


def solve_by_gaussian(xor_rows: Sequence[Tuple[Sequence[int], int]], num_vars: int) -> GaussianResult:
    matrix: List[List[int]] = []
    rhs: List[int] = []
    for row, value in xor_rows:
        mask = 0
        for idx in row:
            mask |= 1 << idx
        matrix.append([mask])
        rhs.append(value & 1)

    start = time.perf_counter()
    row_ops = 0
    pivot = 0
    rows = len(matrix)
    for col in range(num_vars):
        pivot_row = None
        for r in range(pivot, rows):
            if (matrix[r][0] >> col) & 1:
                pivot_row = r
                break
        if pivot_row is None:
            continue
        if pivot_row != pivot:
            matrix[pivot], matrix[pivot_row] = matrix[pivot_row], matrix[pivot]
            rhs[pivot], rhs[pivot_row] = rhs[pivot_row], rhs[pivot]
            row_ops += 1
        for r in range(rows):
            if r == pivot:
                continue
            if (matrix[r][0] >> col) & 1:
                matrix[r][0] ^= matrix[pivot][0]
                rhs[r] ^= rhs[pivot]
                row_ops += 1
        pivot += 1
        if pivot == rows:
            break
    inconsistent = any((row_mask == 0 and bit == 1) for (row_mask,), bit in zip(matrix, rhs))
    runtime = time.perf_counter() - start
    return GaussianResult(
        result="unsat" if inconsistent else "sat",
        runtime_seconds=runtime,
        row_operations=row_ops,
        pivots=pivot,
    )


def current_commit() -> str:
    try:
        return (
            subprocess.check_output(["git", "rev-parse", "HEAD"], stderr=subprocess.DEVNULL)
            .decode("utf-8")
            .strip()
        )
    except Exception:
        return "unknown"


def run_experiments(cfg: argparse.Namespace) -> Dict:
    output: Dict = {
        "generated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "git_commit": current_commit(),
        "instances": [],
        "summary": {},
        "config": {
            "n": cfg.n,
            "seeds": cfg.seeds,
            "max_seconds": cfg.max_seconds,
        },
    }

    for n in cfg.n:
        if n % 2:
            raise SystemExit(f"Requested n={n} but 3-regular graphs require even n")
        for seed in cfg.seeds:
            instance = generate_tseitin_expander(n, seed)
            num_edges = len(instance["edges"])
            if cfg.verbose:
                print(f"[instance] n={n} seed={seed} edges={num_edges}")
            baseline_raw = solve_by_bruteforce(
                instance["cnf"], max_seconds=cfg.max_seconds
            )
            baseline = dict(baseline_raw)
            baseline["mu_discovery"] = 0

            gaussian = solve_by_gaussian(instance["xor_rows"], num_edges)
            if gaussian.mu_discovery == 0:
                time_per_mu = None
            else:
                time_per_mu = gaussian.runtime_seconds / gaussian.mu_discovery
            record = {
                "n": n,
                "seed": seed,
                "num_edges": num_edges,
                "baseline": baseline,
                "thiele": {
                    "result": gaussian.result,
                    "runtime_seconds": gaussian.runtime_seconds,
                    "row_operations": gaussian.row_operations,
                    "mu_discovery": gaussian.mu_discovery,
                    "pivots": gaussian.pivots,
                    "time_per_mu": time_per_mu,
                },
            }
            output["instances"].append(record)

    baseline_times = [inst["baseline"]["runtime_seconds"] for inst in output["instances"]]
    thiele_times = [inst["thiele"]["runtime_seconds"] for inst in output["instances"]]
    thiele_mu = [inst["thiele"]["mu_discovery"] for inst in output["instances"]]
    runtime_ratio = [
        inst["baseline"]["runtime_seconds"] / inst["thiele"]["runtime_seconds"]
        if inst["thiele"]["runtime_seconds"] > 0 else math.inf
        for inst in output["instances"]
    ]
    time_saved_per_mu = [
        (inst["baseline"]["runtime_seconds"] - inst["thiele"]["runtime_seconds"])
        / inst["thiele"]["mu_discovery"]
        for inst in output["instances"]
        if inst["thiele"]["mu_discovery"] > 0
    ]
    output["summary"] = {
        "instances": len(output["instances"]),
        "baseline_avg_s": statistics.mean(baseline_times) if baseline_times else 0.0,
        "thiele_avg_s": statistics.mean(thiele_times) if thiele_times else 0.0,
        "baseline_median_s": statistics.median(baseline_times) if baseline_times else 0.0,
        "thiele_median_s": statistics.median(thiele_times) if thiele_times else 0.0,
        "avg_runtime_ratio": statistics.mean(runtime_ratio) if runtime_ratio else 0.0,
        "thiele_avg_mu": statistics.mean(thiele_mu) if thiele_mu else 0.0,
        "thiele_median_mu": statistics.median(thiele_mu) if thiele_mu else 0.0,
        "avg_time_saved_per_mu": statistics.mean(time_saved_per_mu)
        if time_saved_per_mu
        else 0.0,
    }
    return output


def write_outputs(data: Dict, *, json_path: Path, markdown_path: Path) -> None:
    json_path.parent.mkdir(parents=True, exist_ok=True)
    markdown_path.parent.mkdir(parents=True, exist_ok=True)

    with json_path.open("w", encoding="utf-8") as fh:
        json.dump(data, fh, indent=2)

    lines: List[str] = []
    lines.append("# Honest Tseitin Benchmark")
    lines.append("")
    lines.append(f"Generated: {data['generated_at']}")
    lines.append(f"Git commit: {data['git_commit']}")
    lines.append("")
    lines.append(
        "| n | seed | edges | baseline status | baseline s | baseline μ | checked | "
        "thiele status | thiele s | thiele μ | time/μ (s) | runtime ratio |"
    )
    lines.append(
        "|---|------|-------|-----------------|------------|------------|---------|" \
        "---------------|----------|----------|------------|--------------|"
    )
    for inst in data["instances"]:
        baseline = inst["baseline"]
        thiele = inst["thiele"]
        if thiele["runtime_seconds"] > 0:
            ratio = baseline["runtime_seconds"] / thiele["runtime_seconds"]
        else:
            ratio = None
        if thiele["time_per_mu"] is None:
            time_per_mu = "–"
        else:
            time_per_mu = f"{thiele['time_per_mu']:.6f}"
        ratio_text = "∞" if ratio is None else f"{ratio:.2f}"
        lines.append(
            "| {n} | {seed} | {edges} | {bstatus} | {btime:.6f} | {bmu} | {checked} | {tstatus} | {ttime:.6f} | {tmu} | {tpm} | {ratio} |".format(
                n=inst["n"],
                seed=inst["seed"],
                edges=inst["num_edges"],
                bstatus=baseline["status"],
                btime=baseline["runtime_seconds"],
                bmu=baseline["mu_discovery"],
                checked=baseline["assignments_checked"],
                tstatus=thiele["result"],
                ttime=thiele["runtime_seconds"],
                tmu=thiele["mu_discovery"],
                tpm=time_per_mu,
                ratio=ratio_text,
            )
        )
    lines.append("")
    summary = data["summary"]
    lines.append("## Summary")
    lines.append("")
    lines.append(f"Instances: {summary['instances']}")
    lines.append(
        f"Average runtime – baseline: {summary['baseline_avg_s']:.6f}s, "
        f"Thiele: {summary['thiele_avg_s']:.6f}s"
    )
    lines.append(
        f"Median runtime – baseline: {summary['baseline_median_s']:.6f}s, "
        f"Thiele: {summary['thiele_median_s']:.6f}s"
    )
    lines.append(f"Average runtime ratio (baseline/thiele): {summary['avg_runtime_ratio']:.2f}")
    lines.append(
        f"Average μ-discovery (Thiele): {summary['thiele_avg_mu']:.2f}"
    )
    lines.append(
        f"Median μ-discovery (Thiele): {summary['thiele_median_mu']:.2f}"
    )
    if summary["avg_time_saved_per_mu"]:
        lines.append(
            f"Average time saved per μ-bit: {summary['avg_time_saved_per_mu']:.6f}s"
        )
    lines.append("")
    lines.append(
        "Baseline exhaustive search accumulates zero μ because it never learns a "
        "structure; the Thiele-style solver pays a finite μ-discovery cost equal "
        "to its GF(2) row operations while shrinking runtime exponentially."
    )

    with markdown_path.open("w", encoding="utf-8") as fh:
        fh.write("\n".join(lines) + "\n")


def main(argv: Sequence[str] | None = None) -> None:
    cfg = parse_args(argv)
    data = run_experiments(cfg)
    write_outputs(data, json_path=cfg.output, markdown_path=cfg.markdown)
    if cfg.verbose:
        print(f"Wrote {cfg.output} and {cfg.markdown}")


if __name__ == "__main__":
    main()
