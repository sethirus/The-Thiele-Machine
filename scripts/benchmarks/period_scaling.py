#!/usr/bin/env python3
"""Period-scaling benchmark for Thiele Machine period oracle.

Writes CSV to artifacts/period_scaling.csv with columns:
n,a,period,mu_cost,solver_queries,wall_time,cpu_time,success,num_factors
"""

from __future__ import annotations

import csv
import math
import sys
import time
from pathlib import Path
from typing import List, Tuple


REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

from thielecpu.shor_oracle import find_period_with_claims


def choose_coprime_base(n: int) -> int:
    for a in range(2, min(n, 50)):
        if math.gcd(a, n) == 1:
            return a
    # fallback: scan further
    for a in range(2, n):
        if math.gcd(a, n) == 1:
            return a
    raise ValueError("no coprime base found")


def shor_reduction_factors(n: int, a: int, r: int) -> List[int]:
    if r <= 0 or r % 2 != 0:
        return []
    half = r // 2
    term = pow(a, half, n)
    if term == 1 or term == n - 1:
        return []
    f1 = math.gcd(term - 1, n)
    f2 = math.gcd(term + 1, n)
    fs = []
    for f in (f1, f2):
        if 1 < f < n and f not in fs:
            fs.append(f)
    return fs


def ensure_artifacts_dir(path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)


def run_bench(ns: List[int], out_path: Path) -> None:
    ensure_artifacts_dir(out_path)
    with out_path.open("w", newline="") as csvfile:
        writer = csv.writer(csvfile)
        writer.writerow([
            "n",
            "a",
            "period",
            "mu_cost",
            "solver_queries",
            "wall_time",
            "cpu_time",
            "success",
            "num_factors",
        ])

        for n in ns:
            a = choose_coprime_base(n)
            print(f"Running N={n}, base a={a}")
            t0 = time.time()
            c0 = time.process_time()
            try:
                result = find_period_with_claims(n, a, max_period=2 * n)
            except Exception as e:
                print(f"  ERROR for N={n}: {e}")
                writer.writerow([n, a, "error", 0, 0, 0, 0, False, 0])
                continue
            wall = time.time() - t0
            cpu = time.process_time() - c0

            period = result.period
            mu_cost = float(result.mu_cost)
            solver_queries = int(result.solver_queries)
            factors = shor_reduction_factors(n, a, period)
            success = len(factors) >= 2

            writer.writerow([
                n,
                a,
                period,
                mu_cost,
                solver_queries,
                f"{wall:.6f}",
                f"{cpu:.6f}",
                success,
                len(factors),
            ])

            print(f"  period={period}, μ={mu_cost:.2f}, queries={solver_queries}, wall={wall:.3f}s")


def main() -> None:
    # Choose a set of Ns to run (small → medium). Add or modify as needed.
    ns = [15, 21, 35, 55, 77, 91, 143, 3233]
    out = REPO_ROOT / "artifacts" / "period_scaling.csv"
    run_bench(ns, out)
    print("Wrote results to:", out)


if __name__ == "__main__":
    main()
