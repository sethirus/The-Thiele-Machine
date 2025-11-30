#!/usr/bin/env python3
"""
Benchmark Harness for Blind vs Sighted Thiele Machine Comparison

This is the primary tool for running reproducible, falsifiable benchmarks
that demonstrate the sight vs blind separation.

USAGE:
    python tools/run_benchmarks.py --family=tseitin --mode=both --min-n=5 --max-n=20
    python tools/run_benchmarks.py --family=all --repetitions=3

OUTPUT:
    - CSV file with all results: artifacts/benchmarks/results.csv
    - JSON records for each run: artifacts/benchmarks/runs/
    - Summary statistics: artifacts/benchmarks/summary.json
    - Scaling plots (if matplotlib available): artifacts/benchmarks/plots/

FALSIFIABILITY:
    All runs are deterministic given (family, size, seed).
    Anyone can reproduce results and verify/falsify scaling claims.
"""

from __future__ import annotations

import argparse
import csv
import json
import sys
import time
from dataclasses import asdict
from datetime import datetime
from pathlib import Path
from typing import Any, Dict, List, Optional

# Add repo root to path
REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from thielecpu.benchmarks.problem_families import (
    BenchmarkInstance,
    generate_instance,
    list_families,
    PROBLEM_FAMILIES,
)
from thielecpu.benchmarks.solvers import (
    BlindSolver,
    SightedSolver,
    SolverResult,
)


def run_benchmark(
    family: str,
    size: int,
    seed: int,
    mode: str,
    timeout_s: float,
) -> SolverResult:
    """Run a single benchmark."""
    
    # Generate instance (same API for all families)
    instance = generate_instance(family, size, seed)
    
    # Run appropriate solver
    if mode == "blind":
        solver = BlindSolver(timeout_s=timeout_s)
        return solver.solve(instance)
    else:
        solver = SightedSolver(timeout_s=timeout_s)
        return solver.solve(instance)


def run_benchmark_suite(
    families: List[str],
    min_n: int,
    max_n: int,
    step_n: int,
    mode: str,
    repetitions: int,
    timeout_s: float,
    output_dir: Path,
) -> List[Dict[str, Any]]:
    """Run a full benchmark suite."""
    
    results = []
    total_runs = 0
    
    # Count total runs
    for family in families:
        for n in range(min_n, max_n + 1, step_n):
            for rep in range(repetitions):
                total_runs += (2 if mode == "both" else 1)
    
    print(f"Running {total_runs} benchmarks...")
    print(f"Families: {families}")
    print(f"Size range: {min_n} to {max_n} (step {step_n})")
    print(f"Repetitions: {repetitions}")
    print(f"Mode: {mode}")
    print(f"Timeout: {timeout_s}s")
    print()
    
    run_count = 0
    for family in families:
        print(f"\n{'='*60}")
        print(f"FAMILY: {family.upper()}")
        print(f"{'='*60}")
        
        for n in range(min_n, max_n + 1, step_n):
            for rep in range(repetitions):
                seed = 42 + rep  # Deterministic seeds
                
                # Handle period_finding differently
                if family == "period_finding":
                    # Use primes for N, small bases
                    n_values = [15, 21, 35, 55, 77, 91, 143]
                    if n - min_n < len(n_values):
                        actual_n = n_values[n - min_n]
                        actual_seed = 2 + rep  # bases: 2, 3, 4, ...
                    else:
                        continue
                else:
                    actual_n = n
                    actual_seed = seed
                
                modes_to_run = ["blind", "sighted"] if mode == "both" else [mode]
                
                for solver_mode in modes_to_run:
                    run_count += 1
                    progress = f"[{run_count}/{total_runs}]"
                    
                    print(f"{progress} {family} n={actual_n} seed={actual_seed} mode={solver_mode}...", end=" ", flush=True)
                    
                    try:
                        result = run_benchmark(
                            family=family,
                            size=actual_n,
                            seed=actual_seed,
                            mode=solver_mode,
                            timeout_s=timeout_s,
                        )
                        
                        print(f"{result.status} ({result.wall_time_s:.3f}s, μ={result.mu_total:.1f})")
                        
                        results.append(result.to_dict())
                        
                        # Save individual result
                        run_dir = output_dir / "runs" / family / f"n{actual_n}_s{actual_seed}_{solver_mode}"
                        run_dir.mkdir(parents=True, exist_ok=True)
                        (run_dir / "result.json").write_text(result.to_json())
                        
                    except Exception as e:
                        print(f"ERROR: {e}")
                        results.append({
                            "family": family,
                            "size": actual_n,
                            "seed": actual_seed,
                            "mode": solver_mode,
                            "status": "ERROR",
                            "error": str(e),
                        })
    
    return results


def compute_summary(results: List[Dict[str, Any]]) -> Dict[str, Any]:
    """Compute summary statistics from results."""
    
    summary = {
        "timestamp": datetime.now().isoformat(),
        "total_runs": len(results),
        "families": {},
    }
    
    # Group by family
    by_family: Dict[str, List[Dict]] = {}
    for r in results:
        family = r.get("family", "unknown")
        if family not in by_family:
            by_family[family] = []
        by_family[family].append(r)
    
    for family, family_results in by_family.items():
        blind_results = [r for r in family_results if r.get("mode") == "blind"]
        sighted_results = [r for r in family_results if r.get("mode") == "sighted"]
        
        def safe_avg(lst: List, key: str) -> float:
            vals = [r.get(key, 0) for r in lst if key in r]
            return sum(vals) / len(vals) if vals else 0.0
        
        summary["families"][family] = {
            "blind": {
                "count": len(blind_results),
                "avg_time": safe_avg(blind_results, "wall_time_s"),
                "avg_decisions": safe_avg(blind_results, "decisions"),
                "avg_mu": safe_avg(blind_results, "mu_total"),
            },
            "sighted": {
                "count": len(sighted_results),
                "avg_time": safe_avg(sighted_results, "wall_time_s"),
                "avg_decisions": safe_avg(sighted_results, "decisions"),
                "avg_mu": safe_avg(sighted_results, "mu_total"),
            },
        }
        
        # Compute speedup
        blind_mu = summary["families"][family]["blind"]["avg_mu"]
        sighted_mu = summary["families"][family]["sighted"]["avg_mu"]
        if blind_mu > 0 and sighted_mu > 0:
            summary["families"][family]["speedup_mu"] = blind_mu / sighted_mu
        else:
            summary["families"][family]["speedup_mu"] = None
    
    return summary


def save_results(
    results: List[Dict[str, Any]],
    summary: Dict[str, Any],
    output_dir: Path,
) -> None:
    """Save results to files."""
    
    output_dir.mkdir(parents=True, exist_ok=True)
    
    # Save CSV
    csv_path = output_dir / "results.csv"
    if results:
        fieldnames = sorted(set().union(*(r.keys() for r in results)))
        with open(csv_path, 'w', newline='') as f:
            writer = csv.DictWriter(f, fieldnames=fieldnames)
            writer.writeheader()
            writer.writerows(results)
        print(f"\nResults saved to: {csv_path}")
    
    # Save summary JSON
    summary_path = output_dir / "summary.json"
    summary_path.write_text(json.dumps(summary, indent=2))
    print(f"Summary saved to: {summary_path}")
    
    # Save all results as JSON
    all_json_path = output_dir / "all_results.json"
    all_json_path.write_text(json.dumps(results, indent=2))
    print(f"All results saved to: {all_json_path}")


def print_summary(summary: Dict[str, Any]) -> None:
    """Print summary to console."""
    
    print("\n" + "=" * 70)
    print("BENCHMARK SUMMARY")
    print("=" * 70)
    print(f"Timestamp: {summary['timestamp']}")
    print(f"Total runs: {summary['total_runs']}")
    
    for family, stats in summary.get("families", {}).items():
        print(f"\n{family.upper()}")
        print("-" * 40)
        
        blind = stats.get("blind", {})
        sighted = stats.get("sighted", {})
        
        print(f"  Blind:   {blind.get('count', 0)} runs, "
              f"avg_time={blind.get('avg_time', 0):.4f}s, "
              f"avg_μ={blind.get('avg_mu', 0):.1f}")
        print(f"  Sighted: {sighted.get('count', 0)} runs, "
              f"avg_time={sighted.get('avg_time', 0):.4f}s, "
              f"avg_μ={sighted.get('avg_mu', 0):.1f}")
        
        speedup = stats.get("speedup_mu")
        if speedup:
            print(f"  Speedup (μ-cost): {speedup:.2f}x")
    
    print("\n" + "=" * 70)


def main():
    parser = argparse.ArgumentParser(
        description="Run blind vs sighted Thiele Machine benchmarks",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python tools/run_benchmarks.py --family=tseitin --min-n=5 --max-n=15
  python tools/run_benchmarks.py --family=all --mode=both --repetitions=3
  python tools/run_benchmarks.py --family=planted_sat --mode=sighted --max-n=50
        """,
    )
    
    parser.add_argument(
        "--family",
        choices=list(PROBLEM_FAMILIES.keys()) + ["all"],
        default="tseitin",
        help="Problem family to benchmark (default: tseitin)",
    )
    parser.add_argument(
        "--mode",
        choices=["blind", "sighted", "both"],
        default="both",
        help="Solver mode (default: both)",
    )
    parser.add_argument(
        "--min-n",
        type=int,
        default=5,
        help="Minimum problem size (default: 5)",
    )
    parser.add_argument(
        "--max-n",
        type=int,
        default=15,
        help="Maximum problem size (default: 15)",
    )
    parser.add_argument(
        "--step-n",
        type=int,
        default=2,
        help="Step size for problem sizes (default: 2)",
    )
    parser.add_argument(
        "--repetitions",
        type=int,
        default=1,
        help="Number of repetitions per size (default: 1)",
    )
    parser.add_argument(
        "--timeout",
        type=float,
        default=60.0,
        help="Timeout per solve in seconds (default: 60)",
    )
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path("artifacts/benchmarks"),
        help="Output directory (default: artifacts/benchmarks)",
    )
    parser.add_argument(
        "--list-families",
        action="store_true",
        help="List available problem families and exit",
    )
    
    args = parser.parse_args()
    
    if args.list_families:
        print("Available problem families:")
        for info in list_families():
            print(f"  {info['name']}: {info['description']}")
        return
    
    # Determine families to run
    if args.family == "all":
        families = list(PROBLEM_FAMILIES.keys())
    else:
        families = [args.family]
    
    print("=" * 70)
    print("THIELE MACHINE BENCHMARK SUITE")
    print("Blind vs Sighted Separation Study")
    print("=" * 70)
    print()
    
    # Run benchmarks
    start_time = time.time()
    results = run_benchmark_suite(
        families=families,
        min_n=args.min_n,
        max_n=args.max_n,
        step_n=args.step_n,
        mode=args.mode,
        repetitions=args.repetitions,
        timeout_s=args.timeout,
        output_dir=args.output_dir,
    )
    elapsed = time.time() - start_time
    
    print(f"\nTotal benchmark time: {elapsed:.2f}s")
    
    # Compute and save summary
    summary = compute_summary(results)
    save_results(results, summary, args.output_dir)
    print_summary(summary)
    
    print("\n✓ Benchmarks complete!")
    print(f"Results available in: {args.output_dir}")


if __name__ == "__main__":
    main()
