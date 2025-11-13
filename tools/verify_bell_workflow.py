#!/usr/bin/env python3
"""Reproduce the Bell workflow checks used in the comprehensive audit."""

from __future__ import annotations

import argparse
import json
import random
from fractions import Fraction
from pathlib import Path

try:  # Allow execution via ``python tools/verify_bell_workflow.py``
    from tools.compute_chsh_from_table import (
        check_no_signalling,
        compute_chsh,
        load_table,
        verify_distribution,
    )
    from tools.scan_thiele_box_polytope import (
        scan_polytope,
        write_samples,
    )
    from tools.search_nearby_boxes import (
        explore_neighbourhood,
        summarise_results,
    )
except ModuleNotFoundError:  # pragma: no cover - runtime convenience
    import sys

    REPO_ROOT = Path(__file__).resolve().parent.parent
    sys.path.insert(0, str(REPO_ROOT))
    from tools.compute_chsh_from_table import (
        check_no_signalling,
        compute_chsh,
        load_table,
        verify_distribution,
    )
    from tools.scan_thiele_box_polytope import (
        scan_polytope,
        write_samples,
    )
    from tools.search_nearby_boxes import (
        explore_neighbourhood,
        summarise_results,
    )


DEFAULT_SUPRA_TABLE = Path("artifacts/bell/supra_quantum_16_5.csv")
DEFAULT_POLYTOPE_OUTPUT = Path("artifacts/bell/polytope_scan.csv")
DEFAULT_NEARBY_OUTPUT = Path("artifacts/bell/nearby_scan.json")


def _pr_box_table() -> dict:
    table = {}
    for x in (0, 1):
        for y in (0, 1):
            if x == 0 and y == 0:
                table[(x, y)] = {
                    (0, 1): Fraction(1, 2),
                    (1, 0): Fraction(1, 2),
                }
            else:
                table[(x, y)] = {
                    (0, 0): Fraction(1, 2),
                    (1, 1): Fraction(1, 2),
                }
    return table


def _classical_box_from_polytope(supra_table: dict) -> dict:
    classical_table, _ = scan_polytope(supra_table, resolution=1)
    return classical_table


def _assert_close(actual: Fraction, expected: Fraction, *, tol: float = 1e-9) -> None:
    if abs(float(actual) - float(expected)) > tol:
        raise AssertionError(
            f"Expected CHSH {expected} but observed {actual} (Δ={abs(float(actual)-float(expected))})"
        )


def run_bell_checks(
    *,
    supra_table_path: Path,
    polytope_output: Path,
    nearby_output: Path,
    polytope_resolution: int,
    perturbation_epsilon: float,
    perturbation_attempts: int,
    perturbation_limit: int,
) -> None:
    supra_table = load_table(supra_table_path)
    verify_distribution(supra_table)
    check_no_signalling(supra_table)

    supra_value = compute_chsh(supra_table)
    _assert_close(supra_value, Fraction(16, 5))

    classical_table = _classical_box_from_polytope(supra_table)
    verify_distribution(classical_table)
    check_no_signalling(classical_table)
    classical_value = compute_chsh(classical_table)
    if classical_value > Fraction(2, 1):
        raise AssertionError(f"Classical CHSH should be ≤ 2, observed {classical_value}")

    pr_table = _pr_box_table()
    pr_value = compute_chsh(pr_table)
    _assert_close(pr_value, Fraction(4, 1))

    _, samples = scan_polytope(supra_table, polytope_resolution)
    write_samples(polytope_output, samples)

    rng = random.Random(0xBEE1)
    neighbourhood = explore_neighbourhood(
        supra_table, perturbation_epsilon, perturbation_attempts, perturbation_limit, rng
    )
    summary = summarise_results(neighbourhood)
    nearby_output.parent.mkdir(parents=True, exist_ok=True)
    nearby_output.write_text(json.dumps(summary, indent=2, sort_keys=True))

    accepted = summary.get("accepted", 0)
    if accepted:
        chsh_min = summary.get("chsh_min")
        chsh_max = summary.get("chsh_max")
        if chsh_min is None or chsh_max is None:
            raise AssertionError("Perturbation summary missing CHSH bounds.")
        if chsh_min > float(Fraction(16, 5)) + 1e-6:
            raise AssertionError("Minimum CHSH in neighbourhood exceeded supra-quantum baseline.")
        if chsh_max < float(Fraction(16, 5)) - 1e-6:
            raise AssertionError("Maximum CHSH in neighbourhood failed to reach supra-quantum baseline.")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--supra-table",
        type=Path,
        default=DEFAULT_SUPRA_TABLE,
        help="Path to the supra-quantum correlation table.",
    )
    parser.add_argument(
        "--polytope-output",
        type=Path,
        default=DEFAULT_POLYTOPE_OUTPUT,
        help="Where to store the polytope scan CSV.",
    )
    parser.add_argument(
        "--polytope-resolution",
        type=int,
        default=12,
        help="Resolution for the polytope grid search.",
    )
    parser.add_argument(
        "--nearby-output",
        type=Path,
        default=DEFAULT_NEARBY_OUTPUT,
        help="Where to write the neighbourhood exploration summary.",
    )
    parser.add_argument(
        "--perturbation-epsilon",
        type=float,
        default=0.05,
        help="Magnitude of probability perturbations when scanning the neighbourhood.",
    )
    parser.add_argument(
        "--perturbation-attempts",
        type=int,
        default=300,
        help="Maximum number of perturbation attempts considered.",
    )
    parser.add_argument(
        "--perturbation-limit",
        type=int,
        default=60,
        help="Number of accepted perturbations to record.",
    )
    args = parser.parse_args()

    run_bell_checks(
        supra_table_path=args.supra_table,
        polytope_output=args.polytope_output,
        nearby_output=args.nearby_output,
        polytope_resolution=args.polytope_resolution,
        perturbation_epsilon=args.perturbation_epsilon,
        perturbation_attempts=args.perturbation_attempts,
        perturbation_limit=args.perturbation_limit,
    )

    print(
        "Bell workflow reproduced: classical ≤ 2, Thiele supra-quantum = 16/5, PR box = 4."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
