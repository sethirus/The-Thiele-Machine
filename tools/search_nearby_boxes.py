"""Probe a neighbourhood of the supra-quantum table for CHSH variation."""

from __future__ import annotations

import argparse
import json
import random
from fractions import Fraction
from pathlib import Path
from typing import Dict, Iterable, List, Tuple

try:
    from tools.compute_chsh_from_table import (
        check_no_signalling,
        compute_chsh,
        load_table,
        verify_distribution,
    )
except ModuleNotFoundError:  # pragma: no cover - standalone execution
    import sys

    REPO_ROOT = Path(__file__).resolve().parent.parent
    sys.path.insert(0, str(REPO_ROOT))
    from tools.compute_chsh_from_table import (
        check_no_signalling,
        compute_chsh,
        load_table,
        verify_distribution,
    )

Bit = int
Setting = Tuple[Bit, Bit]
Outcome = Tuple[Bit, Bit]
Table = Dict[Setting, Dict[Outcome, Fraction]]


def _perturb_distribution(
    distribution: Dict[Outcome, Fraction], epsilon: float, rng: random.Random
) -> Dict[Outcome, Fraction]:
    weights: List[float] = []
    outcomes: List[Outcome] = []
    for outcome, value in distribution.items():
        perturbation = rng.uniform(-epsilon, epsilon)
        adjusted = max(float(value) + perturbation, 0.0)
        weights.append(adjusted)
        outcomes.append(outcome)

    total = sum(weights)
    if total <= 0:
        return distribution

    normalised = [weight / total for weight in weights]
    return {
        outcome: Fraction(probability).limit_denominator(10**6)
        for outcome, probability in zip(outcomes, normalised)
    }


def _perturb_table(
    table: Table, epsilon: float, rng: random.Random
) -> Table:
    return {
        setting: _perturb_distribution(dist, epsilon, rng)
        for setting, dist in table.items()
    }


def explore_neighbourhood(
    table: Table,
    epsilon: float,
    attempts: int,
    limit: int,
    rng: random.Random,
) -> List[Tuple[float, Table]]:
    """Return accepted perturbations and their CHSH values."""

    results: List[Tuple[float, Table]] = []
    for _ in range(attempts):
        candidate = _perturb_table(table, epsilon, rng)
        try:
            verify_distribution(candidate)
            check_no_signalling(candidate)
        except ValueError:
            continue
        value = float(compute_chsh(candidate))
        results.append((value, candidate))
        if len(results) >= limit:
            break
    return results


def summarise_results(results: List[Tuple[float, Table]]) -> Dict[str, object]:
    if not results:
        return {"accepted": 0}
    values = [value for value, _ in results]
    max_value, max_table = max(results, key=lambda item: item[0])
    min_value, min_table = min(results, key=lambda item: item[0])
    return {
        "accepted": len(results),
        "chsh_min": min_value,
        "chsh_max": max_value,
        "max_table": _serialise_table(max_table),
        "min_table": _serialise_table(min_table),
        "samples": values,
    }


def _serialise_table(table: Table) -> Dict[str, Dict[str, float]]:
    return {
        f"{setting[0]}{setting[1]}": {f"{outcome[0]}{outcome[1]}": float(prob)
        for outcome, prob in dist.items()}
        for setting, dist in table.items()
    }


def main(argv: Iterable[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--table",
        type=Path,
        default=Path("artifacts/bell/supra_quantum_16_5.csv"),
        help="Baseline supra-quantum correlation table.",
    )
    parser.add_argument(
        "--epsilon",
        type=float,
        default=0.05,
        help="Magnitude of random perturbations applied to each probability.",
    )
    parser.add_argument(
        "--attempts",
        type=int,
        default=200,
        help="Maximum number of perturbation attempts to consider.",
    )
    parser.add_argument(
        "--limit",
        type=int,
        default=60,
        help="Number of accepted samples to record.",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("artifacts/bell/nearby_scan.json"),
        help="Where to store the JSON summary.",
    )
    args = parser.parse_args(list(argv) if argv is not None else None)

    table = load_table(args.table)
    verify_distribution(table)
    check_no_signalling(table)

    rng = random.Random(0xBEE1)
    results = explore_neighbourhood(table, args.epsilon, args.attempts, args.limit, rng)
    summary = {
        "epsilon": args.epsilon,
        "attempts": args.attempts,
        "limit": args.limit,
        **summarise_results(results),
    }

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(summary, indent=2, sort_keys=True))

    if summary.get("accepted", 0) == 0:
        print("No perturbations satisfied the constraints.")
    else:
        print(
            "Accepted {accepted} perturbations; CHSH spans [{chsh_min:.6f}, {chsh_max:.6f}].".format(
                accepted=summary["accepted"],
                chsh_min=summary["chsh_min"],
                chsh_max=summary["chsh_max"],
            )
        )


if __name__ == "__main__":
    main()
