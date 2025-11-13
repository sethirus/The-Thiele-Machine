"""Explore mixtures of classical, supra-quantum, and PR boxes."""

from __future__ import annotations

import argparse
import csv
from fractions import Fraction
from itertools import product
from pathlib import Path
from typing import Dict, Iterable, Tuple

try:  # Support running as a standalone script
    from tools.compute_chsh_from_table import (
        check_no_signalling,
        compute_chsh,
        load_table,
        verify_distribution,
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

Bit = int
Setting = Tuple[Bit, Bit]
Outcome = Tuple[Bit, Bit]
Table = Dict[Setting, Dict[Outcome, Fraction]]


def _deterministic_table(a0: Bit, a1: Bit, b0: Bit, b1: Bit) -> Table:
    table: Table = {}
    for x, y in product((0, 1), repeat=2):
        expected_a = a0 if x == 0 else a1
        expected_b = b0 if y == 0 else b1
        dist: Dict[Outcome, Fraction] = {}
        for a, b in product((0, 1), repeat=2):
            dist[(a, b)] = Fraction(int(a == expected_a and b == expected_b))
        table[(x, y)] = dist
    return table


def _pr_box() -> Table:
    table: Table = {}
    for x, y in product((0, 1), repeat=2):
        dist: Dict[Outcome, Fraction] = {}
        for a, b in product((0, 1), repeat=2):
            if x == 0 and y == 0:
                correlated = (a == 1 and b == 0) or (a == 0 and b == 1)
            else:
                correlated = a == b
            dist[(a, b)] = Fraction(1, 2) if correlated else Fraction(0)
        table[(x, y)] = dist
    return table


def _mix_tables(weights: Tuple[Fraction, Fraction, Fraction], tables: Tuple[Table, Table, Table]) -> Table:
    mixed: Table = {}
    for setting in product((0, 1), repeat=2):
        dist: Dict[Outcome, Fraction] = {}
        for outcome in product((0, 1), repeat=2):
            dist[outcome] = sum(
                weight * tables[idx][tuple(setting)][tuple(outcome)]
                for idx, weight in enumerate(weights)
            )
        mixed[tuple(setting)] = dist
    return mixed


def _best_classical_table() -> Table:
    best_value = Fraction(-999)
    best_table: Table | None = None
    for a0, a1, b0, b1 in product((0, 1), repeat=4):
        table = _deterministic_table(a0, a1, b0, b1)
        verify_distribution(table)
        value = abs(compute_chsh(table))
        if value > best_value:
            best_value = value
            best_table = table
    assert best_table is not None
    return best_table


def _weight_grid(resolution: int) -> Iterable[Tuple[Fraction, Fraction, Fraction]]:
    for classical_steps in range(resolution + 1):
        for supra_steps in range(resolution + 1 - classical_steps):
            pr_steps = resolution - classical_steps - supra_steps
            yield (
                Fraction(classical_steps, resolution),
                Fraction(supra_steps, resolution),
                Fraction(pr_steps, resolution),
            )


def scan_polytope(
    supra_table: Table, resolution: int
) -> Tuple[Table, Iterable[Tuple[Fraction, Fraction, Fraction, Fraction]]]:
    classical_table = _best_classical_table()
    pr_table = _pr_box()
    samples = []
    for weights in _weight_grid(resolution):
        mixed = _mix_tables(weights, (classical_table, supra_table, pr_table))
        verify_distribution(mixed)
        check_no_signalling(mixed)
        s_value = compute_chsh(mixed)
        samples.append((*weights, s_value))
    return classical_table, samples


def write_samples(path: Path, samples: Iterable[Tuple[Fraction, Fraction, Fraction, Fraction]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.writer(handle)
        writer.writerow(["w_classical", "w_supra", "w_pr", "chsh"])
        for classical, supra, pr_weight, chsh_val in samples:
            writer.writerow([
                float(classical),
                float(supra),
                float(pr_weight),
                float(chsh_val),
            ])


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--supra-table",
        type=Path,
        default=Path("artifacts/bell/supra_quantum_16_5.csv"),
        help="Path to the supra-quantum correlation table.",
    )
    parser.add_argument(
        "--resolution",
        type=int,
        default=20,
        help="Grid granularity for mixture weights (higher is denser).",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("artifacts/bell/polytope_scan.csv"),
        help="Where to save the CSV of sampled CHSH values.",
    )
    args = parser.parse_args()

    supra_table = load_table(args.supra_table)
    verify_distribution(supra_table)
    check_no_signalling(supra_table)

    classical_table, samples = scan_polytope(supra_table, args.resolution)
    classical_value = compute_chsh(classical_table)
    supra_value = compute_chsh(supra_table)

    write_samples(args.output, samples)

    print("Classical CHSH:", float(classical_value))
    print("Supra-quantum CHSH:", float(supra_value))
    print(f"Saved {len(samples)} samples to {args.output}")


if __name__ == "__main__":
    main()
