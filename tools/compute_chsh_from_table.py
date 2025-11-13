#!/usr/bin/env python3
"""Compute CHSH value and basic consistency checks from a correlation table.

The CSV is expected to provide one row per (x, y, a, b) combination with
probabilities encoded either as rational strings (e.g. ``3/10``) or decimals.
"""
from __future__ import annotations

import argparse
import csv
from collections import defaultdict
from fractions import Fraction
from pathlib import Path
from typing import Dict, Tuple

Bit = int
Setting = Tuple[Bit, Bit]
Outcome = Tuple[Bit, Bit]


def parse_probability(raw: str) -> Fraction:
    """Return a rational probability from ``raw``."""

    raw = raw.strip()
    if not raw:
        raise ValueError("Missing probability entry")
    if "/" in raw:
        numerator, denominator = raw.split("/", 1)
        return Fraction(int(numerator), int(denominator))
    return Fraction(raw)


def load_table(path: Path) -> Dict[Setting, Dict[Outcome, Fraction]]:
    """Load the correlation table from ``path`` and normalise the mapping."""

    table: Dict[Setting, Dict[Outcome, Fraction]] = defaultdict(dict)
    with path.open(newline="", encoding="utf-8") as handle:
        reader = csv.DictReader(handle)
        expected = {"x", "y", "a", "b", "probability"}
        if set(reader.fieldnames or []) != expected:
            raise ValueError(
                f"Unexpected columns {reader.fieldnames}; expected {sorted(expected)}"
            )
        for row in reader:
            setting = (int(row["x"]), int(row["y"]))
            outcome = (int(row["a"]), int(row["b"]))
            probability = parse_probability(row["probability"])
            table[setting][outcome] = probability

    return table


def verify_distribution(table: Dict[Setting, Dict[Outcome, Fraction]]) -> None:
    """Sanity check that each conditional distribution sums to one."""

    for (x, y), dist in table.items():
        total = sum(dist.values())
        if total != 1:
            raise ValueError(f"Distribution for x={x}, y={y} sums to {total}, not 1")
        for (a, b), prob in dist.items():
            if prob < 0:
                raise ValueError(
                    f"Negative probability {prob} at (x={x}, y={y}, a={a}, b={b})"
                )


def check_no_signalling(table: Dict[Setting, Dict[Outcome, Fraction]]) -> None:
    """Raise ``ValueError`` if Alice or Bob marginals depend on the remote setting."""

    # Alice marginals P(a|x,y)
    for x in (0, 1):
        reference = None
        for y in (0, 1):
            marginal = [
                sum(prob for (a_val, _), prob in table[(x, y)].items() if a_val == a)
                for a in (0, 1)
            ]
            reference = reference or marginal
            if marginal != reference:
                raise ValueError(
                    f"Alice marginal for x={x} differs between y settings: {reference} vs {marginal}"
                )
    # Bob marginals P(b|x,y)
    for y in (0, 1):
        reference = None
        for x in (0, 1):
            marginal = [
                sum(prob for (_, b_val), prob in table[(x, y)].items() if b_val == b)
                for b in (0, 1)
            ]
            reference = reference or marginal
            if marginal != reference:
                raise ValueError(
                    f"Bob marginal for y={y} differs between x settings: {reference} vs {marginal}"
                )


def correlator(table: Dict[Setting, Dict[Outcome, Fraction]], x: Bit, y: Bit) -> Fraction:
    """Return E(x, y) for the supplied distribution."""

    def sgn(bit: Bit) -> int:
        return -1 if bit == 0 else 1

    return sum(
        Fraction(sgn(a) * sgn(b)) * prob
        for (a, b), prob in table[(x, y)].items()
    )


def compute_chsh(table: Dict[Setting, Dict[Outcome, Fraction]]) -> Fraction:
    """Compute S = E(1,1) + E(1,0) + E(0,1) - E(0,0)."""

    return (
        correlator(table, 1, 1)
        + correlator(table, 1, 0)
        + correlator(table, 0, 1)
        - correlator(table, 0, 0)
    )


def main() -> int:
    parser = argparse.ArgumentParser(description="Compute CHSH from a correlation table")
    parser.add_argument("table", type=Path, help="Path to CSV correlation table")
    args = parser.parse_args()

    table = load_table(args.table)
    verify_distribution(table)
    check_no_signalling(table)
    s_value = compute_chsh(table)
    print(f"CHSH S = {s_value} ≈ {float(s_value):.6f}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
