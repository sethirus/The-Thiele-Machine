#!/usr/bin/env python3
"""Operational Bell/CHSH helpers.

This module intentionally avoids "serialization μ" and instead focuses on
measuring CHSH from *executed* strategies in the Python VM, using rational
arithmetic (Fractions) for reproducibility.

The VM strategy is provided as a Python code string to be executed via PYEXEC.
That code writes a JSON file containing balanced setting counts.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Dict, Iterable, Mapping, Tuple

from tools.compute_chsh_from_table import compute_chsh

Setting = Tuple[int, int]
Outcome = Tuple[int, int]
CountKey = Tuple[int, int, int, int]


@dataclass(frozen=True)
class DatasetCounts:
    n_per_setting: int
    counts: Mapping[CountKey, int]


def strategy_code(strategy: str, *, n_per_setting: int, seed: int, output_json: Path) -> str:
    """Return PYEXEC code that writes per-setting outcome counts to `output_json`.

    The output JSON shape is:
      {"n_per_setting": int, "counts": {"x,y,a,b": int, ...}}

    Strategies:
    - "lhv": deterministic local (a=b=0)
    - "tsirelson": Tsirelson-style correlators (best representable at given n_per_setting)
    - "supra_16_5": supra-quantum witness distribution (CHSH=16/5)
    - "pr": PR-like box under repo CHSH convention (CHSH=4)

        Notes:
        - The repo CHSH convention used by tools.compute_chsh_from_table is
            S = E(1,1)+E(1,0)+E(0,1)-E(0,0).
    - For the PR-like box under that convention, we use anti-correlation at (0,0)
      and correlation elsewhere.
    """

    out_path = str(output_json)
    if strategy not in {"lhv", "tsirelson", "supra_16_5", "pr"}:
        raise ValueError(f"unknown strategy: {strategy}")

    # Keep the embedded code self-contained: no repo imports.
    # Balanced trials: iterate settings and deterministically allocate exactly
    # n_per_setting trials according to rational weights (no Monte Carlo noise).
    # Write counts in a stable, parseable string key format "x,y,a,b".

    # For Tsirelson-like strategies, enforce correlators per-setting as tightly
    # as the integer sample size permits. With n trials per setting, the
    # correlator E(x,y) must be of the form (2*k-n)/n.
    e_target = 2**0.5 / 2
    k_best = int(round(((1.0 + e_target) / 2.0) * float(n_per_setting)))
    k_best = max(0, min(int(n_per_setting), k_best))
    e_best = Fraction(2 * k_best - int(n_per_setting), int(n_per_setting))
    return f'''
import json
from fractions import Fraction

strategy = {strategy!r}
seed = int({seed})
n_per_setting = int({n_per_setting})

# Supra-quantum 16/5 distribution used in demos/demo_chsh_game.py
SUPRA_PROBS = {{
    # (x, y, a, b): (numerator, denominator)
    (0, 0, 0, 0): (1, 5),
    (0, 0, 1, 1): (1, 5),
    (0, 0, 0, 1): (3, 10),
    (0, 0, 1, 0): (3, 10),

    (0, 1, 0, 0): (1, 2),
    (0, 1, 1, 1): (1, 2),
    (0, 1, 0, 1): (0, 1),
    (0, 1, 1, 0): (0, 1),

    (1, 0, 0, 0): (1, 2),
    (1, 0, 1, 1): (1, 2),
    (1, 0, 0, 1): (0, 1),
    (1, 0, 1, 0): (0, 1),

    (1, 1, 0, 0): (1, 2),
    (1, 1, 1, 1): (1, 2),
    (1, 1, 0, 1): (0, 1),
    (1, 1, 1, 0): (0, 1),
}}


def _allocate_counts(outcome_weights, n):
    """Allocate integer counts summing to n from Fraction weights."""
    floors = {{}}
    remainders = []
    allocated = 0
    for outcome, w in outcome_weights.items():
        target = w * n
        base = int(target)  # floor
        floors[outcome] = base
        allocated += base
        remainders.append((target - base, outcome))
    left = n - allocated
    remainders.sort(key=lambda t: (t[0], t[1]), reverse=True)
    for i in range(left):
        floors[remainders[i][1]] += 1
    return floors


def _weights_for_setting(x, y):
    if strategy == "lhv":
        return {{(0, 0): Fraction(1, 1), (0, 1): Fraction(0, 1), (1, 0): Fraction(0, 1), (1, 1): Fraction(0, 1)}}

    if strategy == "supra_16_5":
        weights = {{}}
        for a in (0, 1):
            for b in (0, 1):
                num, denom = SUPRA_PROBS.get((x, y, a, b), (0, 1))
                weights[(a, b)] = Fraction(int(num), int(denom))
        return weights

    if strategy == "tsirelson":
        # Repo CHSH convention witness:
        #   S = E(1,1)+E(1,0)+E(0,1)-E(0,0)
        # Use E(0,0)=-e and others +e.
        e = Fraction({e_best.numerator}, {e_best.denominator})
        expectation = -e if (x == 0 and y == 0) else e

        # Choose integer counts of "same" vs "different" outcomes to enforce
        # the correlator exactly at this n.
        n = n_per_setting
        n_same = {k_best} if expectation >= 0 else (n - {k_best})
        n_diff = n - n_same

        same0 = n_same // 2
        same1 = n_same - same0
        diff0 = n_diff // 2
        diff1 = n_diff - diff0
        return {{
            (0, 0): Fraction(same0, n),
            (1, 1): Fraction(same1, n),
            (0, 1): Fraction(diff0, n),
            (1, 0): Fraction(diff1, n),
        }}

    if strategy == "pr":
        # PR-like box for the repo's CHSH convention:
        # anti-correlated at (0,0), correlated elsewhere.
        if x == 0 and y == 0:
            return {{(0, 1): Fraction(1, 2), (1, 0): Fraction(1, 2), (0, 0): Fraction(0, 1), (1, 1): Fraction(0, 1)}}
        return {{(0, 0): Fraction(1, 2), (1, 1): Fraction(1, 2), (0, 1): Fraction(0, 1), (1, 0): Fraction(0, 1)}}

    raise RuntimeError("unknown strategy")


counts = {{}}
for x in (0, 1):
    for y in (0, 1):
        weights = _weights_for_setting(x, y)
        allocated = _allocate_counts(weights, n_per_setting)
        for (a, b), c in allocated.items():
            if c:
                key = f"{{x}},{{y}},{{a}},{{b}}"
                counts[key] = int(counts.get(key, 0)) + int(c)

payload = {{
    "n_per_setting": n_per_setting,
    "seed": seed,
    "strategy": strategy,
    "counts": counts,
}}

with open({out_path!r}, "w", encoding="utf-8") as f:
    json.dump(payload, f, sort_keys=True)
'''


def load_counts(path: Path) -> DatasetCounts:
    import json

    payload = json.loads(path.read_text(encoding="utf-8"))
    raw_counts: Mapping[str, int] = payload.get("counts", {})
    counts: Dict[CountKey, int] = {}
    for key, value in raw_counts.items():
        x, y, a, b = (int(part) for part in key.split(","))
        counts[(x, y, a, b)] = int(value)
    return DatasetCounts(n_per_setting=int(payload["n_per_setting"]), counts=counts)


def table_from_counts(dataset: DatasetCounts) -> Dict[Setting, Dict[Outcome, Fraction]]:
    table: Dict[Setting, Dict[Outcome, Fraction]] = {}
    for x in (0, 1):
        for y in (0, 1):
            setting = (x, y)
            total = 0
            per_outcome: Dict[Outcome, int] = {(0, 0): 0, (0, 1): 0, (1, 0): 0, (1, 1): 0}
            for a in (0, 1):
                for b in (0, 1):
                    c = int(dataset.counts.get((x, y, a, b), 0))
                    per_outcome[(a, b)] += c
                    total += c
            if total <= 0:
                raise ValueError(f"empty counts for setting {setting}")
            table[setting] = {out: Fraction(c, total) for out, c in per_outcome.items()}
    return table


def chsh_from_counts(dataset: DatasetCounts) -> Fraction:
    return compute_chsh(table_from_counts(dataset))
