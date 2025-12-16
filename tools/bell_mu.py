"""Helpers for relating Bell/CHSH boxes to μ-cost.

This module is intentionally explicit about what μ-cost means in this repo:
μ-cost is computed by `tools.mu_spec.calculate_mu_cost`, which is purely a
syntactic description-length term plus an optional information-gain term.

The functions here let us *measure* how μ varies across families of no-signaling
boxes under specific encodings, without assuming any quantum postulates.
"""

from __future__ import annotations

import csv
from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from pathlib import Path
from typing import Dict, Iterable, List, Literal, Mapping, Sequence, Tuple

from tools.compute_chsh_from_table import check_no_signalling, compute_chsh, load_table, verify_distribution
from tools.mu_spec import calculate_mu_cost, mu_breakdown

Bit = int
Setting = Tuple[Bit, Bit]
Outcome = Tuple[Bit, Bit]
Table = Dict[Setting, Dict[Outcome, Fraction]]

EncodingKind = Literal["table_sexpr", "mixture_sexpr", "tag_sexpr"]


def _fraction_literal(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def table_to_sexpr(table: Mapping[Setting, Mapping[Outcome, Fraction]]) -> str:
    """Canonical S-expression for a 2×2×2×2 correlation table."""

    settings = sorted(table.keys())
    parts: List[str] = ["(box"]
    for x, y in settings:
        parts.append(f" (xy {x} {y}")
        dist = table[(x, y)]
        for a, b in sorted(dist.keys()):
            parts.append(f"  (ab {a} {b} p {_fraction_literal(dist[(a, b)])})")
        parts.append(")")
    parts.append(")")
    return "".join(parts)


def mixture_to_sexpr(weights: Tuple[Fraction, Fraction, Fraction]) -> str:
    w_classical, w_supra, w_pr = weights
    return (
        "(mixture (classical "
        + _fraction_literal(w_classical)
        + ") (supra "
        + _fraction_literal(w_supra)
        + ") (pr "
        + _fraction_literal(w_pr)
        + "))"
    )


def tag_to_sexpr(tag: str) -> str:
    return f"(box_tag {tag})"


def tsirelson_like_table(gamma: Fraction = Fraction(7071, 10000)) -> Table:
    """Build a no-signaling Tsirelson-like box using a rational correlator.

    Uses the CHSH convention from `tools.compute_chsh_from_table`:
    S = E(1,1) + E(1,0) + E(0,1) - E(0,0)

    Setting the correlators as:
    - E(0,0) = -gamma
    - E(0,1) = +gamma
    - E(1,0) = +gamma
    - E(1,1) = +gamma
    yields S = 4*gamma ≈ 2.828 when gamma ≈ 0.7071.

    Uniform marginals, so this is no-signaling by construction.
    """

    def dist_for_expectation(e: Fraction) -> Dict[Outcome, Fraction]:
        # With uniform marginals, the joint distribution over bits a,b in {0,1}
        # mapped to ±1 has:
        #   P(a=b)   = (1+E)/2
        #   P(a!=b)  = (1-E)/2
        # split equally between the two outcomes in each class.
        p_same = Fraction(1, 2) + e / 2
        p_diff = Fraction(1, 2) - e / 2
        return {
            (0, 0): p_same / 2,
            (1, 1): p_same / 2,
            (0, 1): p_diff / 2,
            (1, 0): p_diff / 2,
        }

    table: Table = {}
    for x, y in product((0, 1), repeat=2):
        expectation = -gamma if (x, y) == (0, 0) else gamma
        table[(x, y)] = dist_for_expectation(expectation)
    verify_distribution(table)
    check_no_signalling(table)
    return table


def pr_box_table() -> Table:
    """PR box in the same convention used by tools.scan_thiele_box_polytope."""

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
    verify_distribution(table)
    check_no_signalling(table)
    return table


def deterministic_table(a0: Bit, a1: Bit, b0: Bit, b1: Bit) -> Table:
    table: Table = {}
    for x, y in product((0, 1), repeat=2):
        expected_a = a0 if x == 0 else a1
        expected_b = b0 if y == 0 else b1
        dist: Dict[Outcome, Fraction] = {}
        for a, b in product((0, 1), repeat=2):
            dist[(a, b)] = Fraction(int(a == expected_a and b == expected_b))
        table[(x, y)] = dist
    verify_distribution(table)
    check_no_signalling(table)
    return table


def best_classical_table() -> Table:
    best_value = Fraction(-999)
    best: Table | None = None
    for a0, a1, b0, b1 in product((0, 1), repeat=4):
        candidate = deterministic_table(a0, a1, b0, b1)
        value = abs(compute_chsh(candidate))
        if value > best_value:
            best_value = value
            best = candidate
    assert best is not None
    return best


def mix_tables(
    weights: Tuple[Fraction, Fraction, Fraction],
    tables: Tuple[Table, Table, Table],
) -> Table:
    w0, w1, w2 = weights
    t0, t1, t2 = tables
    mixed: Table = {}
    for x, y in product((0, 1), repeat=2):
        setting = (x, y)
        dist: Dict[Outcome, Fraction] = {}
        for a, b in product((0, 1), repeat=2):
            outcome = (a, b)
            dist[outcome] = (
                w0 * t0[setting][outcome]
                + w1 * t1[setting][outcome]
                + w2 * t2[setting][outcome]
            )
        mixed[setting] = dist
    verify_distribution(mixed)
    check_no_signalling(mixed)
    return mixed


def weight_grid(resolution: int) -> Iterable[Tuple[Fraction, Fraction, Fraction]]:
    if resolution <= 0:
        raise ValueError("resolution must be positive")
    for classical_steps in range(resolution + 1):
        for supra_steps in range(resolution + 1 - classical_steps):
            pr_steps = resolution - classical_steps - supra_steps
            yield (
                Fraction(classical_steps, resolution),
                Fraction(supra_steps, resolution),
                Fraction(pr_steps, resolution),
            )


@dataclass(frozen=True)
class MuChshSample:
    w_classical: Fraction
    w_supra: Fraction
    w_pr: Fraction
    chsh: Fraction
    mu_total: float
    question_bits: float
    info_bits: float
    encoding: EncodingKind


def sample_mu_vs_chsh(
    supra_table: Table,
    *,
    resolution: int,
    encoding: EncodingKind,
    before: int = 1,
    after: int = 1,
) -> List[MuChshSample]:
    classical = best_classical_table()
    pr_table = pr_box_table()
    tables = (classical, supra_table, pr_table)

    samples: List[MuChshSample] = []
    for weights in weight_grid(resolution):
        mixed = mix_tables(weights, tables)
        s_val = compute_chsh(mixed)

        if encoding == "table_sexpr":
            expr = table_to_sexpr(mixed)
        elif encoding == "mixture_sexpr":
            expr = mixture_to_sexpr(weights)
        elif encoding == "tag_sexpr":
            expr = tag_to_sexpr("mixture(classical,supra,pr)")
        else:
            raise ValueError(f"unknown encoding {encoding}")

        breakdown = mu_breakdown(expr, before, after)
        samples.append(
            MuChshSample(
                w_classical=weights[0],
                w_supra=weights[1],
                w_pr=weights[2],
                chsh=s_val,
                mu_total=breakdown["question_bits"] + breakdown["information_gain"],
                question_bits=breakdown["question_bits"],
                info_bits=breakdown["information_gain"],
                encoding=encoding,
            )
        )
    return samples


def load_supra_table(path: Path) -> Table:
    supra_table = load_table(path)
    verify_distribution(supra_table)
    check_no_signalling(supra_table)
    return supra_table


def write_mu_vs_chsh_csv(path: Path, samples: Sequence[MuChshSample]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.writer(handle)
        writer.writerow(
            [
                "encoding",
                "w_classical",
                "w_supra",
                "w_pr",
                "chsh",
                "mu_total",
                "question_bits",
                "info_bits",
            ]
        )
        for s in samples:
            writer.writerow(
                [
                    s.encoding,
                    float(s.w_classical),
                    float(s.w_supra),
                    float(s.w_pr),
                    float(s.chsh),
                    float(s.mu_total),
                    float(s.question_bits),
                    float(s.info_bits),
                ]
            )


def baseline_boxes(supra_table: Table) -> Mapping[str, Table]:
    return {
        "classical_best": best_classical_table(),
        "tsirelson_like": tsirelson_like_table(),
        "supra_16_5": supra_table,
        "pr_box": pr_box_table(),
    }


def mu_for_box(
    table: Table,
    *,
    encoding: EncodingKind,
    before: int = 1,
    after: int = 1,
    tag: str | None = None,
) -> float:
    if encoding == "table_sexpr":
        expr = table_to_sexpr(table)
    elif encoding == "mixture_sexpr":
        raise ValueError("mixture_sexpr requires mixture weights; use tag_sexpr or table_sexpr")
    elif encoding == "tag_sexpr":
        expr = tag_to_sexpr(tag or "box")
    else:
        raise ValueError(f"unknown encoding {encoding}")
    return float(calculate_mu_cost(expr, before, after))
