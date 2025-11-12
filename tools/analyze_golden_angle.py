#!/usr/bin/env python3
"""Analyse μ-costs of divergence angles under the NUSD functional."""

from __future__ import annotations

import argparse
import math
import random
from dataclasses import dataclass
from typing import Iterable, List, Sequence, Tuple


@dataclass
class AngleResult:
    label: str
    seeds: int
    mu_question: float
    mu_answer: float
    mu_total: float


def fractional_part(value: float) -> float:
    value -= math.floor(value)
    if value >= 1.0:
        value -= 1.0
    return value


def continued_fraction_digits(theta: float, max_depth: int = 64) -> List[int]:
    """Return the continued-fraction digits for a real θ in (0, 1)."""

    if not 0.0 < theta < 1.0:
        raise ValueError("θ must lie in (0, 1)")
    digits: List[int] = []
    value = theta
    for _ in range(max_depth):
        a0 = math.floor(value)
        digits.append(int(a0))
        frac = value - a0
        if frac < 1e-15:
            break
        value = 1.0 / frac
    return digits


def convergents_from_digits(digits: Sequence[int]) -> Tuple[List[int], List[int]]:
    """Compute the convergent numerators and denominators for the digits."""

    numerators: List[int] = []
    denominators: List[int] = []
    p_prev, p_curr = 0, 1
    q_prev, q_curr = 1, 0
    for a in digits:
        p_next = a * p_curr + p_prev
        q_next = a * q_curr + q_prev
        numerators.append(p_next)
        denominators.append(q_next)
        p_prev, p_curr = p_curr, p_next
        q_prev, q_curr = q_curr, q_next
    return numerators, denominators


def mu_question(theta: float, seeds: int) -> float:
    """Compute the μ-question cost using continued-fraction coefficients."""

    digits = continued_fraction_digits(theta)
    if digits and digits[0] == 0:
        digits = digits[1:]
    depth = max(1, int(math.ceil(math.log2(seeds))))
    usable_digits = digits[:depth]
    if not usable_digits:
        usable_digits = digits
    return sum(math.log2(1.0 + float(a)) for a in usable_digits)


def mu_answer(theta: float, seeds: int) -> float:
    phases = [fractional_part(k * theta) for k in range(seeds)]
    phases.sort()
    for left, right in zip(phases, phases[1:]):
        if abs(left - right) < 1e-12:
            return math.inf
    gaps: List[float] = []
    for idx, current in enumerate(phases):
        nxt = phases[0] + 1.0 if idx + 1 == len(phases) else phases[idx + 1]
        gap = nxt - current
        gaps.append(gap)
    discrepancy = sum((gap - 1.0 / seeds) ** 2 for gap in gaps)
    return math.log2(1.0 + seeds * discrepancy)


def evaluate_angle(label: str, theta: float, seeds: int) -> AngleResult:
    question = mu_question(theta, seeds)
    answer = mu_answer(theta, seeds)
    total = question + answer
    return AngleResult(label=label, seeds=seeds, mu_question=question, mu_answer=answer, mu_total=total)


def random_angles(count: int) -> Iterable[Tuple[str, float]]:
    rng = random.Random(2025)
    for idx in range(count):
        value = rng.random()
        if value == 0.0 or value == 1.0:
            continue
        yield (f"rand_{idx}", value)


def analyse(angles: Sequence[Tuple[str, float]], seeds: Sequence[int]) -> List[AngleResult]:
    results: List[AngleResult] = []
    for label, theta in angles:
        for count in seeds:
            results.append(evaluate_angle(label, theta, count))
    return results


def parse_args(argv: Iterable[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-seeds", type=int, default=256, help="largest seed count to test (default: 256)")
    parser.add_argument("--include-random", type=int, default=0, help="number of random irrationals to sample")
    return parser.parse_args(argv)


def main(argv: Iterable[str] | None = None) -> None:
    args = parse_args(argv)
    seeds = [args.max_seeds // 4, args.max_seeds // 2, args.max_seeds]
    canonical_angles: List[Tuple[str, float]] = [
        ("golden", (math.sqrt(5.0) - 1.0) / 2.0),
        ("sqrt2_mod_1", math.sqrt(2.0) % 1.0),
        ("pi_mod_1", math.pi % 1.0),
    ]
    extra = list(random_angles(args.include_random))
    results = analyse(canonical_angles + extra, seeds)
    header = f"{'angle':<16}{'seeds':>8}{'μ_question':>14}{'μ_answer':>12}{'μ_total':>12}"
    print(header)
    print("-" * len(header))
    for result in results:
        print(
            f"{result.label:<16}{result.seeds:>8d}{result.mu_question:>14.3f}{result.mu_answer:>12.3f}{result.mu_total:>12.3f}"
        )
    best = min(
        (res for res in results if res.seeds == seeds[-1] and math.isfinite(res.mu_total)),
        key=lambda res: res.mu_total,
    )
    print("\nMinimum μ_total at N = {} achieved by {} ({:.6f} bits).".format(seeds[-1], best.label, best.mu_total))


if __name__ == "__main__":
    main()
