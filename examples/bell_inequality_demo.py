# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

"""Bell inequality utilities mirroring the constructive Coq development.

This module recreates the key CHSH witnesses from
``coq/thielemachine/coqproofs/BellInequality.v`` using rational arithmetic.
It provides:

* Explicit enumeration of the 16 deterministic classical strategies and
  confirmation that all obey the |S| <= 2 local bound.
* A PR-box implementation that attains the algebraic maximum |S| = 4.
* A rational Tsirelson box matching the ``TsirelsonApprox`` witness from the
  Coq proofs with ``S = 4 * gamma`` for ``gamma = 7071/10000``.

Running the module as a script prints the CHSH value for each witness together
with their absolute-value comparisons to the classical bound.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from typing import Callable, Dict, Iterable, Tuple

Bit = int

B0: Bit = 0
B1: Bit = 1


def sgn(bit: Bit) -> int:
    """Return the ±1 sign used in the CHSH correlator."""

    return -1 if bit == B0 else 1


def sum_bit(values: Callable[[Bit], Fraction]) -> Fraction:
    return values(B0) + values(B1)


def sum_bit2(values: Callable[[Bit, Bit], Fraction]) -> Fraction:
    return sum(values(a, b) for a in (B0, B1) for b in (B0, B1))


ProbFn = Callable[[Bit, Bit, Bit, Bit], Fraction]


def correlator(box: ProbFn, x: Bit, y: Bit) -> Fraction:
    """Compute the CHSH correlator E(x, y)."""

    return sum_bit2(
        lambda a, b: Fraction(sgn(a) * sgn(b)) * box(a, b, x, y)
    )


def chsh(box: ProbFn) -> Fraction:
    """Return the CHSH combination S for the given probability box."""

    return (
        correlator(box, B1, B1)
        + correlator(box, B1, B0)
        + correlator(box, B0, B1)
        - correlator(box, B0, B0)
    )


# ---------------------------------------------------------------------------
# Classical deterministic strategies
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Response:
    out0: Bit
    out1: Bit

    def __call__(self, setting: Bit) -> Bit:
        return self.out0 if setting == B0 else self.out1


Strategy = Tuple[Response, Response]


def all_responses() -> Iterable[Response]:
    for out0, out1 in product((B0, B1), repeat=2):
        yield Response(out0, out1)


def all_strategies() -> Iterable[Strategy]:
    for resp_a, resp_b in product(all_responses(), repeat=2):
        yield resp_a, resp_b


def strategy_chsh(strategy: Strategy) -> Fraction:
    alice, bob = strategy

    def deterministic_box(a: Bit, b: Bit, x: Bit, y: Bit) -> Fraction:
        return Fraction(int(alice(x) == a and bob(y) == b))

    return chsh(deterministic_box)


def classical_chsh_extrema() -> Dict[Strategy, Fraction]:
    return {strategy: strategy_chsh(strategy) for strategy in all_strategies()}


# ---------------------------------------------------------------------------
# PR-box (algebraic violation)
# ---------------------------------------------------------------------------


def pr_box(a: Bit, b: Bit, x: Bit, y: Bit) -> Fraction:
    if x == B0 and y == B0:
        # Anti-correlated when both settings are 0.
        return Fraction(1, 2) if (a == B1 and b == B0) or (a == B0 and b == B1) else Fraction(0)
    # Correlated for all other settings.
    return Fraction(1, 2) if a == b else Fraction(0)


# ---------------------------------------------------------------------------
# Tsirelson rational approximation (matches the Coq witness)
# ---------------------------------------------------------------------------


TSIRELSON_GAMMA = Fraction(7071, 10000)


def tsirelson_correlator(x: Bit, y: Bit) -> Fraction:
    return -TSIRELSON_GAMMA if (x, y) == (B0, B0) else TSIRELSON_GAMMA


def tsirelson_box(a: Bit, b: Bit, x: Bit, y: Bit) -> Fraction:
    return Fraction(1, 4) + Fraction(1, 4) * Fraction(sgn(a) * sgn(b)) * tsirelson_correlator(x, y)


# ---------------------------------------------------------------------------
# Script entry point
# ---------------------------------------------------------------------------


def format_fraction(value: Fraction) -> str:
    return f"{value} (~{float(value):.6f})"


def main() -> None:
    strategies = classical_chsh_extrema()
    extrema = {strategy: abs(val) for strategy, val in strategies.items()}
    max_strategy = max(extrema, key=extrema.get)
    max_value = extrema[max_strategy]

    print("Classical deterministic strategies:")
    print(f"  Maximum |S| = {format_fraction(max_value)}")

    pr_value = chsh(pr_box)
    print("\nPR-box:")
    print(f"  S = {format_fraction(pr_value)}")

    tsirelson_value = chsh(tsirelson_box)
    print("\nTsirelson approximation:")
    print(f"  S = {format_fraction(tsirelson_value)}")

    print("\nInequality summary:")
    print(f"  Classical bound satisfied? {max_value <= 2}")
    print(f"  PR-box violates bound? {abs(pr_value) > 2}")
    print(f"  Tsirelson approximation violates bound? {abs(tsirelson_value) > 2}")


if __name__ == "__main__":
    main()
