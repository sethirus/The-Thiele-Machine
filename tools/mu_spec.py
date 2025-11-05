"""μ-spec helper copied into tools to isolate validator TCB.

This module provides the canonical S-expression encoding and the
calculate_mu_cost function. It mirrors the implementation in
`thielecpu/mu.py` but is intentionally self-contained so that
validators and receipt tools do not import runtime VM code.
"""

from __future__ import annotations

import math
from typing import Tuple


def _tokenise(expr: str) -> Tuple[str, ...]:
    tokens = []
    current = []
    for ch in expr:
        if ch in "()":
            if current:
                tokens.append("".join(current))
                current = []
            tokens.append(ch)
        elif ch.isspace():
            if current:
                tokens.append("".join(current))
                current = []
        else:
            current.append(ch)
    if current:
        tokens.append("".join(current))
    return tuple(tokens)


def canonical_s_expression(expr: str) -> str:
    """Return the canonical S-expression string for ``expr``."""

    tokens = _tokenise(expr)
    return " ".join(tokens)


def question_cost_bits(expr: str) -> int:
    """Compute the description-length cost for ``expr``."""

    canonical = canonical_s_expression(expr)
    return len(canonical.encode("utf-8")) * 8


def information_gain_bits(before: int, after: int) -> float:
    """Return the Shannon information gain in bits for the transition ``before``→``after``."""

    if before <= 0:
        raise ValueError("`before` must be a positive integer")
    if after <= 0:
        raise ValueError("`after` must be a positive integer")
    if after > before:
        raise ValueError("`after` cannot exceed `before`")
    if after == before:
        return 0.0
    return math.log2(before / after)


def calculate_mu_cost(expr: str, before: int, after: int) -> float:
    """Return the total μ-cost for the reasoning triple ``(expr, before, after)``."""

    question_bits = question_cost_bits(expr)
    info_bits = information_gain_bits(before, after)
    return question_bits + info_bits


# Optional convenience wrapper matching the runtime module
def mu_breakdown(expr: str, before: int, after: int):
    canonical = canonical_s_expression(expr)
    question_bits = float(question_cost_bits(expr))
    info_bits = information_gain_bits(before, after)
    return {"canonical": canonical, "question_bits": question_bits, "information_gain": info_bits}
