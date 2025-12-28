"""Shared utilities implementing μ-spec v2.0.

This module intentionally separates two concepts that get conflated in prose:

- **Description length**: how many bits it costs to *state the question*.
- **Shannon information gain** (uniform hypothesis model): how many bits of
    uncertainty are eliminated when a hypothesis set of size ``before`` is
    reduced to size ``after``.

The total μ-cost used by many pipelines is the sum of these two components.
"""

from __future__ import annotations

import math
from dataclasses import dataclass
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


def shannon_entropy_component(before_hypotheses: int, after_hypotheses: int) -> float:
    """Return the pure Shannon information gain component in bits.

    Interpretation: under the uniform hypothesis-set model, the Shannon entropy
    of a hypothesis set of size ``n`` is $H = \log_2(n)$ (in bits). Therefore
    reducing a set from ``before`` to ``after`` costs

    $\Delta H = \log_2(\tfrac{\text{before}}{\text{after}})$.

    This is exactly the ``information_gain_bits`` component.

    Preconditions:
    - ``before_hypotheses`` and ``after_hypotheses`` are positive integers.
    - ``after_hypotheses <= before_hypotheses``.
    """

    return information_gain_bits(before_hypotheses, after_hypotheses)


def calculate_mu_cost(expr: str, before: int, after: int) -> float:
    """Return the total μ-cost for the reasoning triple ``(expr, before, after)``.

    Backward-compatible API: returns a single float ``description_bits + entropy_bits``.
    Prefer :func:`calculate_mu_cost_breakdown` when you need the split.
    """

    return calculate_mu_cost_breakdown(expr, before, after).total


@dataclass(frozen=True)
class MuCost:
    """Structured μ-cost split into description vs entropy components."""

    canonical: str
    description_bits: float
    entropy_bits: float

    @property
    def total(self) -> float:
        return self.description_bits + self.entropy_bits


def calculate_mu_cost_breakdown(expr: str, before: int, after: int) -> MuCost:
    """Return a structured μ-cost split.

    - ``description_bits`` is the UTF-8 byte length of the canonicalized query × 8.
    - ``entropy_bits`` is the Shannon information gain under the uniform hypothesis model.
    """

    canonical = canonical_s_expression(expr)
    description_bits = float(question_cost_bits(expr))
    entropy_bits = shannon_entropy_component(before, after)
    return MuCost(
        canonical=canonical,
        description_bits=description_bits,
        entropy_bits=entropy_bits,
    )


@dataclass(frozen=True)
class MuBreakdown:
    """Structured breakdown of a μ-cost computation."""

    canonical: str
    question_bits: float
    information_gain: float

    @property
    def total(self) -> float:
        return self.question_bits + self.information_gain


def mu_breakdown(expr: str, before: int, after: int) -> MuBreakdown:
    """Convenience helper returning the canonical breakdown structure."""

    canonical = canonical_s_expression(expr)
    question_bits = float(question_cost_bits(expr))
    info_bits = information_gain_bits(before, after)
    return MuBreakdown(canonical=canonical, question_bits=question_bits, information_gain=info_bits)


# =============================================================================
# Quantitative No Free Insight Theorem (StateSpaceCounting.v)
# =============================================================================

def axiom_bitlength(formula: str) -> int:
    """Compute axiom bit-length matching Coq StateSpaceCounting.v.
    
    Definition: String.length(formula) * 8 bits
    
    This is the description length component of μ-cost, representing
    the minimum information required to specify the constraint.
    """
    return len(formula.encode('utf-8')) * 8


def log2_nat(n: int) -> int:
    """Ceiling of log₂(n) matching Coq StateSpaceCounting.v.
    
    Definition: log2_nat(n) = if n =? 2^(log2 n) then log2 n else log2 n + 1
    
    This computes the ceiling of log₂, used in information-theoretic bounds.
    Special case: log2_nat(0) = 0 by convention.
    """
    if n <= 0:
        return 0
    
    log_n = n.bit_length() - 1  # Floor of log2(n)
    
    # Check if n is exactly a power of 2
    if (1 << log_n) == n:
        return log_n
    else:
        return log_n + 1


def quantitative_nofreeinsight_bound(k: int) -> int:
    """Information-theoretic bound: k bits → log₂(2^k) = k reduction.
    
    Theorem (nofreeinsight_information_theoretic_bound):
        k ≥ log2_nat(2^k) for all k > 0
    
    This establishes that k constraint bits provide at least k bits
    of state space reduction under optimal encoding.
    """
    if k <= 0:
        return 0
    return log2_nat(2 ** k)


__all__ = [
    "MuBreakdown",
    "MuCost",
    "axiom_bitlength",
    "calculate_mu_cost",
    "calculate_mu_cost_breakdown",
    "canonical_s_expression",
    "information_gain_bits",
    "log2_nat",
    "mu_breakdown",
    "quantitative_nofreeinsight_bound",
    "question_cost_bits",
    "shannon_entropy_component",
]
