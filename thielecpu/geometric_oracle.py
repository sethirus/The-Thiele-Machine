"""Lightweight reasoning primitives for congruence-based heuristics.

This module deliberately avoids heavy-weight SMT tooling.  It provides a
minimal "geometric oracle" that answers questions about the compatibility of
congruence classes with a target modulus without ever producing concrete
factors.  The demo code consumes this oracle to illustrate how the Thiele
Machine can spend μ-bits to erase impossible regions of the search space using
pure arithmetic structure.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Literal, TypedDict

Status = Literal["possible", "impossible"]


class CongruenceVerdict(TypedDict):
    """Structured response from :func:`check_congruence_possibility`.

    ``status``
        Either ``"possible"`` or ``"impossible"``.

    ``reason``
        A short human-readable explanation of how the verdict was reached.

    ``product_residue``
        The residue of ``a * b`` modulo ``m``.

    ``target_residue``
        The residue of ``N`` modulo ``m``.
    """

    status: Status
    reason: str
    product_residue: int
    target_residue: int


@dataclass(frozen=True)
class CongruenceQuery:
    """Descriptor for a congruence feasibility request."""

    modulus: int
    residue_a: int
    residue_b: int
    base: int


def check_congruence_possibility(
    n: int, residue_a: int, residue_b: int, base: int
) -> CongruenceVerdict:
    """Return whether a congruence pair can describe factors of ``n``.

    The oracle implements the textbook identity:

    .. math:: (p \\bmod m) (q \\bmod m) \\equiv n \\bmod m.

    For supplied residues ``residue_a`` and ``residue_b`` this function computes
    both sides of the identity modulo ``base`` and simply checks equality.  If
    the residues are incompatible the function reports ``"impossible"``; this
    allows the demo to erase entire congruence classes without learning the
    actual factors.
    """

    product_residue = (residue_a * residue_b) % base
    target_residue = n % base

    if product_residue == target_residue:
        return CongruenceVerdict(
            status="possible",
            reason=(
                "Residues multiply to the target modulo base; factors in this"
                " class cannot be ruled out."
            ),
            product_residue=product_residue,
            target_residue=target_residue,
        )

    return CongruenceVerdict(
        status="impossible",
        reason=(
            "Residues are inconsistent with n modulo base; the congruence"
            " class is eliminated."
        ),
        product_residue=product_residue,
        target_residue=target_residue,
    )

