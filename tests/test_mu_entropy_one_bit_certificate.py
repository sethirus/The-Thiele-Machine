"""Executable gate for the μ/entropy 1-bit tight certificate.

This is the Python-side falsifiable analogue of the Coq specialization:
DeliverableMuEntropyOneBit.mu_cost_ge_one_bit.

We choose the *tight* case (empty query string) so description_bits=0.
"""

from __future__ import annotations

from thielecpu.mu import calculate_mu_cost_breakdown, shannon_entropy_component


def test_entropy_component_two_to_one_is_one_bit() -> None:
    assert shannon_entropy_component(2, 1) == 1.0


def test_mu_breakdown_is_tight_for_empty_query() -> None:
    breakdown = calculate_mu_cost_breakdown("", 2, 1)
    assert breakdown.description_bits == 0.0
    assert breakdown.entropy_bits == 1.0
    assert breakdown.total == 1.0


def test_mu_total_always_bounds_entropy_component() -> None:
    # Non-empty query adds description bits, but the lower bound still holds.
    breakdown = calculate_mu_cost_breakdown("(query x)", 2, 1)
    assert breakdown.total >= breakdown.entropy_bits
