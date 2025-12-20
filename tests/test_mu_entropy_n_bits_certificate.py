"""Executable gate for μ/entropy N-bit table certificates."""

from __future__ import annotations

from thielecpu.mu import calculate_mu_cost_breakdown


def test_mu_entropy_table_small_range_is_tight() -> None:
    expr = ""
    for n in range(1, 11):
        before = 1 << n
        after = 1
        bd = calculate_mu_cost_breakdown(expr, before, after)
        assert bd.description_bits == 0.0
        assert bd.entropy_bits == float(n)
        assert bd.total == float(n)


def test_mu_total_bounds_entropy_for_nonempty_query() -> None:
    bd = calculate_mu_cost_breakdown("(query x)", 8, 1)
    assert bd.total >= bd.entropy_bits
