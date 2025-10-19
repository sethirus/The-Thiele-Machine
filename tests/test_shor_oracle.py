"""Unit tests for the Project Sovereign Shor oracle."""

from __future__ import annotations

import pytest

from thielecpu.shor_oracle import find_period_with_claims


def test_find_period_with_claims_basic():
    result = find_period_with_claims(21, 2, max_period=42)
    assert result.period == 6
    assert result.mu_cost > 0.0
    assert result.solver_queries >= 6
    assert result.claims, "Expected at least one recorded claim"
    summary = result.reasoning_summary
    assert summary["period"] == 6
    assert summary["claims"]
    assert summary["residue_trace"][0]["residue"] == 1


@pytest.mark.parametrize("n,a", [(15, 3), (21, 21), (1, 2)])
def test_find_period_rejects_invalid_inputs(n: int, a: int):
    with pytest.raises(ValueError):
        find_period_with_claims(n, a)
