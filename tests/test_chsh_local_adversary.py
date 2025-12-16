from __future__ import annotations

from fractions import Fraction
from pathlib import Path

from tools.local_chsh_adversary import enumerate_local_strategies, run_strategy_vm


def test_local_strategies_cannot_exceed_chsh_2(tmp_path: Path) -> None:
    # Exhaustive adversarial search over deterministic local strategies.
    # Each run executes a real VM program, extracts CHSH from receipts via the
    # canonical parser, and enforces the classical bound.
    max_s = None
    min_s = None
    for strat in enumerate_local_strategies():
        s = run_strategy_vm(strategy=strat, outdir=tmp_path / strat.label())
        assert abs(s) <= Fraction(2, 1), f"local strategy {strat.label()} violated bound: {s}"
        max_s = s if max_s is None else max(max_s, s)
        min_s = s if min_s is None else min(min_s, s)

    # Tightness sanity check: deterministic local strategies can saturate ±2.
    assert max_s == Fraction(2, 1)
    assert min_s == Fraction(-2, 1)
