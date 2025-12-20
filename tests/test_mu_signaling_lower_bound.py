"""Falsifiable tight μ lower-bound demo checks.

This test suite asserts two things:
1) Non-targeting traces cannot change a victim module’s observable region.
2) A single PMERGE(victim, hidden) can transmit one-bit world differences into
   the victim observable region with mu_execution = 4.

If either assertion fails, the partition semantics / μ-ledger model has diverged.
"""

from __future__ import annotations

from thielecpu._types import ModuleId
from thielecpu.state import State


def _obs(state: State, mid: ModuleId) -> frozenset[int]:
    return frozenset(state.regions[mid])


def _build(hidden_region: set[int]) -> tuple[State, ModuleId, ModuleId]:
    s = State()
    victim = s.pnew({0, 1})
    hidden = s.pnew(hidden_region)
    return s, victim, hidden


def test_non_targeting_trace_cannot_signal() -> None:
    s0, victim0, hidden0 = _build({2, 3, 4, 5})

    before = _obs(s0, victim0)

    # Trace targets only hidden-side module(s)
    left, right = s0.psplit(hidden0, lambda i: i % 2 == 0)
    s0.pmerge(left, right)

    after = _obs(s0, victim0)
    assert before == after


def test_one_merge_signals_and_is_mu_tight() -> None:
    w0, victim0, hidden0 = _build({2})
    w1, victim1, hidden1 = _build({3})

    assert victim0 == victim1 == ModuleId(1)

    mu0_before = w0.mu_ledger.mu_execution
    mu1_before = w1.mu_ledger.mu_execution

    # One PMERGE targets victim; output depends on hidden world.
    out0 = w0.pmerge(victim0, hidden0)
    out1 = w1.pmerge(victim1, hidden1)

    obs0 = _obs(w0, out0)
    obs1 = _obs(w1, out1)

    assert obs0 != obs1

    mu0_after = w0.mu_ledger.mu_execution
    mu1_after = w1.mu_ledger.mu_execution
    assert int(mu0_after - mu0_before) == 4
    assert int(mu1_after - mu1_before) == 4
