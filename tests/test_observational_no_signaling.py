"""Falsifiable no-signaling check on the concrete partition state.

This is the executable analogue of KernelPhysics.observational_no_signaling:
operations that do not target a module id must not change that module’s
observable region.

We also use a two-run "hidden bit" experiment: we vary only *other* modules and
confirm the victim module’s observable region cannot carry that information.
"""

from __future__ import annotations

from copy import deepcopy

from thielecpu._types import ModuleId
from thielecpu.state import State


def _observable_region(state: State, mid: ModuleId) -> frozenset[int]:
    return frozenset(state.regions[mid])


def _run_non_targeting_trace(state: State, *, hidden_mid: ModuleId) -> None:
    """Run a short trace that avoids touching module 1 (the victim)."""

    # Axiom updates and structural ops on the hidden module only.
    state.add_axiom(hidden_mid, "hidden: axiom 0")
    left, right = state.psplit(hidden_mid, lambda i: i % 2 == 0)
    state.add_axiom(left, "hidden: axiom 1")

    # Merge back (still not touching victim).
    state.pmerge(left, right)


def test_observational_no_signaling_region_unchanged_for_untargeted_module() -> None:
    state = State()

    victim = state.pnew({0, 1})
    hidden = state.pnew({2, 3, 4, 5})

    before = _observable_region(state, victim)
    _run_non_targeting_trace(state, hidden_mid=hidden)
    after = _observable_region(state, victim)

    assert before == after


def test_no_signaling_hidden_bit_cannot_be_observed_via_other_modules() -> None:
    # Construct two states with the same victim module id, but different hidden regions.
    base_a = State()
    victim_a = base_a.pnew({0, 1})
    hidden_a = base_a.pnew({2, 3, 4, 5})

    base_b = State()
    victim_b = base_b.pnew({0, 1})
    hidden_b = base_b.pnew({10, 11, 12, 13})

    assert victim_a == victim_b == ModuleId(1)
    assert hidden_a == hidden_b == ModuleId(2)

    obs0_a = _observable_region(base_a, victim_a)
    obs0_b = _observable_region(base_b, victim_b)
    assert obs0_a == obs0_b

    # Run the same non-targeting trace in both states.
    _run_non_targeting_trace(base_a, hidden_mid=hidden_a)
    _run_non_targeting_trace(base_b, hidden_mid=hidden_b)

    obs1_a = _observable_region(base_a, victim_a)
    obs1_b = _observable_region(base_b, victim_b)

    # If the victim observable region could change based on hidden structure,
    # this would be a signaling channel. The machine forbids it.
    assert obs1_a == obs1_b == obs0_a
