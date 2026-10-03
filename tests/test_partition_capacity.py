"""PNEW, PSPLIT and PMERGE trap when the partition would leave its bounds.

A module's range lies inside the 128-word data memory, and module numbers
stay below 64, the slot count of the hardware partition table. PNEW of a
range that runs past memory traps; PNEW and PMERGE trap when no module
number is free, PSPLIT when fewer than two are free. A trapped step sets
err and leaves the partition graph as it was.

Module numbers start at 1, so 63 PNEWs fill the table.
"""

from __future__ import annotations

import pytest

from build.thiele_vm import run_vm

pytestmark = pytest.mark.strict_extracted


def _fill(count: int) -> list[str]:
    """PNEW the single addresses 0 .. count-1: modules 1 .. count."""
    return [f"PNEW {{{i}}} 1" for i in range(count)]


def _module_ids(state) -> list[int]:
    return sorted(mid for mid, _ in state.graph.pg_modules)


def test_pnew_ending_at_the_last_address_succeeds():
    state = run_vm(["PNEW {126,127} 1", "HALT 0"])
    assert not state.err
    assert _module_ids(state) == [1]


def test_pnew_past_memory_traps():
    state = run_vm(["PNEW {127,128} 1", "HALT 0"])
    assert state.err
    assert state.graph.pg_modules == []
    assert state.graph.pg_next_id == 1


def test_sixty_three_modules_fit():
    state = run_vm(_fill(63) + ["HALT 0"], fuel=200)
    assert not state.err
    assert _module_ids(state) == list(range(1, 64))
    assert state.graph.pg_next_id == 64


def test_pnew_on_a_full_table_traps():
    state = run_vm(_fill(63) + ["PNEW {63} 1", "HALT 0"], fuel=200)
    assert state.err
    assert _module_ids(state) == list(range(1, 64))
    assert state.graph.pg_next_id == 64


def test_pmerge_on_a_full_table_traps():
    state = run_vm(_fill(63) + ["PMERGE 1 2 1", "HALT 0"], fuel=200)
    assert state.err
    assert _module_ids(state) == list(range(1, 64))
    assert state.graph.pg_next_id == 64


def test_psplit_with_one_free_number_traps():
    state = run_vm(_fill(62) + ["PSPLIT 1 {0} {} 1", "HALT 0"], fuel=200)
    assert state.err
    assert _module_ids(state) == list(range(1, 63))
    assert state.graph.pg_next_id == 63
