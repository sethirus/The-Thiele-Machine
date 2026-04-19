"""Hardware-in-the-loop logic bridge checks using Verilator backend."""

from __future__ import annotations

import pytest

from thielecpu.hardware.cosim import run_verilog


@pytest.mark.hardware
@pytest.mark.z3
@pytest.mark.strict_rtl
def test_lassert_bridge_prevents_stall_and_reaches_halt() -> None:
    """LASSERT SAT path via on-chip FSM reaches HALT.

    Registers 28/29 point to the binary formula and dual witness blocks.
    Formula is (x1), model sets x1=true, countermodel sets x1=false.
    """
    program = "\n".join([
        "INIT_MEM 16 2",    # two literal words: +x1, end-of-clause
        "INIT_MEM 17 1",    # num_vars
        "INIT_MEM 18 1",    # num_clauses
        "INIT_MEM 19 1",    # literal +x1
        "INIT_MEM 20 0",    # end-of-clause
        "INIT_MEM 97 1",    # model at cbase+1: x1=true
        "INIT_MEM 98 0",    # countermodel at cbase+nvars+1: x1=false
        "LOAD_IMM 28 16 0",
        "LOAD_IMM 29 96 0",
        "LASSERT 28 29 1 2 1",
        "ADD 0 0 0 0",
        "HALT 0",
    ])
    try:
        state = run_verilog(program, backend="verilator", logic_z3_bridge=True)
    except RuntimeError as exc:
        pytest.skip(f"verilator unavailable: {exc}")

    if state is None:
        pytest.skip("verilator backend unavailable")

    assert state is not None
    assert state.get("status", 0) == 2  # HALTED
    assert state.get("err", 0) == 0
    assert state.get("cycles", 0) < 10000
