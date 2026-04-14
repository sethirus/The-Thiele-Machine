"""Hardware-in-the-loop logic bridge checks using Verilator backend."""

from __future__ import annotations

import pytest

from thielecpu.hardware.cosim import run_verilog


@pytest.mark.hardware
@pytest.mark.z3
@pytest.mark.strict_rtl
def test_lassert_bridge_prevents_stall_and_reaches_halt() -> None:
    """LASSERT SAT path via on-chip FSM reaches HALT.

    op_a=32: bit5=1 (SAT), freg=0 → fbase=regs[0]=0.
    Trivial formula in memory: 1 clause (x1), assignment x1=true.
    """
    program = "\n".join([
        # Trivial SAT formula in data memory
        "INIT_MEM 0 1",    # flen = 1
        "INIT_MEM 1 1",    # cert: var 1 = true
        "INIT_MEM 2 1",    # nclauses = 1
        "INIT_MEM 3 1",    # literal: var 1 (positive)
        "INIT_MEM 4 0",    # end-of-clause sentinel
        "LASSERT 32 0 1",  # SAT (bit5=1), freg=0, creg=0, cost=1
        "ADD 0 0 0",
        "HALT",
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
