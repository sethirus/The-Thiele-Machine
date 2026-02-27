"""Hardware-in-the-loop logic bridge checks using Verilator backend."""

from __future__ import annotations

import pytest

from thielecpu.hardware.cosim import run_verilog


@pytest.mark.hardware
def test_lassert_bridge_prevents_stall_and_reaches_halt() -> None:
    program = "\n".join([
        "LASSERT 9 4 1",
        "ADD 0 0 0",
        "HALT",
    ])
    try:
        state = run_verilog(program, backend="verilator", logic_z3_bridge=True)
    except RuntimeError as exc:
        pytest.skip(f"verilator unavailable: {exc}")

    assert state is not None
    assert state.get("status", 0) == 2  # HALTED
    assert state.get("err", 0) == 0
    assert state.get("cycles", 0) < 10000
