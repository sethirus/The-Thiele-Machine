from __future__ import annotations

import pytest

from thielecpu.hardware.cosim import run_verilog

ERR_BIANCHI = 0x0B1A4C81


@pytest.mark.hardware
def test_bianchi_clears_logic_stall_and_logic_req_valid() -> None:
    program = "\n".join(
        [
            "INIT_MU 0",
            "INIT_TENSOR 0 1",
            "INIT_LOGIC_STALL 1",
            "INIT_LOGIC_REQ_VALID 1",
            "LOAD_IMM 0 1 0",
            "HALT 0",
            "",
        ]
    )

    result = run_verilog(program, backend="verilator")
    if result is None:
        pytest.skip("verilator unavailable")

    assert result.get("error_code", 0) == ERR_BIANCHI
    assert result.get("logic_stall", 1) == 0
    assert result.get("logic_req_valid", 1) == 0
