from __future__ import annotations

import pytest

from thielecpu.hardware.cosim import run_verilog

ERR_BIANCHI = 0x0B1A4C81


@pytest.mark.hardware
@pytest.mark.strict_rtl
def test_bianchi_alarm_fires_on_uninitialised_tensor() -> None:
    """BIANCHI alarm fires when a CHSH tensor is set but locality walls are violated.

    The on-chip LASSERT model removes the external logic_stall / logic_req_valid
    coprocessor signals.  This test verifies the BIANCHI error-code path still
    fires correctly under the new on-chip FSM architecture.
    """
    program = "\n".join(
        [
            "INIT_MU 0",
            "INIT_TENSOR 0 1",
            "LOAD_IMM 0 1 0",
            "HALT 0",
            "",
        ]
    )

    result = run_verilog(program, backend="verilator")
    if result is None:
        pytest.skip("verilator unavailable")

    assert result.get("error_code", 0) == ERR_BIANCHI
    # bianchi_alarm flag should be set in the JSON snapshot
    assert result.get("bianchi_alarm", 0) == 1
