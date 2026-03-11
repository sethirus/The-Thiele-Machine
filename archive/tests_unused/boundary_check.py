from __future__ import annotations

from thielecpu.hardware.cosim import run_verilog

ERR_PARTITION = 0xBADF001D


def test_root_overwrite_guard_17th_partition_rejected_and_pt0_unchanged() -> None:
    program = ["INIT_MU 0"]
    program.extend(["PNEW 1 0 1" for _ in range(17)])
    program.append("HALT 0")
    program.append("")

    result = run_verilog("\n".join(program), backend="verilator")
    assert result is not None

    assert result.get("error_code", 0) == ERR_PARTITION
    assert result.get("err", 0) == 1
    assert result.get("pt0_size", 0) == 0
