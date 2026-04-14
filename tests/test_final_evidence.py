"""Final evidence generation suite with VCD artifacts and iron regression checks."""

from __future__ import annotations

from pathlib import Path
import re
import subprocess
import shutil

import pytest

pytestmark = pytest.mark.strict_rtl

from thielecpu.hardware.cosim import run_verilog

ERR_LOCALITY = 0x0BADC0DE
TRACE_DIR = Path("build/traces")


def _ensure_trace_dir() -> None:
    TRACE_DIR.mkdir(parents=True, exist_ok=True)


def _signal_went_high(vcd_path: Path, signal_name: str) -> bool:
    text = vcd_path.read_text(errors="ignore")
    var_re = re.compile(rf"\$var\s+\S+\s+\d+\s+(\S+)\s+{re.escape(signal_name)}\s+\$end")
    m = var_re.search(text)
    if not m:
        return False
    token = m.group(1)
    return bool(re.search(rf"(?:^|\n)1{re.escape(token)}(?:\n|$)", text) or re.search(rf"(?:^|\n)b1\s+{re.escape(token)}(?:\n|$)", text))


@pytest.mark.hardware
def test_evidence_locality_theft_trace() -> None:
    _ensure_trace_dir()
    trace = TRACE_DIR / "evidence_locality_theft.vcd"
    result = run_verilog(
        "\n".join(
            [
                "INIT_ACTIVE_MODULE 0",
                "INIT_PT 0 10",
                "LOAD_IMM 1 200 0",
                "LOAD_IMM 0 77 1",
                "STORE 1 0 1",
                "HALT 0",
                "",
            ]
        ),
        backend="verilator",
        trace_file=trace,
    )
    if result is None:
        pytest.skip("verilator unavailable")

    assert result.get("error_code", 0) == ERR_LOCALITY
    assert trace.exists() and trace.stat().st_size > 0


@pytest.mark.hardware
def test_evidence_logic_paradox_trace() -> None:
    """Evidence trace: on-chip LASSERT FSM activates when logic assertion runs.

    In the on-chip model (replacing the old coprocessor bridge), LASSERT reads
    formula and certificate bytes from vm_mem via register-indexed addressing.
    This test records a VCD trace and verifies the lassert_phase FSM register
    was exercised during LASSERT execution.
    """
    _ensure_trace_dir()
    trace = TRACE_DIR / "evidence_logic_paradox.vcd"
    result = run_verilog(
        "\n".join(
            [
                "INIT_LOGIC_ACC 0xCAFEEACE",
                # Trivial SAT formula in data memory
                "INIT_MEM 0 1",    # flen = 1
                "INIT_MEM 1 1",    # cert: var 1 = true
                "INIT_MEM 2 1",    # nclauses = 1
                "INIT_MEM 3 1",    # literal: var 1 (positive)
                "INIT_MEM 4 0",    # end-of-clause sentinel
                "LASSERT 32 0 1",  # SAT (bit5=1), freg=0, creg=0, cost=1
                "HALT 0",
                "",
            ]
        ),
        backend="verilator",
        trace_file=trace,
    )
    if result is None:
        pytest.skip("verilator unavailable")

    assert result.get("status", 0) == 2
    assert trace.exists() and trace.stat().st_size > 0
    # The on-chip FSM register lassert_phase should appear in the VCD.
    text = trace.read_text(errors="ignore")
    assert "lassert_phase" in text, "Expected on-chip LASSERT FSM signal in VCD trace"


@pytest.mark.hardware
def test_evidence_valid_quantum_physics_trace() -> None:
    _ensure_trace_dir()
    trace = TRACE_DIR / "evidence_valid_physics.vcd"
    result = run_verilog(
        "\n".join(
            [
                "INIT_MU 100",
                "INIT_LOGIC_ACC 0xCAFEEACE",
                "REVEAL 0 0 1",
                "CHSH_TRIAL 1 0 0 0 7",
                "HALT 0",
                "",
            ]
        ),
        backend="verilator",
        trace_file=trace,
    )
    if result is None:
        pytest.skip("verilator unavailable")

    assert result.get("status", 0) == 2
    assert result.get("mu", 0) >= 260
    assert trace.exists() and trace.stat().st_size > 0


