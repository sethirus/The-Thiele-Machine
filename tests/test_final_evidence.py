"""Final evidence generation suite with VCD artifacts and iron regression checks."""

from __future__ import annotations

from pathlib import Path
import re
import subprocess

import pytest

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
                "LOAD_IMM 0 77 1",
                "STORE 255 0 1",
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
    _ensure_trace_dir()
    trace = TRACE_DIR / "evidence_logic_paradox.vcd"
    result = run_verilog(
        "\n".join(
            [
                "LASSERT 0 1 0",
                "HALT 0",
                "",
            ]
        ),
        backend="verilator",
        logic_z3_bridge=True,
        force_logic_error=True,
        trace_file=trace,
    )
    if result is None:
        pytest.skip("verilator unavailable")

    assert result.get("status", 0) == 2
    assert trace.exists() and trace.stat().st_size > 0
    assert _signal_went_high(trace, "logic_stall")


@pytest.mark.hardware
def test_evidence_valid_quantum_physics_trace() -> None:
    _ensure_trace_dir()
    trace = TRACE_DIR / "evidence_valid_physics.vcd"
    result = run_verilog(
        "\n".join(
            [
                "INIT_MU 100",
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


def test_iron_regression_minimum_dff_count() -> None:
    cmd = (
        "yosys -p \"read_verilog -sv -DSYNTHESIS thielecpu/hardware/rtl/thiele_cpu_kami.v; "
        "hierarchy -top mkModule1; proc; flatten; stat\""
    )
    result = subprocess.run(cmd, shell=True, text=True, capture_output=True, check=True)
    m = re.search(r"\$dff\s+(\d+)", result.stdout)
    assert m is not None, "Yosys stat output missing $dff line"
    assert int(m.group(1)) >= 300, f"$dff dropped below iron floor: {m.group(1)}"
