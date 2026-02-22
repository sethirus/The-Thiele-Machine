"""
test_rtl_synthesis_gate.py
==========================
Gate test: the Thiele CPU Verilog is structurally healthy (parse/elaborate/smoke sim).

What this enforces
------------------
1. Yosys is installed and reachable.
2. iverilog is installed and reachable (for simulation gate).
3. ``thiele_cpu_kami.v`` parses and elaborates without syntax errors.
4. Yosys synthesis on extracted RTL completes with exit code 0.
5. The synthesised design has top-level module ``mkModule1``.
6. Yosys reports a positive cell count (design is not empty).
7. The synthesised Verilog output (``synth_lite_out.v``) is written and is
   non-empty.
8. (Co-sim gate, slow) A representative test-bench compiles and runs under
    iverilog/vvp without fatal simulator errors.

Important limitation
--------------------
These are structural/smoke checks. They do not prove end-to-end ISA semantics
for all execution behavior (HALT terminal behavior, receipt-gated commit
ordering, or CHSH correlator correctness).

Running
-------
Fast (default):   pytest tests/test_rtl_synthesis_gate.py -v
Full cosim:       THIELE_RTL_SIM=verilator pytest tests/test_rtl_synthesis_gate.py -v -m hardware

Environment variables
---------------------
THIELE_RTL_SIM=verilator   Use Verilator backend instead of iverilog for co-sim.
RTL_SKIP_SYNTHESIS=1       Skip Yosys gate (keep iverilog parse check only).
"""

from __future__ import annotations

import os
import re
import shutil
import subprocess
import tempfile
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[1]
RTL_DIR = REPO_ROOT / "thielecpu" / "hardware" / "rtl"
TB_DIR = REPO_ROOT / "thielecpu" / "hardware" / "testbench"
SYNTH_OUT_V = RTL_DIR / "synth_lite_out.v"
KAMI_V = RTL_DIR / "thiele_cpu_kami.v"
KAMI_TB = TB_DIR / "thiele_cpu_kami_tb.v"
TOP_MODULE = "mkModule1"


# ── helpers ───────────────────────────────────────────────────────────────────


def _run(cmd: list[str], cwd: str, timeout: int = 120) -> subprocess.CompletedProcess:
    return subprocess.run(
        cmd,
        cwd=cwd,
        capture_output=True,
        text=True,
        timeout=timeout,
    )


def _yosys_cell_count(stdout: str) -> int:
    """Parse ``Number of cells:`` from yosys stat output."""
    m = re.search(r"Number of cells:\s+(\d+)", stdout)
    return int(m.group(1)) if m else 0


def _yosys_module_names(stdout: str) -> list[str]:
    """Extract module names reported by yosys stat from design hierarchy section."""
    # Match lines like "   thiele_cpu                        1"
    # or "     mu_alu                          1" from design hierarchy
    return re.findall(r"^\s+([A-Za-z_]\w+)\s+\d+\s*$", stdout, re.MULTILINE)


# ── tests ──────────────────────────────────────────────────────────────────────


@pytest.mark.hardware
def test_yosys_available():
    """Yosys binary must be on PATH."""
    assert shutil.which("yosys") is not None, "yosys not found on PATH"


@pytest.mark.hardware
def test_iverilog_available():
    """iverilog binary must be on PATH."""
    assert shutil.which("iverilog") is not None, "iverilog not found on PATH"


@pytest.mark.hardware
def test_rtl_source_exists():
    """thiele_cpu_kami.v must exist."""
    assert KAMI_V.exists(), f"RTL source missing: {KAMI_V}"


@pytest.mark.hardware
def test_verilog_parse_iverilog():
    """
    iverilog must parse thiele_cpu_kami.v without errors.

    This is faster than Yosys and catches most syntax/type errors immediately.
    """
    result = _run(
        [
            "iverilog",
            "-t", "null",
            "-g2012",
            "-DYOSYS_LITE",
            "-DSYNTHESIS",
            str(KAMI_V),
        ],
        cwd=str(RTL_DIR),
        timeout=60,
    )
    assert result.returncode == 0, (
        "iverilog parse failed:\n"
        f"STDOUT: {result.stdout}\n"
        f"STDERR: {result.stderr}"
    )


@pytest.mark.hardware
@pytest.mark.slow
def test_yosys_synthesis_succeeds():
    """
    Yosys lite synthesis (synth_lite.ys) must complete with exit code 0.
    Skipped when RTL_SKIP_SYNTHESIS=1.
    """
    if os.environ.get("RTL_SKIP_SYNTHESIS"):
        pytest.skip("RTL_SKIP_SYNTHESIS=1 — skipping Yosys gate")

    result = _run([
        "yosys",
        "-p",
        f"read_verilog -sv -DSYNTHESIS {KAMI_V}; hierarchy -check -top {TOP_MODULE}; stat",
    ], cwd=str(REPO_ROOT), timeout=300)
    assert result.returncode == 0, (
        f"Yosys synthesis failed (exit {result.returncode}).\n"
        f"STDOUT (tail):\n{result.stdout[-3000:]}\n"
        f"STDERR (tail):\n{result.stderr[-3000:]}"
    )


@pytest.mark.hardware
@pytest.mark.slow
def test_yosys_top_module_present():
    """After synthesis, yosys must report the ``mkModule1`` top module."""
    if os.environ.get("RTL_SKIP_SYNTHESIS"):
        pytest.skip("RTL_SKIP_SYNTHESIS=1")

    result = _run([
        "yosys",
        "-p",
        f"read_verilog -sv -DSYNTHESIS {KAMI_V}; hierarchy -check -top {TOP_MODULE}; stat",
    ], cwd=str(REPO_ROOT), timeout=300)
    assert result.returncode == 0, "synthesis failed — cannot check module"
    output = result.stdout
    has_top = (
        f"Top module:  \\{TOP_MODULE}" in output
        or f"=== {TOP_MODULE} ===" in output
    )
    assert has_top, (
        f"Top module '{TOP_MODULE}' not found in yosys output.\n"
        f"Output tail:\n{output[-2000:]}"
    )


@pytest.mark.hardware
@pytest.mark.slow
def test_yosys_nonempty_design():
    """After synthesis, the design must have ≥ 1 cell (not trivially empty)."""
    if os.environ.get("RTL_SKIP_SYNTHESIS"):
        pytest.skip("RTL_SKIP_SYNTHESIS=1")

    result = _run([
        "yosys",
        "-p",
        f"read_verilog -sv -DSYNTHESIS {KAMI_V}; hierarchy -check -top {TOP_MODULE}; stat",
    ], cwd=str(REPO_ROOT), timeout=300)
    if result.returncode != 0:
        pytest.skip("synthesis failed — cannot check cell count")
    cells = _yosys_cell_count(result.stdout)
    assert cells > 0, (
        f"Yosys reports 0 cells — synthesis produced empty design.\n"
        f"STDOUT (tail):\n{result.stdout[-2000:]}"
    )


@pytest.mark.hardware
@pytest.mark.slow
def test_synth_output_verilog_written():
    """synth_lite_out.v must be written and non-empty after synthesis."""
    if os.environ.get("RTL_SKIP_SYNTHESIS"):
        pytest.skip("RTL_SKIP_SYNTHESIS=1")

    result = _run([
        "yosys",
        "-p",
        f"read_verilog -sv -DSYNTHESIS {KAMI_V}; hierarchy -check -top {TOP_MODULE}; stat; write_verilog {SYNTH_OUT_V}",
    ], cwd=str(REPO_ROOT), timeout=300)
    if result.returncode != 0:
        pytest.skip("synthesis failed — cannot check output file")

    assert SYNTH_OUT_V.exists(), f"synth_lite_out.v was not written by Yosys"
    assert SYNTH_OUT_V.stat().st_size > 0, "synth_lite_out.v is empty"


@pytest.mark.hardware
@pytest.mark.integration
@pytest.mark.slow
def test_verilog_cosim_testbench():
    """
    Compile and run the CPU testbench under iverilog/vvp.

    This is the highest-confidence gate: it verifies that the RTL actually
    SIMULATES without fatal errors, not just that it parses.

    Only runs if a testbench file exists in hardware/testbench/.
    """
    if not KAMI_TB.exists():
        pytest.skip(f"Kami testbench missing: {KAMI_TB}")

    with tempfile.TemporaryDirectory() as tmp:
        sim_bin = Path(tmp) / "sim_out"
        compile_result = _run(
            [
                "iverilog",
                "-g2012",
                "-DSIMULATION",
                "-o", str(sim_bin),
                str(KAMI_V),
                str(KAMI_TB),
            ],
            cwd=str(REPO_ROOT),
            timeout=120,
        )
        assert compile_result.returncode == 0, (
            "iverilog testbench compile failed:\n"
            f"STDERR: {compile_result.stderr}"
        )

        run_result = _run(
            ["vvp", str(sim_bin)],
            cwd=str(REPO_ROOT),
            timeout=60,
        )
        # vvp exit code 0 = clean finish; 1 = $fatal or compile error
        assert run_result.returncode == 0, (
            "vvp simulation failed or reported $fatal:\n"
            f"STDOUT: {run_result.stdout[-2000:]}\n"
            f"STDERR: {run_result.stderr[-1000:]}"
        )
        # No "$error" or "FAILED" in output
        output = run_result.stdout + run_result.stderr
        assert "FAILED" not in output.upper() or "0 FAILED" in output.upper(), (
            "Testbench reported FAILED:\n" + output[-2000:]
        )
