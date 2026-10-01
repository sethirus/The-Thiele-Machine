"""A program loaded over the system's serial pin runs as it does on the CPU.

The extracted system (CPU and loader, thiele_system.v) receives each program
as serial frames through rtl_harness/testbench/system_tb.v and reports its
final state over the serial output. The report must equal the CPU's own
result for the same program. scripts/system_sim.py --gates repeats this on a
synthesized gate netlist in CI (Full).
"""
from __future__ import annotations

import importlib.util
import tempfile
from pathlib import Path

import pytest

SCRIPT = Path(__file__).resolve().parents[1] / "scripts" / "system_sim.py"
SPEC = importlib.util.spec_from_file_location("system_sim", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


def test_stream_frames_count_then_little_endian_words():
    stream = MODULE.program_stream("LOAD_IMM 1 5 0\nHALT 0")
    assert stream[:2] == [2, 0]
    assert len(stream) == 2 + 2 * 16
    # The first instruction word, least significant byte first.
    assert stream[2:4] == [0x00, 0x05] and stream[17] == 0x02


@pytest.mark.parametrize("name", sorted(MODULE.PROGRAMS))
def test_serial_load_matches_the_cpu(name):
    prog = MODULE.PROGRAMS[name]
    with tempfile.TemporaryDirectory() as tmp:
        got = MODULE.run_iverilog(MODULE.SOURCES, MODULE.program_stream(prog), Path(tmp))
    assert got == MODULE.reference(prog)
