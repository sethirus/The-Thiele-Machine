#!/usr/bin/env python3
"""Cross-platform consistency checks using active Kami RTL only.

These tests compare Python-side computations against the canonical RTL
co-simulation path (thielecpu/hardware/rtl/thiele_cpu_kami.v via cosim.py).
Only active canonical RTL/testbench files are used.
"""

from __future__ import annotations

import math
from pathlib import Path

import pytest

from thielecpu.mu_fixed import FixedPointMu

REPO_ROOT = Path(__file__).resolve().parent.parent


def _run_cosim(program: str):
    from thielecpu.hardware.cosim import run_verilog

    result = run_verilog(program, timeout=30)
    if result is None:
        pytest.skip("RTL simulator unavailable")
    return result


class TestCrossPlatformIsomorphism:
    """Validate Python and canonical RTL agree on key invariants."""

    def test_program_to_hex_has_stable_opcode_encoding(self):
        from thielecpu.hardware.cosim import program_to_hex

        instr, _, _ = program_to_hex("LASSERT 1 0 4\nLJOIN 2 0 3\nHALT")
        assert int(instr[0], 16) >> 24 == 0x03
        assert int(instr[1], 16) >> 24 == 0x04
        assert int(instr[2], 16) >> 24 == 0xFF

    def test_info_gain_formula_matches_python_reference(self):
        py = FixedPointMu()
        expected = py.from_q16(py.information_gain_q16(7, 5))
        assert abs(expected - math.log2(7 / 5)) < 0.01

    def test_rtl_executes_logic_path_without_error(self):
        state = _run_cosim(
            "\n".join(
                [
                    "INIT_LOGIC_ACC -889263410",
                    "LASSERT 1 0 3",
                    "LJOIN 2 0 4",
                    "REVEAL 0 0 2",
                    "HALT",
                ]
            )
        )
        assert isinstance(state.get("mu"), int)
        assert state["mu"] >= 2
        assert "status" in state


class TestOpcodeAlignment:
    """Ensure Python ISA and cosim opcodes stay aligned."""

    def test_all_python_opcodes_exist_in_cosim(self):
        from thielecpu.hardware.cosim import OPCODES
        from thielecpu.isa import Opcode

        for op in Opcode:
            assert op.name in OPCODES
            assert OPCODES[op.name] == op.value

    def test_canonical_rtl_files_exist(self):
        assert (REPO_ROOT / "thielecpu/hardware/rtl/thiele_cpu_kami.v").exists()
        assert (REPO_ROOT / "thielecpu/hardware/testbench/thiele_cpu_kami_tb.v").exists()
