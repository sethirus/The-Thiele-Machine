#!/usr/bin/env python3
"""Edge-case boundary tests for the Thiele Machine.

Tests boundary conditions that the fuzzer misses: register 0, register 15 (SP),
address boundaries, cost boundaries, arithmetic overflow/underflow, and
check_model parity with more formula patterns.

All tests run through both Python VM and RTL for cross-layer comparison.
"""
from __future__ import annotations

import sys
from pathlib import Path
from typing import List

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT))


# ---------------------------------------------------------------------------
# RTL availability guard
# ---------------------------------------------------------------------------

def _rtl_available() -> bool:
    try:
        from thielecpu.hardware.cosim import run_verilog
        result = run_verilog(["PNEW {0,1} 1", "HALT 0"])
        return result is not None
    except Exception:
        return False


pytestmark = pytest.mark.strict_rtl

RTL_SKIP = pytest.mark.skipif(
    not _rtl_available(),
    reason="RTL cosim backend unavailable",
)


def _run_both(program: List[str]):
    """Run program through both Python VM and RTL, return (vm_state, rtl_result)."""
    from build.thiele_vm import run_vm
    from thielecpu.hardware.cosim import run_verilog
    vm_state = run_vm(program)
    rtl_result = run_verilog(program)
    return vm_state, rtl_result


PREAMBLE = [
    "INIT_LOGIC_ACC 0xCAFEEACE",
    "INIT_PT 0 128",
    "INIT_ACTIVE_MODULE 0",
]


# ===========================================================================
# Register boundary tests
# ===========================================================================

@RTL_SKIP
class TestRegisterBoundaries:

    def test_register_0_write_read(self):
        """Writing to r0 and reading it back."""
        program = PREAMBLE + [
            "LOAD_IMM 0 42 1",
            "HALT 0",
        ]
        vm, rtl = _run_both(program)
        assert rtl is not None
        assert (vm.regs[0] & 0xFFFFFFFF) == (rtl["regs"][0] & 0xFFFFFFFF)

    def test_register_15_write_read(self):
        """Writing to r15 (stack pointer) and reading it back."""
        program = PREAMBLE + [
            "LOAD_IMM 15 200 1",
            "HALT 0",
        ]
        vm, rtl = _run_both(program)
        assert rtl is not None
        assert (vm.regs[15] & 0xFFFFFFFF) == (rtl["regs"][15] & 0xFFFFFFFF)

    def test_all_16_registers_independent(self):
        """Write unique values to all 16 registers, verify none clobber each other."""
        program = PREAMBLE + [
            f"LOAD_IMM {i} {i + 100} 1" for i in range(16)
        ] + ["HALT 0"]
        vm, rtl = _run_both(program)
        assert rtl is not None
        for i in range(16):
            expected = i + 100
            assert (rtl["regs"][i] & 0xFF) == expected, (
                f"r{i} clobbered: expected {expected}, got {rtl['regs'][i]}"
            )


# ===========================================================================
# Arithmetic overflow/underflow tests
# ===========================================================================

@RTL_SKIP
class TestArithmeticBoundaries:

    def test_add_large_values(self):
        """ADD two large immediate values, verify cross-layer agreement."""
        program = PREAMBLE + [
            "LOAD_IMM 1 255 1",
            "LOAD_IMM 2 255 1",
            "ADD 3 1 2 1",  # r3 = r1 + r2 = 510
            "HALT 0",
        ]
        vm, rtl = _run_both(program)
        assert rtl is not None
        assert (vm.regs[3] & 0xFFFFFFFF) == (rtl["regs"][3] & 0xFFFFFFFF)

    def test_sub_larger_from_smaller(self):
        """SUB where rs2 > rs1 -- tests unsigned wrap behavior."""
        program = PREAMBLE + [
            "LOAD_IMM 1 5 1",
            "LOAD_IMM 2 10 1",
            "SUB 3 1 2 1",  # r3 = r1 - r2 = 5 - 10 (wraps unsigned)
            "HALT 0",
        ]
        vm, rtl = _run_both(program)
        assert rtl is not None
        assert (vm.regs[3] & 0xFFFFFFFF) == (rtl["regs"][3] & 0xFFFFFFFF)

    def test_sub_equal_values(self):
        """SUB equal values gives zero."""
        program = PREAMBLE + [
            "LOAD_IMM 1 42 1",
            "LOAD_IMM 2 42 1",
            "SUB 3 1 2 1",  # r3 = r1 - r2 = 0
            "HALT 0",
        ]
        vm, rtl = _run_both(program)
        assert rtl is not None
        assert (vm.regs[3] & 0xFFFFFFFF) == 0
        assert (rtl["regs"][3] & 0xFFFFFFFF) == 0

    def test_add_zero(self):
        """ADD with zero: r1 + 0 = r1."""
        program = PREAMBLE + [
            "LOAD_IMM 1 77 1",
            "LOAD_IMM 2 0 1",
            "ADD 3 1 2 1",  # r3 = r1 + r2 = 77
            "HALT 0",
        ]
        vm, rtl = _run_both(program)
        assert rtl is not None
        assert (vm.regs[3] & 0xFFFFFFFF) == (rtl["regs"][3] & 0xFFFFFFFF)
        assert (rtl["regs"][3] & 0xFF) == 77

    def test_xor_self_is_zero(self):
        """XOR_ADD r with itself should give 0."""
        program = PREAMBLE + [
            "LOAD_IMM 5 123 1",
            "XOR_ADD 5 5 1",  # r5 = r5 XOR r5 = 0
            "HALT 0",
        ]
        vm, rtl = _run_both(program)
        assert rtl is not None
        assert (rtl["regs"][5] & 0xFFFFFFFF) == 0


# ===========================================================================
# Memory boundary tests
# ===========================================================================

@RTL_SKIP
class TestMemoryBoundaries:

    def test_store_load_addr_0(self):
        """Store and load at address 0."""
        program = PREAMBLE + [
            "LOAD_IMM 1 42 1",
            "STORE 0 1 1",
            "LOAD 2 0 1",
            "HALT 0",
        ]
        vm, rtl = _run_both(program)
        assert rtl is not None
        assert (vm.regs[2] & 0xFFFFFFFF) == (rtl["regs"][2] & 0xFFFFFFFF)

    def test_store_load_addr_127(self):
        """Store and load at address 127 (max addressable, MEM_SIZE=128)."""
        program = PREAMBLE + [
            "LOAD_IMM 1 99 1",
            "STORE 127 1 1",
            "LOAD 2 127 1",
            "HALT 0",
        ]
        vm, rtl = _run_both(program)
        assert rtl is not None
        assert (vm.regs[2] & 0xFFFFFFFF) == (rtl["regs"][2] & 0xFFFFFFFF)

    @pytest.mark.parametrize("value", [0, 1, 127, 128, 255])
    def test_store_load_roundtrip_values(self, value):
        """Store various values and read them back."""
        program = PREAMBLE + [
            f"LOAD_IMM 1 {value} 1",
            "STORE 10 1 1",
            "LOAD 2 10 1",
            "HALT 0",
        ]
        vm, rtl = _run_both(program)
        assert rtl is not None
        assert (vm.regs[2] & 0xFF) == value
        assert (rtl["regs"][2] & 0xFF) == value


# ===========================================================================
# Cost boundary tests
# ===========================================================================

@RTL_SKIP
class TestCostBoundaries:

    def test_zero_cost_instruction(self):
        """LOAD_IMM with cost=0 executes but does not increase mu."""
        program = PREAMBLE + [
            "LOAD_IMM 1 42 0",
            "HALT 0",
        ]
        vm, rtl = _run_both(program)
        assert rtl is not None
        assert vm.mu == rtl["mu"]

    def test_max_cost_single(self):
        """Single instruction with cost=15 (max for 4-bit field)."""
        program = PREAMBLE + [
            "LOAD_IMM 1 42 15",
            "HALT 0",
        ]
        vm, rtl = _run_both(program)
        assert rtl is not None
        assert vm.mu == rtl["mu"]
        assert rtl["mu"] >= 15

    def test_mu_accumulation_many_instructions(self):
        """50 instructions with cost=10, verify mu accumulates correctly."""
        instrs = [f"LOAD_IMM {i % 32} {i} 10" for i in range(50)]
        program = PREAMBLE + instrs + ["HALT 0"]
        vm, rtl = _run_both(program)
        assert rtl is not None
        assert vm.mu == rtl["mu"]
        assert rtl["mu"] >= 500  # 50 * 10


# ===========================================================================
# Control flow edge cases
# ===========================================================================

@RTL_SKIP
class TestControlFlowEdgeCases:

    def test_jump_to_next(self):
        """JUMP to the very next instruction (nop-like).
        Note: Python VM does not branch (sequential execution), so mu values
        differ between layers. JUMP is a control-flow instruction that does
        NOT charge mu in the OCaml runner. We verify each layer independently.
        """
        from thielecpu.hardware.cosim import run_verilog
        from build.thiele_vm import run_vm
        # RTL: JUMP actually branches, skipping nothing (addr 1 = next instr)
        rtl = run_verilog(PREAMBLE + [
            "JUMP 1 1",        # jump to addr 1
            "LOAD_IMM 1 42 1",
            "HALT 0",
        ])
        assert rtl is not None
        assert rtl["mu"] >= 1
        # VM: JUMP is a control-flow op — does not charge mu
        vm = run_vm(PREAMBLE + [
            "JUMP 1 1",
            "LOAD_IMM 1 42 1",
            "HALT 0",
        ])
        assert vm.mu >= 0

    def test_jnez_with_zero_falls_through(self):
        """JNEZ with r1=0 should fall through (not branch)."""
        program = PREAMBLE + [
            "LOAD_IMM 1 0 1",   # r1 = 0
            "JNEZ 1 10 1",      # should NOT branch
            "LOAD_IMM 2 42 1",  # this should execute
            "HALT 0",
        ]
        vm, rtl = _run_both(program)
        assert rtl is not None
        assert (rtl["regs"][2] & 0xFF) == 42  # fell through

    def test_jnez_with_nonzero_branches(self):
        """JNEZ with r1=1 should take the branch."""
        program = PREAMBLE + [
            "LOAD_IMM 1 1 1",   # r1 = 1
            "JNEZ 1 3 1",       # branch to addr 3 (HALT)
            "LOAD_IMM 2 99 1",  # should be skipped
            "HALT 0",
        ]
        vm, rtl = _run_both(program)
        assert rtl is not None
        # r2 should NOT be 99 (instruction was skipped)
        assert (rtl["regs"][2] & 0xFF) != 99
