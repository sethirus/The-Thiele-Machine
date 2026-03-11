#!/usr/bin/env python3
"""Test assembler programs on RTL cosim.

Verifies that the four standard programs assemble correctly and execute
on the Verilog RTL simulation with expected results.
"""
from __future__ import annotations

import os
import pytest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
PROGRAMS_DIR = REPO_ROOT / "programs"


def _rtl_available() -> bool:
    try:
        from rtl_harness.cosim import run_verilog
        result = run_verilog("LOAD_IMM 1 1 0\nHALT 0")
        return result is not None
    except Exception:
        return False


RTL_SKIP = pytest.mark.skipif(
    not _rtl_available(),
    reason="RTL cosim backend unavailable",
)


def _assemble_and_run(program_path: Path) -> dict:
    """Assemble a .asm file and run through RTL cosim."""
    import sys
    sys.path.insert(0, str(REPO_ROOT))
    from scripts.thiele_asm import assemble, to_trace
    from rtl_harness.cosim import run_verilog

    source = program_path.read_text()
    instructions, data_memory, metadata = assemble(source)
    trace = to_trace(instructions, data_memory, metadata)
    result = run_verilog(trace)
    return result


@RTL_SKIP
class TestAssemblerPrograms:
    """Verify assembler programs on RTL cosim."""

    def test_hello_world(self):
        result = _assemble_and_run(PROGRAMS_DIR / "hello_world.asm")
        assert result is not None
        assert result.get("status") == 2, f"Expected halted (status=2), got {result.get('status')}"
        assert not result.get("err"), f"Unexpected error: {result.get('error_code')}"
        regs = result.get("regs", [0] * 32)
        assert regs[1] == 42, f"r1={regs[1]}, expected 42"
        assert regs[2] == 58, f"r2={regs[2]}, expected 58"
        assert regs[3] == 100, f"r3={regs[3]}, expected 100"
        mem = result.get("mem", [0] * 256)
        assert mem[0] == 100, f"mem[0]={mem[0]}, expected 100"

    def test_fibonacci(self):
        result = _assemble_and_run(PROGRAMS_DIR / "fibonacci.asm")
        assert result is not None
        assert result.get("status") == 2, f"Expected halted (status=2), got {result.get('status')}"
        assert not result.get("err"), f"Unexpected error: {result.get('error_code')}"
        regs = result.get("regs", [0] * 32)
        # fib(10) = 55
        assert regs[2] == 55 or regs[3] == 55, f"fib(10) not found: r2={regs[2]}, r3={regs[3]}"
        mem = result.get("mem", [0] * 256)
        assert mem[0] == 55, f"mem[0]={mem[0]}, expected 55"

    def test_stress_memory(self):
        result = _assemble_and_run(PROGRAMS_DIR / "stress_memory.asm")
        assert result is not None
        assert result.get("status") == 2, f"Expected halted (status=2), got {result.get('status')}"
        assert not result.get("err"), f"Unexpected error: {result.get('error_code')}"
        regs = result.get("regs", [0] * 32)
        # r2 should be 0 (loop counter exhausted)
        assert regs[2] == 0, f"r2={regs[2]}, expected 0 (loop exhausted)"
        # mu should be substantial (200 iterations × ~4 cost per iter)
        assert result.get("mu", 0) > 100, f"mu={result.get('mu')}, expected > 100"

    def test_all_opcodes(self):
        result = _assemble_and_run(PROGRAMS_DIR / "all_opcodes_test.asm")
        assert result is not None
        assert result.get("status") == 2, f"Expected halted (status=2), got {result.get('status')}"
        assert not result.get("err"), f"Unexpected error at PC={result.get('pc')}"
        regs = result.get("regs", [0] * 32)
        assert regs[3] == 100, f"r3={regs[3]}, expected 100 (42+58)"
        assert regs[4] == 16, f"r4={regs[4]}, expected 16 (58-42)"
        assert regs[5] == 42, f"r5={regs[5]}, expected 42 (XFER)"
        assert regs[10] == 99, f"r10={regs[10]}, expected 99 (LOAD)"
        assert regs[8] == 88, f"r8={regs[8]}, expected 88 (CALL/RET)"
        assert regs[6] == 1, f"r6={regs[6]}, expected 1 (JUMP)"
        assert regs[7] == 7, f"r7={regs[7]}, expected 7 (JNEZ)"
        # New bitwise/arithmetic opcodes
        assert regs[12] == 42, f"r12={regs[12]}, expected 42 (AND 42&58)"
        assert regs[13] == 58, f"r13={regs[13]}, expected 58 (OR 42|58)"
        assert regs[14] == 2, f"r14={regs[14]}, expected 2 (SHL 1<<1)"
        assert regs[15] == 29, f"r15={regs[15]}, expected 29 (SHR 58>>1)"
        assert regs[16] == 2436, f"r16={regs[16]}, expected 2436 (MUL 42*58)"
        assert regs[17] == 43776, f"r17={regs[17]}, expected 43776 (LUI 0xAB)"
        mem = result.get("mem", [0] * 256)
        assert mem[2] == 100, f"mem[2]={mem[2]}, expected 100 (STORE)"
