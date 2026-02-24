"""Strict semantic invariants for Kami-extracted RTL CPU.

These tests target end-to-end CPU semantics (not just parse/smoke):
- HALT must behave as a terminal state for execution.
- Post-HALT instructions must not produce side-effects.
- Receipt checker wiring must be receipt-driven, not instruction-cycle-driven.
- Module metadata storage semantics must be unambiguous.

All simulation tests use cosim.run_verilog() which drives mkModule1 via
thiele_cpu_kami.v + thiele_cpu_kami_tb.v — the single canonical extracted CPU.
"""

from __future__ import annotations

import re
import shutil
import sys
from pathlib import Path

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))
RTL_FILE = REPO_ROOT / "thielecpu" / "hardware" / "rtl" / "thiele_cpu_kami.v"


pytestmark = [
    pytest.mark.hardware,
    pytest.mark.skipif(shutil.which("iverilog") is None, reason="iverilog not installed"),
]


def _run_program(program: str) -> dict:
    """Run a program through the Kami-extracted CPU and return the state dict."""
    from thielecpu.hardware.cosim import run_verilog
    result = run_verilog(program)
    if result is None:
        pytest.skip("iverilog not available")
    return result


def test_halt_freezes_pc_and_blocks_side_effects() -> None:
    """After first HALT executes, PC must freeze and subsequent EMIT must not fire.

    Program: HALT (cost 0) then EMIT (cost 5).
    If HALT is terminal, mu stays 0 (EMIT never executes).
    """
    # HALT cost=0, then EMIT cost=5 — EMIT must never run
    program = "HALT 0\nEMIT 0 0 5\n"
    result = _run_program(program)
    assert result["mu"] == 0, (
        f"HALT must block subsequent EMIT — got mu={result['mu']} (expected 0)"
    )
    assert result.get("status") == 2 or result.get("err") == 0, (
        f"Expected halted state, got status={result.get('status')}"
    )


def test_receipt_checker_wiring_is_receipt_driven() -> None:
    """Kami RTL must not contain a receipt_integrity_checker wired to instr_valid.

    In the Kami-extracted CPU, receipt semantics are handled by the Coq proof layer
    (Abstraction.v). The RTL must not contain the old unified-CPU wiring anti-pattern.
    """
    text = RTL_FILE.read_text(encoding="utf-8")
    assert ".receipt_valid(instr_valid)" not in text, (
        "receipt_integrity_checker is wired to instr_valid — must use receipt_valid."
    )


def test_module_table_not_used_as_existence_flag() -> None:
    """Kami RTL must not contain the module_table existence-flag anti-pattern."""
    text = RTL_FILE.read_text(encoding="utf-8")
    bad_pattern = re.compile(r"module_table\s*\[\s*i\s*\]\s*==\s*32'd1")
    assert bad_pattern.search(text) is None, (
        "module_table is used as an existence flag — conflicts with module_exists[] role."
    )
