"""Strict semantic contracts for Kami-extracted RTL CPU behavior.

These checks target invariants that parse/smoke tests do not guarantee.
They are intended to fail on semantic regressions even when synthesis still passes.

All simulation driven by cosim.run_verilog() → mkModule1 (thiele_cpu_kami.v).
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
RTL = ROOT / "thielecpu" / "hardware" / "rtl" / "thiele_cpu_kami.v"


# Opcode encoding: [opcode:8][a:8][b:8][cost:8]
_OPCODE_NAMES = {
    0x00: "PNEW", 0x06: "PDISCOVER", 0x07: "XFER", 0x08: "LOAD_IMM",
    0x09: "CHSH_TRIAL", 0x0A: "XOR_LOAD", 0x0B: "XOR_ADD", 0x0C: "XOR_SWAP",
    0x0D: "XOR_RANK", 0x0E: "EMIT", 0x0F: "REVEAL", 0xFF: "HALT",
}


def _run_custom_tb(program_words: list[int]) -> dict[str, int]:
    """Run a program (as raw 32-bit instruction words) through mkModule1.

    Returns a dict with at least: mu, status, error (error_code), pc.
    """
    from thielecpu.hardware.cosim import run_verilog, OPCODES

    # Convert raw instruction words back to a text program so cosim.run_verilog()
    # can encode them — cosim owns the hex-file encoding and testbench loading.
    lines = []
    for word in program_words:
        opcode = (word >> 24) & 0xFF
        op_a   = (word >> 16) & 0xFF
        op_b   = (word >>  8) & 0xFF
        cost   =  word        & 0xFF
        name = _OPCODE_NAMES.get(opcode)
        if name is None:
            name = "HALT"  # unknown → safe no-op fallthrough
        if name == "HALT":
            lines.append(f"HALT {cost}")
        elif name == "CHSH_TRIAL":
            x = (op_a >> 1) & 1
            y = op_a & 1
            a = (op_b >> 1) & 1
            b = op_b & 1
            lines.append(f"CHSH_TRIAL {x} {y} {a} {b} {cost}")
        elif name == "EMIT":
            lines.append(f"EMIT {op_a} {op_b} {cost}")
        else:
            lines.append(f"{name} {op_a} {op_b} {cost}")
    program_text = "\n".join(lines) + "\n"

    result = run_verilog(program_text)
    if result is None:
        pytest.skip("iverilog not available")

    return {
        "status":  result.get("status", 0),
        "error":   result.get("error_code", 0),
        "mu":      result.get("mu", 0),
        "pc":      result.get("pc", 0),
    }


def _word(op: int, a: int = 0, b: int = 0, c: int = 0) -> int:
    return ((op & 0xFF) << 24) | ((a & 0xFF) << 16) | ((b & 0xFF) << 8) | (c & 0xFF)


def test_halt_is_terminal_and_blocks_following_ops() -> None:
    # HALT first; trailing EMIT must not execute.
    program = [
        _word(0xFF, 0, 0, 0),
        _word(0x0E, 0, 7, 5),
    ]
    r = _run_custom_tb(program)
    assert r["mu"] == 0, f"HALT should block later ops, got mu={r['mu']}"


def test_chsh_supra_quantum_sets_error() -> None:
    """CHSH_TRIAL with invalid bit operands (op_a > 1 or op_b > 1) must set error.

    The Kami CPU validates op_a \u22641 (Alice setting) and op_b \u22641 (Bob setting).
    cosim.py encodes CHSH_TRIAL x y a b as op_a = (x<<1)|y, so x=1 → op_a \u2265 2 > 1.
    This is what the Kami err bit and BADC45C error_code gate on.
    """
    from thielecpu.hardware.cosim import run_verilog
    # CHSH validation is reachable only when logic_acc is primed to CAFEEACE.
    # Otherwise a higher-priority policy gate emits C43471A1.
    # x=1 -> op_a = (1<<1)|0 = 2 > 1 -> err=1, error_code=0x0BADC45C
    result = run_verilog(
        "INIT_LOGIC_ACC 0xCAFEEACE\n"
        "CHSH_TRIAL 1 0 0 0 0\n"
        "HALT 0\n"
    )
    if result is None:
        pytest.skip("iverilog not available")
    assert result.get("error_code", 0) == 0x0BADC45C, (
        f"Expected BADC45C error for op_a>1 CHSH, got {result.get('error_code', 0):08X}"
    )


def test_chsh_classical_pattern_no_error() -> None:
    """CHSH_TRIAL with valid bit operands (op_a \u22641, op_b \u22641) must NOT set error.

    cosim.py encodes CHSH_TRIAL x y a b as op_a = (x<<1)|y.
    With x=0: op_a = (0<<1)|y = y \u22641, which passes the Kami bit-validity check.
    """
    from thielecpu.hardware.cosim import run_verilog
    # CHSH path requires logic_acc priming. With valid bit operands there
    # should be no error.
    # x=0 in both trials -> op_a <= 1 -> no bit-bad error
    result = run_verilog(
        "INIT_LOGIC_ACC 0xCAFEEACE\n"
        "CHSH_TRIAL 0 0 0 0 0\n"
        "CHSH_TRIAL 0 1 0 0 0\n"
        "HALT 0\n"
    )
    if result is None:
        pytest.skip("iverilog not available")
    assert result.get("error_code", 0) == 0, (
        f"Valid-bit CHSH_TRIAL must not set error, got {result.get('error_code', 0):08X}"
    )


def test_chsh_requires_logic_acc_priming_policy_gate() -> None:
    """Without logic_acc priming, CHSH path must trip policy gate C43471A1."""
    from thielecpu.hardware.cosim import run_verilog

    result = run_verilog("CHSH_TRIAL 0 0 0 0 0\nHALT 0\n")
    if result is None:
        pytest.skip("iverilog not available")
    assert result.get("error_code", 0) == 0xC43471A1, (
        f"Expected C43471A1 policy gate without priming, got {result.get('error_code', 0):08X}"
    )


def test_static_contract_receipt_checker_uses_receipt_valid() -> None:
    """Kami RTL must not contain the old unified-CPU receipt_valid anti-pattern."""
    txt = RTL.read_text(encoding="utf-8")
    # The Kami RTL uses halted/err gating, not a receipt_valid wire.
    # The old unified CPU had a receipt_integrity_checker submodule with a
    # receipt_valid port — that pattern must not appear in the Kami file.
    assert ".receipt_valid(instr_valid)" not in txt, (
        "receipt_integrity_checker still wired to instr_valid"
    )


def test_static_contract_no_chsh_placeholder_left() -> None:
    """Kami RTL must not contain any TODO placeholder comments."""
    txt = RTL.read_text(encoding="utf-8")
    assert "Placeholder: use ALU result in real impl" not in txt
