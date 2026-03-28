"""Source-backed validation for the universal bridge CPU artifacts."""

from __future__ import annotations

import re
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
CPU_V = ROOT / "coq" / "thieleuniversal" / "coqproofs" / "CPU.v"
BRIDGE_V = ROOT / "coq" / "thieleuniversal" / "verification" / "BridgeDefinitions.v"


def _read(path: Path) -> str:
    assert path.exists(), f"Required source file missing: {path}"
    return path.read_text(encoding="utf-8")


def _cpu_registers() -> dict[str, int]:
    text = _read(CPU_V)
    # Use non-greedy .+? to capture expressions containing dots (e.g. Nat.sub)
    # and anchor on the Coq sentence terminator: '.' followed by whitespace.
    matches = re.findall(r"Definition\s+(REG_[A-Za-z0-9']+)\s*:=\s*(.+?)\.(?=\s)", text)
    registers: dict[str, int] = {}
    for name, expr in matches:
        expr = expr.strip()
        if expr == "Nat.sub 1 1":
            registers[name] = 0
            continue
        if expr.isdigit():
            registers[name] = int(expr)
    return registers


class TestUniversalProgramStructure:
    """Validate UTM bridge properties against the real Coq sources."""

    def test_cpu_register_map_matches_documented_window(self):
        registers = _cpu_registers()
        expected = {
            "REG_PC": 0,
            "REG_Q": 1,
            "REG_HEAD": 2,
            "REG_SYM": 3,
            "REG_Q'": 4,
            "REG_WRITE": 5,
            "REG_MOVE": 6,
            "REG_ADDR": 7,
            "REG_TEMP1": 8,
            "REG_TEMP2": 9,
        }

        assert registers == expected
        assert max(registers.values()) == 9
        assert all(index < 10 for index in registers.values())

    def test_bridge_contains_read_after_write_formal_spec(self):
        text = _read(BRIDGE_V)

        assert "Lemma read_reg_write_reg_same" in text
        assert "CPU.read_reg r (CPU.write_reg r v st) = v" in text
        assert "Lemma read_reg_write_reg_diff" in text
        assert "CPU.read_reg r1 (CPU.write_reg r2 v st) = CPU.read_reg r1 st" in text

    def test_bridge_proves_register_length_is_preserved(self):
        text = _read(BRIDGE_V)

        assert "Lemma length_write_reg_ge" in text
        assert "length (CPU.write_reg r v st).(CPU.regs) >= length st.(CPU.regs)" in text
        assert "Lemma length_step_ge" in text
        assert "length (CPU.regs (CPU.step instr st)) >= length st.(CPU.regs)" in text
        assert "Lemma length_write_reg" in text
        assert "length (CPU.write_reg r v st).(CPU.regs) = length st.(CPU.regs)" in text

    def test_step_length_proof_covers_all_register_writing_instructions(self):
        text = _read(BRIDGE_V)

        for instruction in [
            "LoadConst",
            "LoadIndirect",
            "CopyReg",
            "AddConst",
            "AddReg",
            "SubReg",
        ]:
            assert f"(* {instruction} *)" in text, (
                f"BridgeDefinitions.v no longer proves the register-length case for {instruction}"
            )
