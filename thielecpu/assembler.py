"""Thiele CPU Assembler — two-pass assembler with labels, macros, and diagnostics.

Usage:
    from thielecpu.assembler import Assembler
    asm = Assembler()
    hex_output = asm.assemble_file("program.asm")

Or from CLI:
    python -m thielecpu.assembler program.asm -o program.hex
"""

from __future__ import annotations

import re
import sys
from pathlib import Path
from typing import Dict, List, Optional, Tuple

# Canonical opcode encoding — MUST match cosim.py / generated_opcodes.vh / Coq
OPCODES: Dict[str, int] = {
    "PNEW": 0x00,
    "PSPLIT": 0x01,
    "PMERGE": 0x02,
    "LASSERT": 0x03,
    "LJOIN": 0x04,
    "MDLACC": 0x05,
    "PDISCOVER": 0x06,
    "XFER": 0x07,
    "LOAD_IMM": 0x08,
    "CHSH_TRIAL": 0x09,
    "XOR_LOAD": 0x0A,
    "XOR_ADD": 0x0B,
    "XOR_SWAP": 0x0C,
    "XOR_RANK": 0x0D,
    "EMIT": 0x0E,
    "REVEAL": 0x0F,
    "ORACLE_HALTS": 0x10,
    "LOAD": 0x11,
    "STORE": 0x12,
    "ADD": 0x13,
    "SUB": 0x14,
    "JUMP": 0x15,
    "JNEZ": 0x16,
    "CALL": 0x17,
    "RET": 0x18,
    "HALT": 0xFF,
}

# Symbolic register names
REG_ALIASES: Dict[str, int] = {
    "sp": 31, "SP": 31,
    "zero": 0, "ZERO": 0,
}
for i in range(32):
    REG_ALIASES[f"r{i}"] = i
    REG_ALIASES[f"R{i}"] = i


class AsmError(Exception):
    """Assembly error with source location."""

    def __init__(self, filename: str, line: int, col: int, msg: str):
        self.filename = filename
        self.line = line
        self.col = col
        self.msg = msg
        super().__init__(f"{filename}:{line}:{col}: error: {msg}")


class Assembler:
    """Two-pass assembler for the Thiele CPU ISA."""

    def __init__(self) -> None:
        self.labels: Dict[str, int] = {}
        self.instructions: List[Tuple[int, str, str, int]] = []  # (line, op, args, addr)
        self.filename = "<stdin>"
        self.errors: List[str] = []
        self.data_mem: Dict[int, int] = {}

    def _error(self, line: int, msg: str, col: int = 1) -> None:
        self.errors.append(f"{self.filename}:{line}:{col}: error: {msg}")

    def _resolve_reg(self, tok: str, line: int) -> int:
        """Resolve a register token to an index 0-31."""
        if tok in REG_ALIASES:
            return REG_ALIASES[tok]
        try:
            val = int(tok)
            if 0 <= val <= 31:
                return val
            self._error(line, f"register index out of range (0-31): {tok}")
            return 0
        except ValueError:
            self._error(line, f"invalid register: {tok}")
            return 0

    def _resolve_value(self, tok: str, line: int, bits: int = 8) -> int:
        """Resolve a numeric or label token to an integer."""
        # Check for label reference
        if tok in self.labels:
            return self.labels[tok]
        # Hex literal
        if tok.startswith("0x") or tok.startswith("0X"):
            try:
                val = int(tok, 16)
            except ValueError:
                self._error(line, f"invalid hex literal: {tok}")
                return 0
        else:
            try:
                val = int(tok)
            except ValueError:
                self._error(line, f"undefined symbol: {tok}")
                return 0
        maxval = (1 << bits) - 1
        if val < 0 or val > maxval:
            self._error(line, f"value {val} out of range (0-{maxval})")
        return val & maxval

    def _expand_macros(self, op: str, args: str, line: int) -> List[Tuple[str, str]]:
        """Expand pseudo-instructions / macros into real instructions."""
        op_upper = op.upper()
        if op_upper == "PUSH":
            # PUSH rN [cost] → STORE [SP] rN cost; ADD SP SP 1
            parts = args.split()
            reg = parts[0] if parts else "r0"
            cost = parts[1] if len(parts) > 1 else "1"
            return [
                ("STORE", f"sp {reg} {cost}"),  # store at [SP]
            ]
        elif op_upper == "POP":
            # POP rN [cost] → LOAD rN [SP] cost
            parts = args.split()
            reg = parts[0] if parts else "r0"
            cost = parts[1] if len(parts) > 1 else "1"
            return [
                ("LOAD", f"{reg} sp {cost}"),
            ]
        elif op_upper == "NOP":
            parts = args.split()
            cost = parts[0] if parts else "0"
            return [("LOAD_IMM", f"r0 0 {cost}")]
        elif op_upper == "MOV":
            # MOV dst src [cost] → XFER dst src cost
            parts = args.split()
            dst = parts[0] if len(parts) > 0 else "r0"
            src = parts[1] if len(parts) > 1 else "r0"
            cost = parts[2] if len(parts) > 2 else "1"
            return [("XFER", f"{dst} {src} {cost}")]
        return [(op, args)]

    def _encode(self, op: str, operand_a: int, operand_b: int, cost: int) -> int:
        """Encode a single 32-bit instruction word."""
        opcode = OPCODES.get(op.upper())
        if opcode is None:
            return 0
        return ((opcode & 0xFF) << 24) | ((operand_a & 0xFF) << 16) | \
               ((operand_b & 0xFF) << 8) | (cost & 0xFF)

    def _assemble_instruction(self, line: int, op: str, args: str) -> int:
        """Assemble a single instruction, return 32-bit word."""
        op = op.upper()
        parts = args.split() if args else []

        if op not in OPCODES:
            self._error(line, f"unknown opcode: {op}")
            return 0

        # Instruction-specific operand parsing
        if op == "HALT":
            cost = self._resolve_value(parts[0], line) if parts else 0
            return self._encode("HALT", 0, 0, cost)

        elif op == "RET":
            cost = self._resolve_value(parts[0], line) if parts else 0
            return self._encode("RET", 0, 0, cost)

        elif op == "LOAD_IMM":
            if len(parts) < 2:
                self._error(line, "LOAD_IMM requires: reg imm [cost]")
                return 0
            reg = self._resolve_reg(parts[0], line)
            imm = self._resolve_value(parts[1], line)
            cost = self._resolve_value(parts[2], line) if len(parts) > 2 else 0
            return self._encode("LOAD_IMM", reg, imm, cost)

        elif op == "XFER":
            if len(parts) < 2:
                self._error(line, "XFER requires: dst src [cost]")
                return 0
            dst = self._resolve_reg(parts[0], line)
            src = self._resolve_reg(parts[1], line)
            cost = self._resolve_value(parts[2], line) if len(parts) > 2 else 0
            return self._encode("XFER", dst, src, cost)

        elif op == "LOAD":
            if len(parts) < 2:
                self._error(line, "LOAD requires: reg addr [cost]")
                return 0
            reg = self._resolve_reg(parts[0], line)
            addr = self._resolve_value(parts[1], line)
            cost = self._resolve_value(parts[2], line) if len(parts) > 2 else 0
            return self._encode("LOAD", reg, addr, cost)

        elif op == "STORE":
            if len(parts) < 2:
                self._error(line, "STORE requires: addr reg [cost]")
                return 0
            addr = self._resolve_value(parts[0], line)
            reg = self._resolve_reg(parts[1], line)
            cost = self._resolve_value(parts[2], line) if len(parts) > 2 else 0
            return self._encode("STORE", addr, reg, cost)

        elif op in ("ADD", "SUB"):
            if len(parts) >= 3:
                # 3-register form: ADD dst rs1 rs2 [cost]
                dst = self._resolve_reg(parts[0], line)
                rs1 = self._resolve_reg(parts[1], line)
                rs2 = self._resolve_reg(parts[2], line)
                cost = self._resolve_value(parts[3], line) if len(parts) > 3 else 0
                op_b = ((rs1 & 0xF) << 4) | (rs2 & 0xF)
                return self._encode(op, dst, op_b, cost)
            elif len(parts) >= 2:
                # Legacy: ADD dst packed_op_b [cost]
                dst = self._resolve_reg(parts[0], line)
                op_b = self._resolve_value(parts[1], line)
                cost = self._resolve_value(parts[2], line) if len(parts) > 2 else 0
                return self._encode(op, dst, op_b, cost)
            else:
                self._error(line, f"{op} requires: dst rs1 rs2 [cost]")
                return 0

        elif op == "JUMP":
            if len(parts) < 1:
                self._error(line, "JUMP requires: target [cost]")
                return 0
            target = self._resolve_value(parts[0], line)
            cost = self._resolve_value(parts[1], line) if len(parts) > 1 else 0
            return self._encode("JUMP", target, 0, cost)

        elif op == "JNEZ":
            if len(parts) < 2:
                self._error(line, "JNEZ requires: reg target [cost]")
                return 0
            reg = self._resolve_reg(parts[0], line)
            target = self._resolve_value(parts[1], line)
            cost = self._resolve_value(parts[2], line) if len(parts) > 2 else 0
            return self._encode("JNEZ", reg, target, cost)

        elif op == "CALL":
            if len(parts) < 1:
                self._error(line, "CALL requires: target [cost]")
                return 0
            target = self._resolve_value(parts[0], line)
            cost = self._resolve_value(parts[1], line) if len(parts) > 1 else 0
            return self._encode("CALL", target, 0, cost)

        elif op in ("XOR_LOAD",):
            if len(parts) < 2:
                self._error(line, f"{op} requires: dst addr [cost]")
                return 0
            dst = self._resolve_reg(parts[0], line)
            addr = self._resolve_value(parts[1], line)
            cost = self._resolve_value(parts[2], line) if len(parts) > 2 else 0
            return self._encode(op, dst, addr, cost)

        elif op in ("XOR_ADD", "XOR_SWAP", "XOR_RANK"):
            if len(parts) < 2:
                self._error(line, f"{op} requires: a b [cost]")
                return 0
            a = self._resolve_reg(parts[0], line)
            b = self._resolve_reg(parts[1], line)
            cost = self._resolve_value(parts[2], line) if len(parts) > 2 else 0
            return self._encode(op, a, b, cost)

        elif op == "CHSH_TRIAL":
            if len(parts) >= 4:
                # 4-operand: x y a b [cost]
                x = self._resolve_value(parts[0], line)
                y = self._resolve_value(parts[1], line)
                a = self._resolve_value(parts[2], line)
                b = self._resolve_value(parts[3], line)
                cost = self._resolve_value(parts[4], line) if len(parts) > 4 else 0
                op_a = ((x & 0x1) << 1) | (y & 0x1)
                op_b = ((a & 0x1) << 1) | (b & 0x1)
                return self._encode("CHSH_TRIAL", op_a, op_b, cost)
            else:
                # Legacy: op_a op_b [cost]
                a = self._resolve_value(parts[0], line) if len(parts) > 0 else 0
                b = self._resolve_value(parts[1], line) if len(parts) > 1 else 0
                cost = self._resolve_value(parts[2], line) if len(parts) > 2 else 0
                return self._encode("CHSH_TRIAL", a, b, cost)

        elif op == "REVEAL":
            if len(parts) < 1:
                self._error(line, "REVEAL requires: tensor_idx [unused] cost")
                return 0
            idx = self._resolve_value(parts[0], line)
            b = self._resolve_value(parts[1], line) if len(parts) > 1 else 0
            cost = self._resolve_value(parts[2], line) if len(parts) > 2 else 0
            return self._encode("REVEAL", idx, b, cost)

        elif op == "MDLACC":
            mid = self._resolve_value(parts[0], line) if len(parts) > 0 else 0
            cost = self._resolve_value(parts[1], line) if len(parts) > 1 else 0
            return self._encode("MDLACC", mid, 0, cost)

        else:
            # Generic 3-operand: OP a b cost
            a = self._resolve_value(parts[0], line) if len(parts) > 0 else 0
            b = self._resolve_value(parts[1], line) if len(parts) > 1 else 0
            cost = self._resolve_value(parts[2], line) if len(parts) > 2 else 0
            return self._encode(op, a, b, cost)

    def assemble(self, source: str, filename: str = "<stdin>") -> Tuple[List[str], List[str]]:
        """Assemble source text into hex instruction and data memory images.

        Returns (instr_hex_lines, data_hex_lines).
        Raises AsmError on first error.
        """
        self.filename = filename
        self.labels = {}
        self.errors = []
        self.data_mem = {}

        lines = source.strip().split("\n")

        # ── Pass 1: collect labels and count instructions ──
        addr = 0
        raw_instructions: List[Tuple[int, str, str]] = []  # (source_line, op, args)

        for lineno_0, raw in enumerate(lines):
            lineno = lineno_0 + 1
            line = raw.strip()

            # Strip comments
            if "#" in line:
                line = line[:line.index("#")].strip()
            if ";" in line:
                line = line[:line.index(";")].strip()
            if not line:
                continue

            # Check for label definition  (LABEL:  or  LABEL: INSTR ...)
            m = re.match(r"^([A-Za-z_]\w*)\s*:\s*(.*)", line)
            if m:
                label_name = m.group(1)
                rest = m.group(2).strip()
                if label_name in self.labels:
                    self._error(lineno, f"duplicate label: {label_name}")
                self.labels[label_name] = addr
                if not rest:
                    continue
                line = rest

            parts = line.split(maxsplit=1)
            op = parts[0].upper()
            args = parts[1] if len(parts) > 1 else ""

            # Directives
            if op == ".DATA" or op == "INIT_MEM":
                d_parts = args.split()
                if len(d_parts) >= 2:
                    self.data_mem[int(d_parts[0])] = int(d_parts[1])
                continue
            if op == "FUEL" or op == "INIT_REG":
                continue

            # Expand macros
            expanded = self._expand_macros(op, args, lineno)
            for eop, eargs in expanded:
                raw_instructions.append((lineno, eop, eargs))
                addr += 1

        if addr > 256:
            self._error(0, f"program too large: {addr} instructions (max 256)")

        # ── Pass 2: assemble instructions with resolved labels ──
        words: List[int] = []
        for lineno, op, args in raw_instructions:
            word = self._assemble_instruction(lineno, op, args)
            words.append(word)

        if self.errors:
            raise AsmError(self.filename, 0, 0, "\n".join(self.errors))

        # Convert to hex
        instr_hex = [f"{w:08X}" for w in words]
        while len(instr_hex) < 256:
            instr_hex.append("00000000")

        data_hex = [f"{self.data_mem.get(i, 0):08X}" for i in range(256)]

        return instr_hex, data_hex

    def assemble_file(self, path: str) -> str:
        """Assemble a file and return hex output as a string."""
        p = Path(path)
        source = p.read_text()
        instr_hex, data_hex = self.assemble(source, filename=str(p))
        return "\n".join(instr_hex)

    def assemble_to_files(self, path: str, out_instr: str, out_data: str) -> None:
        """Assemble a file and write instruction/data hex files."""
        p = Path(path)
        source = p.read_text()
        instr_hex, data_hex = self.assemble(source, filename=str(p))
        Path(out_instr).write_text("\n".join(instr_hex) + "\n")
        Path(out_data).write_text("\n".join(data_hex) + "\n")


def main() -> None:
    import argparse
    parser = argparse.ArgumentParser(
        prog="thiele-asm",
        description="Thiele CPU Assembler"
    )
    parser.add_argument("input", help="Assembly source file (.asm)")
    parser.add_argument("-o", "--output", help="Output hex file (default: stdout)")
    parser.add_argument("--data", help="Output data memory hex file")
    parser.add_argument("--list", action="store_true", help="Print listing with addresses")
    args = parser.parse_args()

    asm = Assembler()
    try:
        p = Path(args.input)
        source = p.read_text()
        instr_hex, data_hex = asm.assemble(source, filename=str(p))
    except AsmError as e:
        print(str(e), file=sys.stderr)
        sys.exit(1)
    except FileNotFoundError:
        print(f"error: file not found: {args.input}", file=sys.stderr)
        sys.exit(1)

    hex_output = "\n".join(instr_hex) + "\n"

    if args.list:
        # Print listing
        for i, h in enumerate(instr_hex):
            if h == "00000000" and i >= len([x for x in instr_hex if x != "00000000"]):
                break
            print(f"  {i:3d}  {h}")
        # Print labels
        if asm.labels:
            print("\nLabels:")
            for name, addr in sorted(asm.labels.items(), key=lambda x: x[1]):
                print(f"  {name:20s} = {addr}")

    if args.output:
        Path(args.output).write_text(hex_output)
        if args.data:
            Path(args.data).write_text("\n".join(data_hex) + "\n")
        print(f"Assembled {len([h for h in instr_hex if h != '00000000'])} instructions to {args.output}")
    elif not args.list:
        print(hex_output, end="")


if __name__ == "__main__":
    main()
