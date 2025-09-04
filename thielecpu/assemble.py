"""Tiny assembler for Thiele examples."""

from __future__ import annotations

from pathlib import Path
from typing import Iterable, List, Tuple

Instruction = Tuple[str, str]


def parse(lines: Iterable[str], base: Path) -> List[Instruction]:
    """Parse text ``lines`` into ``[(opcode, arg), ...]``."""
    program: List[Instruction] = []
    for line in lines:
        line = line.strip()
        if not line or line.startswith("#") or line.startswith(";"):
            continue
        # Remove inline comments
        if ";" in line:
            line = line.split(";")[0].strip()
        if not line:
            continue
        parts = line.split(maxsplit=1)
        op = parts[0].upper()
        arg = parts[1] if len(parts) > 1 else ""
        # Only resolve paths for opcodes that expect file arguments
        if arg and not Path(arg).is_absolute() and op in ["LASSERT"]:
            arg = str((base / arg).resolve())
        program.append((op, arg))
    return program


__all__ = ["parse", "Instruction"]
