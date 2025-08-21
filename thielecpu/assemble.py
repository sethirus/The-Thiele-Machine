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
        if not line or line.startswith("#"):
            continue
        parts = line.split(maxsplit=1)
        op = parts[0].upper()
        arg = parts[1] if len(parts) > 1 else ""
        if arg and not Path(arg).is_absolute():
            arg = str((base / arg).resolve())
        program.append((op, arg))
    return program


__all__ = ["parse", "Instruction"]
