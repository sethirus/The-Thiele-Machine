# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

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
        # Strip surrounding quotes if present
        if arg.startswith('"') and arg.endswith('"'):
            arg = arg[1:-1]
        # Only resolve paths for opcodes that expect file arguments
        if op in ["LASSERT", "PYEXEC"]:
            if arg and not Path(arg).is_absolute():
                arg = str((base / arg).resolve())
        elif op == "PDISCOVER":
            # PDISCOVER module_id file1 [file2 ...]
            parts = arg.split()
            if len(parts) >= 2:
                module_id = parts[0]
                file_paths = []
                for file_path in parts[1:]:
                    if file_path and not Path(file_path).is_absolute():
                        file_path = str((base / file_path).resolve())
                    file_paths.append(file_path)
                arg = f"{module_id} {' '.join(file_paths)}"
        program.append((op, arg))
    return program


__all__ = ["parse", "Instruction"]
