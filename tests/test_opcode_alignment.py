# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.
"""Cross-check opcodes across Python cosim and Coq Kami types.

This test verifies that the Python OPCODES dict (used by the cosimulation
harness) matches the canonical opcode definitions in
coq/kami_hw/ThieleTypes.v (the Kami hardware type source of truth).

RTL is now generated via the Kami extraction chain, so there is no separate
generated_opcodes.vh file.  Opcode alignment is checked directly against
the Coq Kami definitions.
"""

from __future__ import annotations

import pathlib
import re

import pytest

ROOT = pathlib.Path(__file__).resolve().parents[1]
# Canonical opcode definitions live in the Kami hardware types
COQ_TYPES_PATH = ROOT / "coq" / "kami_hw" / "ThieleTypes.v"


def _parse_coq_kami_opcodes(path: pathlib.Path) -> dict[str, int]:
    """Parse ``Definition OP_<NAME> : word OpcodeSz := WO~b~b~...~b.`` lines.

    Returns a dict mapping opcode name (e.g. "PNEW") to its integer value.
    """
    pattern = re.compile(
        r"Definition\s+OP_([A-Z0-9_]+)\s*:\s*word\s+OpcodeSz\s*:=\s*WO((?:~[01])+)\."
    )
    opcodes: dict[str, int] = {}
    for line in path.read_text().splitlines():
        match = pattern.search(line)
        if match:
            name = match.group(1)
            bits = match.group(2).replace("~", "")
            opcodes[name] = int(bits, 2)
    if not opcodes:
        raise RuntimeError(f"no OP_* definitions parsed from {path}")
    return opcodes


def _get_python_opcodes() -> dict[str, int]:
    """Import the authoritative Python OPCODES dict from rtl_harness.cosim."""
    # Avoid hard-coding; import directly so we always test the live dict.
    import importlib
    import sys
    sys.path.insert(0, str(ROOT))
    cosim = importlib.import_module("rtl_harness.cosim")
    return dict(cosim.OPCODES)


def test_coq_kami_opcodes_parse():
    """ThieleTypes.v contains all 46 OP_* definitions."""
    coq = _parse_coq_kami_opcodes(COQ_TYPES_PATH)
    assert len(coq) >= 46, f"Expected >= 46 opcodes, found {len(coq)}: {sorted(coq)}"


def test_opcode_maps_align():
    """Verify Python cosim opcodes match Coq Kami definitions."""
    coq = _parse_coq_kami_opcodes(COQ_TYPES_PATH)
    py = _get_python_opcodes()

    # Ensure Python covers all Coq-defined opcodes
    missing_in_py = set(coq) - set(py)
    if missing_in_py:
        pytest.fail(f"Python OPCODES missing opcodes defined in Coq: {sorted(missing_in_py)}")

    missing_in_coq = set(py) - set(coq)
    if missing_in_coq:
        pytest.fail(f"Coq ThieleTypes.v missing opcodes present in Python: {sorted(missing_in_coq)}")

    # Verify numeric values match
    for name, coq_value in coq.items():
        if name in py:
            assert py[name] == coq_value, (
                f"Opcode {name}: Coq={coq_value:#04x} != Python={py[name]:#04x}"
            )
