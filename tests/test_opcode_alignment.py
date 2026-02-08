# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.
"""Cross-check opcodes across Python ISA, RTL constants, and Coq bridge."""

from __future__ import annotations

import pathlib
import re

import pytest

from thielecpu.isa import Opcode

ROOT = pathlib.Path(__file__).resolve().parents[1]
RTL_PATH = ROOT / "thielecpu" / "hardware" / "rtl" / "thiele_cpu_unified.v"
COQ_PATH = ROOT / "coq" / "thielemachine" / "coqproofs" / "HardwareBridge.v"


def _parse_rtl_opcodes(path: pathlib.Path) -> dict[str, int]:
    pattern = re.compile(r"localparam\s+\[7:0\]\s+OPCODE_([A-Z0-9_]+)\s*=\s*8'h([0-9a-fA-F]{2});")
    opcodes: dict[str, int] = {}
    text = path.read_text()
    for line in text.splitlines():
        match = pattern.search(line)
        if match:
            name, value = match.groups()
            opcodes[name] = int(value, 16)

    # If opcodes are not inlined, follow a simple `include "..."` convention.
    if not opcodes:
        inc = re.search(r"^\s*`include\s+\"([^\"]+)\"\s*$", text, re.M)
        if inc:
            inc_path = (path.parent / inc.group(1)).resolve()
            inc_text = inc_path.read_text()
            for line in inc_text.splitlines():
                match = pattern.search(line)
                if match:
                    name, value = match.groups()
                    opcodes[name] = int(value, 16)

    if not opcodes:
        raise RuntimeError(f"no opcodes parsed from {path} (or its include)")
    return opcodes


def _parse_coq_opcodes(path: pathlib.Path) -> dict[str, int]:
    pattern = re.compile(r"Definition opcode_([A-Z0-9_]+)\s*:\s*N\s*:=\s*([0-9]+)%N")
    opcodes: dict[str, int] = {}
    for line in path.read_text().splitlines():
        match = pattern.search(line)
        if match:
            name, value = match.groups()
            opcodes[name.upper()] = int(value)
    if not opcodes:
        raise RuntimeError(f"no opcodes parsed from {path}")
    return opcodes


def test_opcode_maps_align():
    rtl = _parse_rtl_opcodes(RTL_PATH)
    coq = _parse_coq_opcodes(COQ_PATH)
    py = {name: op.value for name, op in Opcode.__members__.items()}

    # Ensure Python covers the RTL surface and matches Coq numerics.
    missing_in_python = set(rtl) - set(py)
    if missing_in_python:
        pytest.fail(f"Python ISA missing opcodes present in RTL: {sorted(missing_in_python)}")

    missing_in_coq = set(rtl) - set(coq)
    if missing_in_coq:
        pytest.fail(f"Coq bridge missing opcodes present in RTL: {sorted(missing_in_coq)}")

    for name, rtl_value in rtl.items():
        assert py[name] == rtl_value, f"Python opcode {name}={py[name]:#x} != RTL {rtl_value:#x}"
        assert coq[name] == rtl_value, f"Coq opcode {name}={coq[name]} != RTL {rtl_value}"
