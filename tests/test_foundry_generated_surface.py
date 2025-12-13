"""Foundry loop-closure: generated Python surface matches generated Verilog.

This is intentionally small and fast; the heavy semantics checks live elsewhere.
"""

from __future__ import annotations

import pathlib
import re

from thielecpu.generated import generated_core


def _parse_generated_verilog_opcodes(path: pathlib.Path) -> dict[str, int]:
    pattern = re.compile(
        r"localparam\s+\[7:0\]\s+OPCODE_([A-Z0-9_]+)\s*=\s*8'h([0-9a-fA-F]{2})\s*;"
    )
    out: dict[str, int] = {}
    for line in path.read_text().splitlines():
        match = pattern.search(line)
        if match:
            name, value = match.groups()
            out[name] = int(value, 16)
    if not out:
        raise AssertionError(f"no generated OPCODE_* params parsed from {path}")
    return out


def test_foundry_generated_surface_matches():
    root = pathlib.Path(__file__).resolve().parents[1]
    verilog_path = root / "thielecpu" / "hardware" / "generated_opcodes.vh"
    verilog_opcodes = _parse_generated_verilog_opcodes(verilog_path)

    # generated_core now provides a tag->mnemonic->opcode byte mapping.
    assert set(generated_core.COQ_TAG_TO_MNEMONIC) == set(generated_core.COQ_INSTRUCTION_TAGS)
    assert set(generated_core.COQ_TAG_TO_OPCODE_BYTE) == set(generated_core.COQ_INSTRUCTION_TAGS)

    # Loop-closure: header values match the generated python opcode bytes.
    for tag in generated_core.COQ_INSTRUCTION_TAGS:
        mnemonic = generated_core.COQ_TAG_TO_MNEMONIC[tag]
        assert mnemonic in verilog_opcodes
        assert verilog_opcodes[mnemonic] == generated_core.COQ_TAG_TO_OPCODE_BYTE[tag]
