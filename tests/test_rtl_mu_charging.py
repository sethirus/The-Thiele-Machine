"""Static checks: RTL charges μ for every opcode.

This is a lightweight safety net to prevent regressions where an opcode executes
but fails to contribute to μ in evidence-strict mode.

We treat these as "μ-charged" patterns:
- Direct per-instruction charge: mu_accumulator <= mu_accumulator + {24'h0, operand_cost}
- ALU-charged opcodes: MDLACC / PDISCOVER / ORACLE_HALTS (μ updated via μ-ALU paths)

This test does not prove the *amount* is correct; it proves every opcode has a
charging pathway in RTL.
"""

from __future__ import annotations

import pathlib
import re


ROOT = pathlib.Path(__file__).resolve().parents[1]
RTL_PATH = ROOT / "thielecpu" / "hardware" / "rtl" / "thiele_cpu.v"
OPCODES_HDR = ROOT / "thielecpu" / "hardware" / "rtl" / "generated_opcodes.vh"


def _strip_line_comment(line: str) -> str:
    # Remove // comments (good enough for this file’s style)
    return line.split("//", 1)[0]


def _rtl_case_blocks(text: str) -> dict[str, str]:
    """Return map opcode_name -> case block text (including begin/end lines)."""

    lines = text.splitlines()
    blocks: dict[str, str] = {}

    case_start = re.compile(r"^\s*OPCODE_([A-Z0-9_]+):\s*begin\s*$")

    i = 0
    while i < len(lines):
        m = case_start.match(lines[i])
        if not m:
            i += 1
            continue

        name = m.group(1)
        start = i
        depth = 0
        j = i
        while j < len(lines):
            code = _strip_line_comment(lines[j])
            # Count begin/end tokens to find matching end.
            depth += len(re.findall(r"\bbegin\b", code))
            depth -= len(re.findall(r"\bend\b", code))
            j += 1
            if depth == 0:
                break

        blocks[name] = "\n".join(lines[start:j])
        i = j

    return blocks


def _opcode_names_from_header(text: str) -> set[str]:
    # Matches: localparam [7:0] OPCODE_FOO = 8'h..;
    names = set(re.findall(r"\bOPCODE_([A-Z0-9_]+)\b", text))
    if not names:
        raise AssertionError("failed to parse any OPCODE_* names from generated header")
    return names


def test_rtl_every_opcode_charges_mu() -> None:
    hdr = OPCODES_HDR.read_text(encoding="utf-8")
    rtl = RTL_PATH.read_text(encoding="utf-8")

    opcode_names = _opcode_names_from_header(hdr)
    blocks = _rtl_case_blocks(rtl)

    # Ensure every opcode has a case arm.
    missing_blocks = sorted(opcode_names - set(blocks))
    assert not missing_blocks, f"Missing opcode cases in RTL: {missing_blocks}"

    # Match any direct mu_accumulator update (e.g. simple or composite additions)
    # Examples matched:
    #   mu_accumulator <= mu_accumulator + {24'h0, operand_cost};
    #   mu_accumulator <= mu_accumulator + {24'h0, operand_cost} + {16'h0, operand_a, 8'h0};
    alu_charged = {
        "MDLACC": "execute_mdlacc(",
        "PDISCOVER": "execute_pdiscover(",
        "ORACLE_HALTS": "execute_oracle_halts(",
    }

    uncharged: list[str] = []
    for name in sorted(opcode_names):
        block = blocks[name]
        # Any mu_accumulator update that adds to the accumulator counts as charging
        if re.search(r"mu_accumulator\s*<=\s*mu_accumulator\s*\+", block):
            continue
        if name in alu_charged and alu_charged[name] in block:
            continue
        uncharged.append(name)

    assert not uncharged, f"Opcodes without an obvious μ-charging path in RTL: {uncharged}"
