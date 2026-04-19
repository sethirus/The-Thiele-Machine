#!/usr/bin/env python3
"""thiele-asm — Thiele Machine standalone assembler.

Assembles .asm files into binary, hex, or OCaml runner trace format.

Usage:
    python3 scripts/thiele_asm.py program.asm                        # → stdout (trace format)
    python3 scripts/thiele_asm.py program.asm -o program.bin         # → binary
    python3 scripts/thiele_asm.py program.asm -o program.hex         # → hex (one word per line)
    python3 scripts/thiele_asm.py program.asm --format trace         # → OCaml runner trace
    python3 scripts/thiele_asm.py program.asm --run                  # assemble + run via OCaml
    python3 scripts/thiele_asm.py program.asm --sim                  # assemble + run via Verilator

Syntax:
    # Comments start with #, ;, or //
    LABEL:                      # label definition (resolved in pass 2)
    LOAD_IMM r1 42 1            # register names: r0-r31, sp (=r31), zero (=r0)
    ADD r3 r1 r2 1              # dst src1 src2 cost  (also: AND, OR, SHL, SHR, MUL)
    JUMP LABEL 0                # labels resolve to instruction addresses
    HALT 0

    NOP                         # macro → LOAD_IMM r0 0 0
    MOV r1 r2                   # macro → XFER r1 r2 1

    .DATA 10 42                 # data memory initialization: mem[10] = 42
    FUEL 1000                   # max execution steps (trace format only)

ISA Reference (47 opcodes total: 40 legacy encodings + 7 categorical morph opcodes):
    Opcode   | Encoding  | Syntax
    ---------+-----------+-------
    PNEW     | 0x00      | PNEW {region} cost       — or — PNEW a b cost
    PSPLIT   | 0x01      | PSPLIT id {l} {r} cost    — or — PSPLIT a b cost
    PMERGE   | 0x02      | PMERGE a b cost
    LASSERT  | 0x03      | LASSERT a b cost
    LJOIN    | 0x04      | LJOIN a b cost
    MDLACC   | 0x05      | MDLACC a b cost
    PDISCOVER| 0x06      | PDISCOVER a b cost
    XFER     | 0x07      | XFER dst src cost
    LOAD_IMM | 0x08      | LOAD_IMM dst imm cost
    CHSH_TRIAL|0x09      | CHSH_TRIAL x y a b cost  — or — CHSH_TRIAL a b cost
    XOR_LOAD | 0x0A      | XOR_LOAD a b cost
    XOR_ADD  | 0x0B      | XOR_ADD a b cost
    XOR_SWAP | 0x0C      | XOR_SWAP a b cost
    XOR_RANK | 0x0D      | XOR_RANK a b cost
    EMIT     | 0x0E      | EMIT module bits cost — charges bits + S(cost)
    REVEAL   | 0x0F      | REVEAL tensor_idx bits cost — charges bits + S(cost)
    REVEAL_EXT|alias     | REVEAL_EXT tensor_idx bits cost — ISA-v2 tensor-extended reveal
    LOAD     | 0x11      | LOAD dst rs_addr cost     — register-indirect
    STORE    | 0x12      | STORE rs_addr src cost    — register-indirect
    ADD      | 0x13      | ADD dst src1 src2 cost    — rs1/rs2 packed into op_b
    SUB      | 0x14      | SUB dst src1 src2 cost
    JUMP     | 0x15      | JUMP target cost          — 16-bit target
    JNEZ     | 0x16      | JNEZ reg target cost      — 8-bit target
    CALL     | 0x17      | CALL target cost          — 16-bit target
    RET      | 0x18      | RET cost
    CHECKPOINT|0x19      | CHECKPOINT a b cost
    READ_PORT| 0x1A      | READ_PORT a b cost
    WRITE_PORT|0x1B      | WRITE_PORT a b cost
    HEAP_LOAD| 0x1C      | HEAP_LOAD dst rs_addr cost — register-indirect
    HEAP_STORE|0x1D      | HEAP_STORE rs_addr src cost — register-indirect
    CERTIFY  | 0x1E      | CERTIFY a b cost
    AND      | 0x1F      | AND dst src1 src2 cost    — rs1/rs2 packed into op_b
    OR       | 0x20      | OR  dst src1 src2 cost
    SHL      | 0x21      | SHL dst src1 src2 cost
    SHR      | 0x22      | SHR dst src1 src2 cost
    MUL      | 0x23      | MUL dst src1 src2 cost
    LUI      | 0x24      | LUI dst imm cost          — like LOAD_IMM
    TENSOR_SET|0x25      | TENSOR_SET mid i j value cost — per-module tensor write
    TENSOR_GET|0x26      | TENSOR_GET rd mid i j cost    — per-module tensor read
    MORPH    | 0x27      | MORPH dst src_mod dst_mod coupling_idx cost
    COMPOSE  | 0x28      | COMPOSE dst m1 m2 cost
    MORPH_ID | 0x29      | MORPH_ID dst module cost
    MORPH_DELETE|0x2A    | MORPH_DELETE morph_id cost
    MORPH_ASSERT|0x2B    | MORPH_ASSERT morph_id property cert cost
    MORPH_ASSERT_EXT|alias| MORPH_ASSERT_EXT morph_id property_hash_or_token cost
    MORPH_TENSOR|0x2C    | MORPH_TENSOR dst f g cost
    MORPH_GET|0x2D       | MORPH_GET dst morph_id selector cost
    HALT     | 0xFF      | HALT cost

Compact binary note:
    The categorical morph opcodes use a shadow hardware encoding in the
    32-bit assembler/cosim path: opcode/dst/cost are preserved, while extra
    graph arguments are truncated because the RTL shadow semantics do not
    materialize the full morphism graph. The `--run` OCaml path preserves the
    full textual arguments.
"""
from __future__ import annotations

import argparse
import re
import struct
import subprocess
import sys
from pathlib import Path
from typing import Any

OPCODES: dict[str, int] = {
    "PNEW": 0x00, "PSPLIT": 0x01, "PMERGE": 0x02, "LASSERT": 0x03,
    "LJOIN": 0x04, "MDLACC": 0x05, "PDISCOVER": 0x06, "XFER": 0x07,
    "LOAD_IMM": 0x08, "CHSH_TRIAL": 0x09, "XOR_LOAD": 0x0A,
    "XOR_ADD": 0x0B, "XOR_SWAP": 0x0C, "XOR_RANK": 0x0D,
    "EMIT": 0x0E, "REVEAL": 0x0F,
    "LOAD": 0x11, "STORE": 0x12, "ADD": 0x13, "SUB": 0x14,
    "JUMP": 0x15, "JNEZ": 0x16, "CALL": 0x17, "RET": 0x18,
    "CHECKPOINT": 0x19, "READ_PORT": 0x1A, "WRITE_PORT": 0x1B,
    "HEAP_LOAD": 0x1C, "HEAP_STORE": 0x1D, "CERTIFY": 0x1E,
    "AND": 0x1F, "OR": 0x20, "SHL": 0x21, "SHR": 0x22,
    "MUL": 0x23, "LUI": 0x24,
    "TENSOR_SET": 0x25, "TENSOR_GET": 0x26,
    "MORPH": 0x27, "COMPOSE": 0x28, "MORPH_ID": 0x29,
    "MORPH_DELETE": 0x2A, "MORPH_ASSERT": 0x2B,
    "MORPH_TENSOR": 0x2C, "MORPH_GET": 0x2D,
    "HALT": 0xFF,
}

ISA_V2_VERSION = 0x02
FMT_LEGACY = 0x00
FMT_TENSOR_EXT = 0x02
FMT_MORPH_INLINE = 0x03
FMT_CERT_INLINE = 0x05

REGISTER_NAMES: dict[str, int] = {
    "zero": 0, "sp": 31,
    **{f"r{i}": i for i in range(32)},
}

MACROS: dict[str, str] = {
    "NOP": "LOAD_IMM r0 0 0",
}


def _parse_int(s: str, labels: dict[str, int] | None = None) -> int:
    """Parse an integer literal or label reference."""
    s = s.strip()
    if labels and s in labels:
        return labels[s]
    if s in REGISTER_NAMES:
        return REGISTER_NAMES[s]
    return int(s, 0)


def _ascii_checksum(text: str) -> int:
    return sum(ord(ch) for ch in text) & 0xFFFFFFFF


def _parse_inline_checksum(s: str, labels: dict[str, int] | None = None) -> int:
    token = s.strip()
    if len(token) >= 2 and token[0] == token[-1] and token[0] in {'"', "'"}:
        token = token[1:-1]
    try:
        return _parse_int(token, labels)
    except ValueError:
        return _ascii_checksum(token)


def _encode(
    opcode: int,
    op_a: int = 0,
    op_b: int = 0,
    cost: int = 0,
    *,
    isa_version: int = ISA_V2_VERSION,
    format_id: int = FMT_LEGACY,
    flags: int = 0,
    ext0: int = 0,
    ext1: int = 0,
) -> int:
    low32 = ((opcode & 0xFF) << 24) | ((op_a & 0xFF) << 16) | ((op_b & 0xFF) << 8) | (cost & 0xFF)
    return (
        ((isa_version & 0xFF) << 120)
        | ((format_id & 0xFF) << 112)
        | ((flags & 0xFFFF) << 96)
        | ((ext1 & 0xFFFFFFFF) << 64)
        | ((ext0 & 0xFFFFFFFF) << 32)
        | low32
    )


class AssemblerError(Exception):
    def __init__(self, line_num: int, message: str):
        super().__init__(f"Line {line_num}: {message}")
        self.line_num = line_num


def assemble(source: str) -> tuple[list[int], dict[int, int], dict[str, Any]]:
    """Two-pass assembler. Returns (instructions, data_memory, metadata).

    Pass 1: collect labels, count instructions, expand macros
    Pass 2: resolve labels, encode instructions
    """
    lines = source.splitlines()
    metadata: dict[str, Any] = {"fuel": 256}
    data_memory: dict[int, int] = {}

    # ---- Pass 1: collect labels, expand macros, count instructions ----
    labels: dict[str, int] = {}
    processed: list[tuple[int, str]] = []  # (original_line_num, cleaned_line)
    pc = 0

    for line_num, raw_line in enumerate(lines, 1):
        line = raw_line.strip()

        # Strip comments
        for comment_char in ("#", ";", "//"):
            idx = line.find(comment_char)
            if idx >= 0:
                line = line[:idx].strip()

        if not line:
            continue

        # Label definition
        if line.endswith(":"):
            label = line[:-1].strip()
            if label in labels:
                raise AssemblerError(line_num, f"Duplicate label: {label}")
            labels[label] = pc
            continue

        # Directives (don't count as instructions)
        upper = line.split()[0].upper()
        if upper == "FUEL":
            metadata["fuel"] = int(line.split()[1], 0)
            continue
        if upper in (".DATA", "INIT_MEM"):
            parts = line.split()
            addr = int(parts[1], 0)
            val = int(parts[2], 0)
            data_memory[addr] = val
            continue
        if upper.startswith("INIT_"):
            processed.append((line_num, line))
            continue

        # Macro expansion
        if upper == "MOV":
            parts = line.split()
            if len(parts) < 3:
                raise AssemblerError(line_num, "MOV requires: MOV dst src")
            line = f"XFER {parts[1]} {parts[2]} 1"
        elif upper in MACROS:
            line = MACROS[upper]

        processed.append((line_num, line))
        pc += 1

    # ---- Pass 2: encode instructions ----
    instructions: list[int] = []
    init_directives: list[str] = []

    for line_num, line in processed:
        parts = line.split(maxsplit=1)
        op = parts[0].upper()
        arg = parts[1] if len(parts) > 1 else ""

        # Pass through INIT directives
        if op.startswith("INIT_"):
            init_directives.append(line)
            continue

        if op == "REVEAL_EXT":
            reveal_parts = arg.split()
            tensor_idx = _parse_int(reveal_parts[0], labels) if reveal_parts else 0
            bits = _parse_int(reveal_parts[1], labels) if len(reveal_parts) > 1 else 0
            cost = _parse_int(reveal_parts[2], labels) if len(reveal_parts) > 2 else 0
            instructions.append(
                _encode(
                    OPCODES["REVEAL"],
                    0,
                    bits,
                    cost,
                    format_id=FMT_TENSOR_EXT,
                    ext0=tensor_idx,
                )
            )
            continue

        if op == "MORPH_EXT":
            morph = arg.split()
            dst = _parse_int(morph[0], labels) if morph else 0
            src_mod = _parse_int(morph[1], labels) if len(morph) > 1 else 0
            dst_mod = _parse_int(morph[2], labels) if len(morph) > 2 else 0
            coupling_desc = _parse_int(morph[3], labels) if len(morph) > 3 else 0
            cost = _parse_int(morph[4], labels) if len(morph) > 4 else 0
            ext0 = (dst_mod & 0x3F) | ((coupling_desc & 0x3F) << 6)
            instructions.append(
                _encode(
                    OPCODES["MORPH"],
                    dst,
                    src_mod,
                    cost,
                    format_id=FMT_MORPH_INLINE,
                    flags=0x0004,
                    ext0=ext0,
                )
            )
            continue

        if op == "COMPOSE_EXT":
            comp = arg.split()
            dst = _parse_int(comp[0], labels) if comp else 0
            m1 = _parse_int(comp[1], labels) if len(comp) > 1 else 0
            m2 = _parse_int(comp[2], labels) if len(comp) > 2 else 0
            cost = _parse_int(comp[3], labels) if len(comp) > 3 else 0
            instructions.append(
                _encode(
                    OPCODES["COMPOSE"],
                    dst,
                    m1,
                    cost,
                    format_id=FMT_MORPH_INLINE,
                    flags=0x0004,
                    ext0=m2,
                )
            )
            continue

        if op == "MORPH_ID_EXT":
            morph_id = arg.split()
            dst = _parse_int(morph_id[0], labels) if morph_id else 0
            module = _parse_int(morph_id[1], labels) if len(morph_id) > 1 else 0
            cost = _parse_int(morph_id[2], labels) if len(morph_id) > 2 else 0
            instructions.append(
                _encode(
                    OPCODES["MORPH_ID"],
                    dst,
                    module,
                    cost,
                    format_id=FMT_MORPH_INLINE,
                    flags=0x0004,
                )
            )
            continue

        if op == "MORPH_DELETE_EXT":
            morph_delete = arg.split()
            morph_id = _parse_int(morph_delete[0], labels) if morph_delete else 0
            cost = _parse_int(morph_delete[1], labels) if len(morph_delete) > 1 else 0
            instructions.append(
                _encode(
                    OPCODES["MORPH_DELETE"],
                    morph_id,
                    0,
                    cost,
                    format_id=FMT_MORPH_INLINE,
                    flags=0x0004,
                )
            )
            continue

        if op == "MORPH_GET_EXT":
            morph_get = arg.split()
            dst = _parse_int(morph_get[0], labels) if morph_get else 0
            morph_id = _parse_int(morph_get[1], labels) if len(morph_get) > 1 else 0
            selector = _parse_int(morph_get[2], labels) if len(morph_get) > 2 else 0
            cost = _parse_int(morph_get[3], labels) if len(morph_get) > 3 else 0
            instructions.append(
                _encode(
                    OPCODES["MORPH_GET"],
                    dst,
                    morph_id,
                    cost,
                    format_id=FMT_MORPH_INLINE,
                    flags=0x0004,
                    ext0=selector,
                )
            )
            continue

        if op == "MORPH_ASSERT_EXT":
            morph_assert = arg.split()
            morph_id = _parse_int(morph_assert[0], labels) if morph_assert else 0
            property_checksum = _parse_inline_checksum(morph_assert[1], labels) if len(morph_assert) > 1 else 0
            cost = _parse_int(morph_assert[2], labels) if len(morph_assert) > 2 else 0
            instructions.append(
                _encode(
                    OPCODES["MORPH_ASSERT"],
                    morph_id,
                    0,
                    cost,
                    format_id=FMT_CERT_INLINE,
                    flags=0x0004,
                    ext0=property_checksum,
                )
            )
            continue

        if op == "MORPH_TENSOR_EXT":
            # MORPH_TENSOR_EXT dst f_id g_id cost
            # FMT_MORPH_INLINE: f_id in op_b (low lane), g_id in ext0[5:0]
            morph_t = arg.split()
            dst = _parse_int(morph_t[0], labels) if morph_t else 0
            f_id = _parse_int(morph_t[1], labels) if len(morph_t) > 1 else 0
            g_id = _parse_int(morph_t[2], labels) if len(morph_t) > 2 else 0
            cost = _parse_int(morph_t[3], labels) if len(morph_t) > 3 else 0
            instructions.append(
                _encode(
                    OPCODES["MORPH_TENSOR"],
                    dst,
                    f_id,
                    cost,
                    format_id=FMT_MORPH_INLINE,
                    flags=0x0004,
                    ext0=g_id & 0x3F,
                )
            )
            continue

        if op not in OPCODES:
            raise AssemblerError(line_num, f"Unknown opcode: {op}")

        opcode = OPCODES[op]

        try:
            if op == "HALT":
                h_parts = arg.split()
                cost = _parse_int(h_parts[0], labels) if h_parts else 0
                instructions.append(_encode(opcode, 0, 0, cost))

            elif op == "RET":
                r_parts = arg.split()
                cost = _parse_int(r_parts[0], labels) if r_parts else 0
                instructions.append(_encode(opcode, 0, 0, cost))

            elif op in ("JUMP", "CALL"):
                jc = arg.split()
                target = _parse_int(jc[0], labels) if jc else 0
                cost = _parse_int(jc[1], labels) if len(jc) > 1 else 0
                instructions.append(_encode(opcode, (target >> 8) & 0xFF, target & 0xFF, cost))

            elif op == "JNEZ":
                jn = arg.split()
                reg = _parse_int(jn[0], labels) if jn else 0
                target = _parse_int(jn[1], labels) if len(jn) > 1 else 0
                cost = _parse_int(jn[2], labels) if len(jn) > 2 else 0
                instructions.append(_encode(opcode, reg, target, cost))

            elif op in ("ADD", "SUB", "AND", "OR", "SHL", "SHR", "MUL"):
                alu = arg.split()
                dst = _parse_int(alu[0], labels)
                rs1 = _parse_int(alu[1], labels) if len(alu) > 1 else 0
                rs2 = _parse_int(alu[2], labels) if len(alu) > 2 else 0
                cost = _parse_int(alu[3], labels) if len(alu) > 3 else 0
                packed = ((rs1 & 0xF) << 4) | (rs2 & 0xF)
                instructions.append(_encode(opcode, dst, packed, cost))

            elif op == "CHSH_TRIAL":
                ct = arg.split()
                if len(ct) >= 4:
                    x = _parse_int(ct[0], labels)
                    y = _parse_int(ct[1], labels)
                    a = _parse_int(ct[2], labels)
                    b = _parse_int(ct[3], labels)
                    cost = _parse_int(ct[4], labels) if len(ct) > 4 else 0
                    op_a = ((x & 1) << 1) | (y & 1)
                    op_b = ((a & 1) << 1) | (b & 1)
                    instructions.append(_encode(opcode, op_a, op_b, cost))
                else:
                    op_a = _parse_int(ct[0], labels) if ct else 0
                    op_b = _parse_int(ct[1], labels) if len(ct) > 1 else 0
                    cost = _parse_int(ct[2], labels) if len(ct) > 2 else 0
                    instructions.append(_encode(opcode, op_a, op_b, cost))

            elif op == "PNEW":
                match = re.match(r"\{([^}]*)\}\s+(\S+)", arg)
                if match:
                    region = [_parse_int(t, labels) for t in match.group(1).split(",") if t.strip()]
                    cost = _parse_int(match.group(2), labels)
                    instructions.append(_encode(opcode, region[0] if region else 0, len(region), cost))
                else:
                    pn = arg.split()
                    instructions.append(_encode(opcode,
                        _parse_int(pn[0], labels), _parse_int(pn[1], labels),
                        _parse_int(pn[2], labels) if len(pn) > 2 else 0))

            elif op == "PSPLIT":
                match = re.match(r"(\S+)\s+\{[^}]*\}\s+\{[^}]*\}\s+(\S+)", arg)
                if match:
                    instructions.append(_encode(opcode,
                        _parse_int(match.group(1), labels), 0,
                        _parse_int(match.group(2), labels)))
                else:
                    ps = arg.split()
                    instructions.append(_encode(opcode,
                        _parse_int(ps[0], labels),
                        _parse_int(ps[1], labels) if len(ps) > 1 else 0,
                        _parse_int(ps[2], labels) if len(ps) > 2 else 0))

            elif op in ("STORE", "HEAP_STORE"):
                # Register-indirect: STORE rs_addr src cost
                # Encoding: op_a=rs_addr_reg, op_b=src_reg, cost
                st = arg.split()
                rs_addr = _parse_int(st[0], labels) if st else 0
                src = _parse_int(st[1], labels) if len(st) > 1 else 0
                cost = _parse_int(st[2], labels) if len(st) > 2 else 0
                instructions.append(_encode(opcode, rs_addr, src, cost))

            elif op == "TENSOR_SET":
                # TENSOR_SET mid i j value cost
                # Binary encoding: op_a = (mid & 0xF) << 4 | (i & 0x3) << 2 | (j & 0x3)
                #                  op_b = value & 0xFF, cost = cost & 0xFF
                ts = arg.split()
                mid = _parse_int(ts[0], labels) if ts else 0
                ti = _parse_int(ts[1], labels) if len(ts) > 1 else 0
                tj = _parse_int(ts[2], labels) if len(ts) > 2 else 0
                val = _parse_int(ts[3], labels) if len(ts) > 3 else 0
                cost = _parse_int(ts[4], labels) if len(ts) > 4 else 0
                op_a = ((mid & 0xF) << 4) | ((ti & 0x3) << 2) | (tj & 0x3)
                instructions.append(_encode(opcode, op_a, val & 0xFF, cost))

            elif op == "TENSOR_GET":
                # TENSOR_GET rd mid i j cost
                # Binary encoding: op_a = rd & 0x1F
                #                  op_b = (mid & 0xF) << 4 | (i & 0x3) << 2 | (j & 0x3)
                #                  cost = cost & 0xFF
                tg = arg.split()
                rd = _parse_int(tg[0], labels) if tg else 0
                mid = _parse_int(tg[1], labels) if len(tg) > 1 else 0
                ti = _parse_int(tg[2], labels) if len(tg) > 2 else 0
                tj = _parse_int(tg[3], labels) if len(tg) > 3 else 0
                cost = _parse_int(tg[4], labels) if len(tg) > 4 else 0
                op_b = ((mid & 0xF) << 4) | ((ti & 0x3) << 2) | (tj & 0x3)
                instructions.append(_encode(opcode, rd & 0x1F, op_b, cost))

            elif op == "MORPH":
                morph = arg.split()
                dst = _parse_int(morph[0], labels) if morph else 0
                src_mod = _parse_int(morph[1], labels) if len(morph) > 1 else 0
                cost = _parse_int(morph[-1], labels) if len(morph) > 1 else 0
                instructions.append(_encode(opcode, dst, src_mod, cost))

            elif op == "COMPOSE":
                comp = arg.split()
                dst = _parse_int(comp[0], labels) if comp else 0
                m1 = _parse_int(comp[1], labels) if len(comp) > 1 else 0
                cost = _parse_int(comp[-1], labels) if len(comp) > 1 else 0
                instructions.append(_encode(opcode, dst, m1, cost))

            elif op == "MORPH_ID":
                morph_id = arg.split()
                dst = _parse_int(morph_id[0], labels) if morph_id else 0
                module = _parse_int(morph_id[1], labels) if len(morph_id) > 1 else 0
                cost = _parse_int(morph_id[-1], labels) if len(morph_id) > 1 else 0
                instructions.append(_encode(opcode, dst, module, cost))

            elif op == "MORPH_DELETE":
                morph_delete = arg.split()
                morph_id = _parse_int(morph_delete[0], labels) if morph_delete else 0
                cost = _parse_int(morph_delete[-1], labels) if len(morph_delete) > 1 else 0
                instructions.append(_encode(opcode, morph_id, 0, cost))

            elif op == "MORPH_ASSERT":
                morph_assert = arg.split()
                morph_id = _parse_int(morph_assert[0], labels) if morph_assert else 0
                cost = _parse_int(morph_assert[-1], labels) if len(morph_assert) > 1 else 0
                instructions.append(_encode(opcode, morph_id, 0, cost))

            elif op == "MORPH_TENSOR":
                morph_tensor = arg.split()
                dst = _parse_int(morph_tensor[0], labels) if morph_tensor else 0
                f_id = _parse_int(morph_tensor[1], labels) if len(morph_tensor) > 1 else 0
                cost = _parse_int(morph_tensor[-1], labels) if len(morph_tensor) > 1 else 0
                instructions.append(_encode(opcode, dst, f_id, cost))

            elif op == "MORPH_GET":
                morph_get = arg.split()
                dst = _parse_int(morph_get[0], labels) if morph_get else 0
                morph_id = _parse_int(morph_get[1], labels) if len(morph_get) > 1 else 0
                cost = _parse_int(morph_get[-1], labels) if len(morph_get) > 1 else 0
                instructions.append(_encode(opcode, dst, morph_id, cost))

            else:
                # Generic 3-operand: op_a op_b cost
                g = arg.split()
                op_a = _parse_int(g[0], labels) if g else 0
                op_b = _parse_int(g[1], labels) if len(g) > 1 else 0
                cost = _parse_int(g[2], labels) if len(g) > 2 else 0
                instructions.append(_encode(opcode, op_a, op_b, cost))

        except (ValueError, IndexError) as e:
            raise AssemblerError(line_num, f"Bad operands for {op}: {arg} ({e})") from e

    metadata["init_directives"] = init_directives
    return instructions, data_memory, metadata


def to_binary(instructions: list[int]) -> bytes:
    """Pack instructions as little-endian 128-bit words."""
    return b"".join(w.to_bytes(16, "little", signed=False) for w in instructions)


def to_hex(instructions: list[int]) -> str:
    """One 32-char uppercase hex word per line."""
    return "\n".join(f"{w:032X}" for w in instructions) + "\n"


def to_trace(instructions: list[int], data_memory: dict[int, int],
             metadata: dict[str, Any]) -> str:
    """OCaml runner trace format (text, one instruction per line)."""
    lines = [f"FUEL {metadata.get('fuel', 256)}"]

    for directive in metadata.get("init_directives", []):
        lines.append(directive)

    for addr, val in sorted(data_memory.items()):
        lines.append(f"INIT_MEM {addr} {val}")

    opcode_by_num = {v: k for k, v in OPCODES.items()}

    for word in instructions:
        format_id = (word >> 112) & 0xFF
        ext0 = (word >> 32) & 0xFFFFFFFF
        opc = (word >> 24) & 0xFF
        op_a = (word >> 16) & 0xFF
        op_b = (word >> 8) & 0xFF
        cost = word & 0xFF
        name = opcode_by_num.get(opc, f"UNKNOWN_{opc:#x}")

        if name in ("JUMP", "CALL"):
            target = (op_a << 8) | op_b
            lines.append(f"{name} {target} {cost}")
        elif name in ("ADD", "SUB", "AND", "OR", "SHL", "SHR", "MUL"):
            rs1 = (op_b >> 4) & 0xF
            rs2 = op_b & 0xF
            lines.append(f"{name} {op_a} {rs1} {rs2} {cost}")
        elif name == "HALT":
            lines.append(f"HALT {cost}")
        elif name == "RET":
            lines.append(f"RET {cost}")
        elif name == "TENSOR_SET":
            mid = (op_a >> 4) & 0xF
            ti = (op_a >> 2) & 0x3
            tj = op_a & 0x3
            lines.append(f"TENSOR_SET {mid} {ti} {tj} {op_b} {cost}")
        elif name == "TENSOR_GET":
            rd = op_a & 0x1F
            mid = (op_b >> 4) & 0xF
            ti = (op_b >> 2) & 0x3
            tj = op_b & 0x3
            lines.append(f"TENSOR_GET {rd} {mid} {ti} {tj} {cost}")
        elif name == "MORPH" and format_id == FMT_MORPH_INLINE:
            dst_mod = ext0 & 0x3F
            coupling_desc = (ext0 >> 6) & 0x3F
            lines.append(f"MORPH_EXT {op_a} {op_b} {dst_mod} {coupling_desc} {cost}")
        elif name == "MORPH":
            lines.append(f"MORPH {op_a} {op_b} 0 0 {cost}")
        elif name == "COMPOSE" and format_id == FMT_MORPH_INLINE:
            lines.append(f"COMPOSE_EXT {op_a} {op_b} {ext0 & 0x3F} {cost}")
        elif name == "COMPOSE":
            lines.append(f"COMPOSE {op_a} {op_b} 0 {cost}")
        elif name == "MORPH_ID" and format_id == FMT_MORPH_INLINE:
            lines.append(f"MORPH_ID_EXT {op_a} {op_b} {cost}")
        elif name == "MORPH_ID":
            lines.append(f"MORPH_ID {op_a} {op_b} {cost}")
        elif name == "MORPH_DELETE" and format_id == FMT_MORPH_INLINE:
            lines.append(f"MORPH_DELETE_EXT {op_a} {cost}")
        elif name == "MORPH_DELETE":
            lines.append(f"MORPH_DELETE {op_a} {cost}")
        elif name == "MORPH_ASSERT" and format_id == FMT_CERT_INLINE:
            lines.append(f"MORPH_ASSERT_EXT {op_a} {ext0} {cost}")
        elif name == "MORPH_ASSERT":
            lines.append(f"MORPH_ASSERT {op_a} shadow shadow {cost}")
        elif name == "MORPH_TENSOR" and format_id == FMT_MORPH_INLINE:
            lines.append(f"MORPH_TENSOR_EXT {op_a} {op_b} {ext0 & 0x3F} {cost}")
        elif name == "MORPH_TENSOR":
            lines.append(f"MORPH_TENSOR {op_a} {op_b} 0 {cost}")
        elif name == "MORPH_GET" and format_id == FMT_MORPH_INLINE:
            lines.append(f"MORPH_GET_EXT {op_a} {op_b} {ext0 & 0x3} {cost}")
        elif name == "MORPH_GET":
            lines.append(f"MORPH_GET {op_a} {op_b} 0 {cost}")
        elif name == "REVEAL" and format_id == FMT_TENSOR_EXT:
            lines.append(f"REVEAL_EXT {ext0 & 0xF} {op_b} {cost}")
        else:
            lines.append(f"{name} {op_a} {op_b} {cost}")

    return "\n".join(lines) + "\n"


def to_cosim(instructions: list[int], data_memory: dict[int, int],
             metadata: dict[str, Any]) -> str:
    """Cosim text format (same as trace but with INIT_* directives)."""
    return to_trace(instructions, data_memory, metadata)


def main():
    parser = argparse.ArgumentParser(
        description="Thiele Machine assembler",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("source", help="Assembly source file (.asm)")
    parser.add_argument("-o", "--output", help="Output file (default: stdout)")
    parser.add_argument("--format", choices=["binary", "hex", "trace", "cosim"],
                        default=None,
                        help="Output format (auto-detected from file extension)")
    parser.add_argument("--run", action="store_true",
                        help="Assemble and run via OCaml extracted runner")
    parser.add_argument("--sim", action="store_true",
                        help="Assemble and run via Verilator RTL cosim")
    parser.add_argument("--fuel", type=int, default=None,
                        help="Override max execution steps")
    args = parser.parse_args()

    source_path = Path(args.source)
    if not source_path.exists():
        print(f"ERROR: File not found: {source_path}", file=sys.stderr)
        sys.exit(1)

    source = source_path.read_text()

    try:
        instructions, data_memory, metadata = assemble(source)
    except AssemblerError as e:
        print(f"ERROR: {e}", file=sys.stderr)
        sys.exit(1)

    if args.fuel is not None:
        metadata["fuel"] = args.fuel

    print(f"Assembled {len(instructions)} instructions", file=sys.stderr)

    if args.run:
        _run_ocaml(source, metadata)
        return

    if args.sim:
        _run_cosim(instructions, data_memory, metadata, source_path)
        return

    # Determine output format
    fmt = args.format
    if fmt is None and args.output:
        ext = Path(args.output).suffix.lower()
        fmt = {"bin": "binary", ".bin": "binary", ".hex": "hex",
               ".txt": "trace", ".trace": "trace"}.get(ext, "trace")
    if fmt is None:
        fmt = "trace"

    if fmt == "binary":
        output = to_binary(instructions)
    elif fmt == "hex":
        output = to_hex(instructions)
    else:
        output = to_trace(instructions, data_memory, metadata)

    if args.output:
        if isinstance(output, bytes):
            Path(args.output).write_bytes(output)
        else:
            Path(args.output).write_text(output)
        print(f"Wrote {args.output}", file=sys.stderr)
    else:
        if isinstance(output, bytes):
            sys.stdout.buffer.write(output)
        else:
            sys.stdout.write(output)


def _preprocess_source(source_text: str) -> tuple[list[str], dict[str, int]]:
    """Two-pass preprocess: collect labels, strip comments, expand macros,
    resolve register names and label references.

    Returns (cleaned_lines, labels) where cleaned_lines are ready for
    the OCaml runner (preserving brace syntax for PNEW/PSPLIT).
    """
    raw_lines: list[tuple[str, str]] = []  # (original_cleaned, upper_opcode)
    labels: dict[str, int] = {}
    pc = 0

    # Pass 1: collect labels, count instructions
    for raw_line in source_text.splitlines():
        line = raw_line.strip()
        for c in ("#", ";", "//"):
            idx = line.find(c)
            if idx >= 0:
                line = line[:idx].strip()
        if not line:
            continue
        if line.endswith(":"):
            labels[line[:-1].strip()] = pc
            continue
        upper = line.split()[0].upper()
        if upper == "FUEL":
            continue
        if upper in (".DATA", "INIT_MEM"):
            raw_lines.append((line, upper))
            continue
        if upper.startswith("INIT_"):
            raw_lines.append((line, upper))
            continue
        raw_lines.append((line, upper))
        pc += 1

    # Pass 2: resolve register names, label refs, expand macros
    out: list[str] = []
    for line, upper in raw_lines:
        if upper == "NOP":
            out.append("LOAD_IMM 0 0 0")
            continue
        if upper == "MOV":
            parts = line.split()
            dst = REGISTER_NAMES.get(parts[1], parts[1])
            src = REGISTER_NAMES.get(parts[2], parts[2])
            out.append(f"XFER {dst} {src} 1")
            continue
        # For PNEW/PSPLIT with brace syntax, only resolve tokens outside braces
        if "{" in line:
            # Split into segments: before-brace, inside-brace, after-brace
            # Resolve only outside brace segments
            result_parts = []
            i = 0
            text = line
            first_token = True
            while i < len(text):
                if text[i] == "{":
                    end = text.index("}", i)
                    result_parts.append(text[i:end + 1])
                    i = end + 1
                    first_token = False
                elif text[i] in (" ", "\t"):
                    result_parts.append(text[i])
                    i += 1
                else:
                    # Read a token
                    j = i
                    while j < len(text) and text[j] not in (" ", "\t", "{", "}"):
                        j += 1
                    token = text[i:j]
                    if first_token:
                        result_parts.append(token)  # opcode, keep as-is
                        first_token = False
                    elif token in REGISTER_NAMES:
                        result_parts.append(str(REGISTER_NAMES[token]))
                    elif token in labels:
                        result_parts.append(str(labels[token]))
                    else:
                        result_parts.append(token)
                    i = j
            out.append("".join(result_parts))
            continue

        # Normal instruction: resolve register names and label refs
        parts = line.split()
        resolved = [parts[0]]  # keep opcode as-is
        for p in parts[1:]:
            if p in REGISTER_NAMES:
                resolved.append(str(REGISTER_NAMES[p]))
            elif p in labels:
                resolved.append(str(labels[p]))
            else:
                resolved.append(p)
        out.append(" ".join(resolved))

    return out, labels


def _run_ocaml(source_text, metadata):
    """Run source through OCaml extracted runner.

    We preprocess the original source (strip labels, resolve register names
    and label references, expand macros) while preserving brace syntax for
    PNEW/PSPLIT, because the OCaml runner expects that text format.
    """
    import tempfile
    root = Path(__file__).resolve().parent.parent
    runner = root / "build" / "extracted_vm_runner"
    if not runner.exists():
        print(f"ERROR: OCaml runner not found: {runner}", file=sys.stderr)
        sys.exit(1)

    fuel = metadata.get("fuel", 256)
    lines, _ = _preprocess_source(source_text)
    out_lines = [f"FUEL {fuel}"] + lines
    trace = "\n".join(out_lines) + "\n"

    with tempfile.NamedTemporaryFile(mode="w", suffix=".txt", delete=False) as f:
        f.write(trace)
        trace_path = f.name

    try:
        result = subprocess.run(
            [str(runner), trace_path],
            capture_output=True, text=True, timeout=30,
        )
        if result.stdout.strip():
            import json
            state = json.loads(result.stdout.strip())
            err = state.get("err", False)
            halted = result.returncode == 0 and not err
            print(f"PC={state.get('pc', '?')}  mu={state.get('mu', '?')}  "
                  f"halted={halted}  err={err}")
            for i in range(32):
                val = state.get("regs", [0] * 32)[i]
                if val != 0:
                    print(f"  r{i} = {val}")
        if result.returncode != 0:
            print(f"Exit code: {result.returncode}", file=sys.stderr)
            if result.stderr.strip():
                print(result.stderr.strip(), file=sys.stderr)
    finally:
        Path(trace_path).unlink(missing_ok=True)


def _run_cosim(instructions, data_memory, metadata, source_path):
    """Assemble and run via Verilator RTL cosim."""
    root = Path(__file__).resolve().parent.parent
    sys.path.insert(0, str(root))

    # Use the binary-encoded trace format for cosim (numeric operands)
    trace = to_cosim(instructions, data_memory, metadata)

    try:
        from rtl_harness.cosim import run_verilog
        result = run_verilog(trace)
        if result:
            # status: 0=running, 2=halted, 3=err
            status = result.get("status", 0)
            halted = status == 2
            err = result.get("err", False) or status == 3
            print(f"PC={result.get('pc', '?')}  mu={result.get('mu', '?')}  "
                  f"halted={halted}  err={err}")
            regs = result.get("regs", [])
            for i, val in enumerate(regs):
                if val != 0:
                    print(f"  r{i} = {val}")
            mem = result.get("mem", [])
            for i, val in enumerate(mem):
                if val != 0:
                    print(f"  mem[{i}] = {val}")
        else:
            print("No result from cosim", file=sys.stderr)
    except ImportError:
        print("ERROR: rtl_harness.cosim not importable", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
