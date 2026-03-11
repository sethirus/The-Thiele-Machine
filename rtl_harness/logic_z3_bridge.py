#!/usr/bin/env python3
from __future__ import annotations

import argparse
from pathlib import Path

import z3

OP_LASSERT = 0x03
OP_LJOIN = 0x04


def solve(opcode: int, payload: int) -> tuple[int, int]:
    operand_a = (payload >> 8) & 0xFF
    operand_b = payload & 0xFF

    if opcode == OP_LASSERT:
        value = z3.Int("value")
        solver = z3.Solver()
        solver.add(value == operand_a)
        solver.add(value >= operand_b)
        ok = solver.check() == z3.sat
        return ((0, payload) if ok else (1, 0))

    if opcode == OP_LJOIN:
        value = z3.BitVec("value", 8)
        solver = z3.Solver()
        solver.add((value & z3.BitVecVal(operand_a, 8)) != 0)
        solver.add((value & z3.BitVecVal(operand_b, 8)) != 0)
        ok = solver.check() == z3.sat
        return ((0, (operand_a << 8) | operand_b) if ok else (1, 0))

    return 1, 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--request", required=True)
    parser.add_argument("--response", required=True)
    args = parser.parse_args()

    req_parts = Path(args.request).read_text(encoding="utf-8").strip().split()
    if len(req_parts) != 2:
        Path(args.response).write_text("1 0\n", encoding="utf-8")
        return 0

    opcode = int(req_parts[0], 0)
    payload = int(req_parts[1], 0)
    error, value = solve(opcode, payload)
    Path(args.response).write_text(f"{error} {value}\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
