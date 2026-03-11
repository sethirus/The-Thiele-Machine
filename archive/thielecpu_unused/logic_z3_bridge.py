#!/usr/bin/env python3
"""External logic bridge for Kami testbench.

Reads an opcode/payload request from a text file and writes
"<error> <value>" response for setLogicResp(valid,error,value).
"""
from __future__ import annotations

import argparse
from pathlib import Path
import z3

OP_LASSERT = 0x03
OP_LJOIN = 0x04


def solve(opcode: int, payload: int) -> tuple[int, int]:
    a = (payload >> 8) & 0xFF
    b = payload & 0xFF

    if opcode == OP_LASSERT:
        # Canonical satisfiability check: does there exist x == a with x >= b?
        x = z3.Int("x")
        s = z3.Solver()
        s.add(x == a)
        s.add(x >= b)
        ok = s.check() == z3.sat
        return (0, payload if ok else 0) if ok else (1, 0)

    if opcode == OP_LJOIN:
        # Join succeeds iff non-empty overlap exists under a bounded model.
        x = z3.BitVec("x", 8)
        s = z3.Solver()
        s.add((x & z3.BitVecVal(a, 8)) != 0)
        s.add((x & z3.BitVecVal(b, 8)) != 0)
        ok = s.check() == z3.sat
        return (0, ((a << 8) | b)) if ok else (1, 0)

    # Unknown logic op -> explicit logic error.
    return 1, 0


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--request", required=True)
    ap.add_argument("--response", required=True)
    args = ap.parse_args()

    req = Path(args.request).read_text(encoding="utf-8").strip().split()
    if len(req) != 2:
        Path(args.response).write_text("1 0\n", encoding="utf-8")
        return 0

    opcode = int(req[0], 0)
    payload = int(req[1], 0)
    err, value = solve(opcode, payload)
    Path(args.response).write_text(f"{err} {value}\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
