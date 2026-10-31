#!/usr/bin/env python3
"""Summarise the measurements written by tests/test_cmp_compiler.py
(THIELE_CMP_REPORT=file.json): per program the source operations, counter
machine steps and host steps, and the slowdown of each stage.

  source operations --(compile to flat, counter machine)--> counter machine steps
  counter machine steps --(DEC through register 0)--> host steps

Usage: scripts/cmp_report.py report.json [more.json ...]
"""

from __future__ import annotations

import json
import math
import sys
from collections import defaultdict


def main(paths):
    rows = []
    for p in paths:
        rows += json.loads(open(p, encoding="utf-8").read())
    prog = [r for r in rows if "source_ops" in r]
    by = defaultdict(list)
    for r in prog:
        by[r["name"].rstrip("0123456789") if r["name"].startswith("fuzz") else r["name"]].append(r)
    print("%-14s %5s %10s %12s %12s %9s %9s %10s" % ("program", "runs", "src ops", "mm steps", "host steps", "mm/src", "host/mm", "host/src"))
    for name in sorted(by):
        rs = by[name]
        ops = sum(r["source_ops"] for r in rs)
        host = sum(r["host_steps"] for r in rs)
        mm = sum(r["mm_steps"] for r in rs if r.get("mm_steps"))
        have_mm = all(r.get("mm_steps") for r in rs)
        print("%-14s %5d %10d %12s %12d %9s %9s %10.1f" % (
            name, len(rs), ops, mm if have_mm else "-", host,
            ("%.1f" % (mm / ops)) if have_mm and ops else "-", ("%.2f" % (host / mm)) if have_mm and mm else "-",
            host / ops if ops else float("nan")))
    ratios = [r["host_steps"] / r["source_ops"] for r in prog if r["source_ops"] > 0]
    if ratios:
        print("host steps per source operation over %d runs: min %.1f, geometric mean %.1f, max %.1f" % (
            len(ratios), min(ratios), math.exp(sum(math.log(x) for x in ratios) / len(ratios)), max(ratios)))
    comp = [(r["t_compile"], r["host_len"]) for r in prog if r.get("t_compile") is not None]
    if comp:
        print("compile time (shape check, compiler, host program) up to %.3f s for programs of up to %d host instructions" % (
            max(c[0] for c in comp), max(c[1] for c in comp)))
    for r in rows:
        if r.get("name") == "speed":
            print("runner speed: %d host steps in %.2f s = %.2f million steps per second" % (
                r["host_steps"], r["seconds"], r["steps_per_second"] / 1e6))


if __name__ == "__main__":
    main(sys.argv[1:])
