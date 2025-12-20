#!/usr/bin/env python3

"""Run a small suite of Thiele VM workloads and compare μ behavior.

This is meant to be a *real execution* sweep (not a mocked report): it runs the
actual VM on several programs and writes a combined JSON report.

Output is intentionally clean and phase-oriented:
INIT → DISCOVER → CLASSIFY → DECOMPOSE → EXECUTE → MERGE → VERIFY → SUCCESS
"""

from __future__ import annotations

import argparse
import json
import logging
import sys
import time
from pathlib import Path
from typing import Any, Dict, List

from thielecpu.program_sweep import default_workloads, run_sweep


PHASES = [
    "INIT",
    "DISCOVER",
    "CLASSIFY",
    "DECOMPOSE",
    "EXECUTE",
    "MERGE",
    "VERIFY",
    "SUCCESS",
]


def _bar(done: int, total: int, width: int = 28) -> str:
    if total <= 0:
        return "[" + "=" * width + "]"
    frac = max(0.0, min(1.0, done / total))
    filled = int(round(frac * width))
    return "[" + "=" * filled + "-" * (width - filled) + "]"


def _print_phase(phase: str) -> None:
    print(f"\n=== {phase} ===")


def _summarize(report: Dict[str, Any]) -> List[Dict[str, Any]]:
    rows: List[Dict[str, Any]] = []
    for item in report.get("workloads", []):
        summary = item.get("summary", {})
        rows.append(
            {
                "name": item.get("name"),
                "mu_discovery": summary.get("mu_discovery"),
                "mu_execution": summary.get("mu_execution"),
                "mu_total": summary.get("mu_total"),
                "mu_information_legacy": summary.get("mu_information"),
                "reasons": sorted((item.get("reasons") or {}).keys()),
            }
        )
    return rows


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument(
        "--outdir",
        type=Path,
        default=Path("out") / "program_sweep",
        help="Output directory (default: out/program_sweep)",
    )
    ap.add_argument(
        "--factoring-n",
        type=int,
        default=15,
        help="Composite modulus used for PYEXEC factoring workload (default: 15)",
    )
    ap.add_argument(
        "--verbose",
        action="store_true",
        help="Do not suppress VM stdout (very noisy)",
    )
    args = ap.parse_args()

    if not args.verbose:
        logging.disable(logging.CRITICAL)

    _print_phase("INIT")
    args.outdir.mkdir(parents=True, exist_ok=True)

    workloads = default_workloads(factoring_n=args.factoring_n)

    _print_phase("DISCOVER")
    print(f"Selected {len(workloads)} workloads")

    _print_phase("CLASSIFY")
    cats = {}
    for w in workloads:
        cat = (w.metadata or {}).get("category", "unknown")
        cats[cat] = cats.get(cat, 0) + 1
    print("Categories:", json.dumps(cats, sort_keys=True))

    _print_phase("DECOMPOSE")
    for w in workloads:
        prog_len = len(w.program)
        print(f"- {w.name}: {prog_len} instructions")

    _print_phase("EXECUTE")
    start = time.time()
    total = len(workloads)
    for i, w in enumerate(workloads, start=1):
        line = f"{_bar(i-1, total)} running {w.name} ({i}/{total})"
        print(line)
    report = run_sweep(
        workloads,
        base_outdir=args.outdir,
        quiet=not args.verbose,
        auto_mdlacc=True,
    )
    elapsed = time.time() - start

    _print_phase("MERGE")
    rows = _summarize(report)
    (args.outdir / "report_table.json").write_text(
        json.dumps(rows, indent=2, sort_keys=True), encoding="utf-8"
    )
    print(f"Wrote combined report to: {args.outdir / 'report.json'}")

    _print_phase("VERIFY")
    index = report.get("index", {})
    ok = True

    emit = index.get("emit_bits", {})
    if "emit_info_gain" not in (emit.get("reasons") or {}):
        print("FAIL: emit_bits did not record emit_info_gain")
        ok = False

    reveal = index.get("reveal_cert", {})
    reasons = (reveal.get("reasons") or {})
    if not any(r.startswith("reveal_module") for r in reasons.keys()):
        print("FAIL: reveal_cert did not record reveal_module*")
        ok = False

    factoring = index.get("pyexec_factoring", {})
    fac_reasons = (factoring.get("reasons") or {})
    if not any(r.startswith("factoring_revelation_") for r in fac_reasons.keys()):
        print("FAIL: pyexec_factoring did not trigger factoring revelation detection")
        ok = False

    if ok:
        print(f"All sweep invariants OK in {elapsed:.2f}s")

    _print_phase("SUCCESS" if ok else "FAILURE")
    print(json.dumps({"ok": ok, "elapsed_s": elapsed, "outdir": str(args.outdir)}, indent=2))
    return 0 if ok else 2


if __name__ == "__main__":
    raise SystemExit(main())
