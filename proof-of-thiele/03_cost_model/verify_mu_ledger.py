#!/usr/bin/env python3
"""Replay μ-ledger conservation on the Tseitin receipts."""

from __future__ import annotations

import json
import math
import sys
from pathlib import Path

from tools import check_mu_ledger


def _iter_receipts(root: Path) -> list[Path]:
    return sorted(path for path in root.glob("receipt_*.json"))


def _summarise_receipt(path: Path) -> dict[str, float]:
    payload = json.loads(path.read_text())
    mu = payload.get("mu_metrics") or {}
    blind = float(mu.get("mu_blind", 0.0))
    sighted = float(mu.get("mu_sighted", 0.0))
    question = float(mu.get("mu_question", 0.0))
    answer = float(mu.get("mu_answer", 0.0))
    counters = payload.get("counters", {})
    info_gain = float(counters.get("info_gain", answer))

    n = int((payload.get('experiment_config') or {}).get('n', 0))
    discovery = float(2 * n * n + 2 * n)
    if not math.isclose(question + answer + discovery, sighted, rel_tol=1e-9, abs_tol=1e-9):
        raise AssertionError(f"{path.name}: μ_sighted != μ_question + μ_answer + 2n^2+2n")
    if not math.isclose(answer, info_gain, rel_tol=1e-9, abs_tol=1e-9):
        raise AssertionError(f"{path.name}: info_gain != μ_answer")
    blind_conflicts = float((payload.get("blind_result") or {}).get("conflicts", blind))
    if not math.isclose(blind_conflicts, blind, rel_tol=1e-9, abs_tol=1e-9):
        raise AssertionError(f"{path.name}: μ_blind != blind conflicts")

    return {
        "mu_blind": blind,
        "mu_sighted": sighted,
        "mu_question": question,
        "mu_answer": answer,
    }


def main(argv: list[str]) -> int:
    root = Path(argv[1]) if len(argv) > 1 else Path(__file__).resolve().parents[2] / "experiments" / "20251101_070033_ci_fix"
    receipts = _iter_receipts(root)
    if not receipts:
        raise FileNotFoundError(f"No receipt_*.json files found under {root}")

    exit_code = check_mu_ledger.main(["check_mu_ledger", str(root)])
    if exit_code:
        raise SystemExit(exit_code)

    totals = {"mu_blind": 0.0, "mu_sighted": 0.0, "mu_question": 0.0, "mu_answer": 0.0}
    for receipt in receipts:
        summary = _summarise_receipt(receipt)
        for key, value in summary.items():
            totals[key] += value

    print("μ-ledger conservation summary (Tseitin bundle):")
    for key, value in totals.items():
        print(f"  {key:>11}: {value:8.1f}")
    print("Checks completed successfully.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
