#!/usr/bin/env python3
"""Deterministically audit the Tseitin receipts without rerunning the solver."""

from __future__ import annotations

import json
import math
import sys
from collections import Counter
from pathlib import Path
from typing import Iterable


def _iter_receipts(root: Path) -> Iterable[Path]:
    yield from sorted(root.glob("receipt_*.json"))


def _verify_receipt(path: Path) -> str:
    payload = json.loads(path.read_text())

    blind = payload.get("blind_result", {})
    sighted = payload.get("sighted_result", {})
    mu = payload.get("mu_metrics", {})
    counters = payload.get("counters", {})

    status = blind.get("status", "unknown")
    if status not in {"unsat", "censored"}:
        raise AssertionError(f"{path.name}: unexpected blind status {status!r}")

    if status == "unsat":
        conflicts = float(blind.get("conflicts", float("nan")))
        mu_blind = float(mu.get("mu_blind", float("nan")))
        if not math.isclose(conflicts, mu_blind, rel_tol=1e-9, abs_tol=1e-9):
            raise AssertionError(f"{path.name}: conflicts {conflicts} != μ_blind {mu_blind}")

    rank_gap = sighted.get("rank_gap")
    if rank_gap is not None:
        if rank_gap <= 0:
            raise AssertionError(f"{path.name}: rank gap {rank_gap} is not strictly positive")
        if sighted.get("rank_A") is not None and sighted.get("rank_aug") is not None:
            expected_gap = sighted["rank_aug"] - sighted["rank_A"]
            if expected_gap != rank_gap:
                raise AssertionError(f"{path.name}: inconsistent rank gap {rank_gap} vs {expected_gap}")

    mu_sighted = float(mu.get("mu_sighted", 0.0))
    mu_question = float(mu.get("mu_question", 0.0))
    mu_answer = float(mu.get("mu_answer", 0.0))
    n = int((payload.get('experiment_config') or {}).get('n', 0))
    expected = float(mu_question + mu_answer + 2 * n * n + 2 * n)
    if not math.isclose(expected, mu_sighted, rel_tol=1e-9, abs_tol=1e-9):
        raise AssertionError(f"{path.name}: μ_sighted != μ_question + μ_answer + 2n^2+2n")
    if not math.isclose(mu_answer, float(counters.get("info_gain", mu_answer)), rel_tol=1e-9, abs_tol=1e-9):
        raise AssertionError(f"{path.name}: info_gain != μ_answer")
    if not math.isclose(math.fmod(mu_question, 8.0), 0.0, abs_tol=1e-6):
        raise AssertionError(f"{path.name}: μ_question must be a multiple of 8 bits")

    return status


def main(argv: list[str]) -> int:
    root = Path(argv[1]) if len(argv) > 1 else Path(__file__).resolve().parents[2] / "experiments" / "20251101_070033_ci_fix"
    if not root.exists():
        raise FileNotFoundError(f"Receipt directory {root} not found")

    statuses = Counter()
    for receipt in _iter_receipts(root):
        status = _verify_receipt(receipt)
        statuses[status] += 1

    print("Receipt audit summary for", root)
    for label, count in sorted(statuses.items()):
        print(f"  {label:8}: {count}")
    print("All receipts passed invariant checks.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
