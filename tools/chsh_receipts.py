#!/usr/bin/env python3
"""Canonical CHSH-from-receipts extractor.

Milestone 1A goal: there should be *one* receipt→CHSH pipeline used across the
repo, so that later gates (adversarial search + 3-layer checks) share the same
parsing, validation, and CHSH convention.

Non-forgeability policy:
- Only accept trials emitted by the CHSH_TRIAL opcode (receipt.instruction.op).
- Only accept payloads with x,y,a,b ∈ {0,1}.

This module is intentionally small and pure: it does not depend on VM execution
or on signature verification (which can be layered on separately).
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Dict, Iterable, List, Tuple

from thielecpu.receipts import load_receipts

from tools.bell_operational import DatasetCounts, chsh_from_counts

CountKey = Tuple[int, int, int, int]


@dataclass(frozen=True)
class ReceiptTrial:
    x: int
    y: int
    a: int
    b: int


def decode_trials_from_receipts(receipts_path: Path) -> List[ReceiptTrial]:
    """Extract semantically-valid CHSH trials from a VM step receipts JSON file."""

    trials: List[ReceiptTrial] = []
    for receipt in load_receipts(receipts_path):
        # Non-forgeability: only accept trials emitted by the CHSH_TRIAL opcode.
        if receipt.instruction.op != "CHSH_TRIAL":
            continue

        payload = receipt.instruction.payload
        if not isinstance(payload, dict):
            continue

        try:
            x_raw = payload.get("x")
            y_raw = payload.get("y")
            a_raw = payload.get("a")
            b_raw = payload.get("b")
            if x_raw is None or y_raw is None or a_raw is None or b_raw is None:
                continue
            x = int(x_raw)
            y = int(y_raw)
            a = int(a_raw)
            b = int(b_raw)
        except Exception:
            continue

        if x in (0, 1) and y in (0, 1) and a in (0, 1) and b in (0, 1):
            trials.append(ReceiptTrial(x=x, y=y, a=a, b=b))

    return trials


def counts_from_trials(trials: Iterable[ReceiptTrial]) -> DatasetCounts:
    """Convert a trial list into balanced per-setting counts."""

    counts: Dict[CountKey, int] = {}
    per_setting: Dict[Tuple[int, int], int] = {(0, 0): 0, (0, 1): 0, (1, 0): 0, (1, 1): 0}

    for t in trials:
        key = (t.x, t.y, t.a, t.b)
        counts[key] = int(counts.get(key, 0)) + 1
        per_setting[(t.x, t.y)] += 1

    n_vals = set(per_setting.values())
    if len(n_vals) != 1:
        raise ValueError(f"unbalanced trials per setting: {per_setting}")

    n_per_setting = int(next(iter(n_vals)))
    return DatasetCounts(n_per_setting=n_per_setting, counts=counts)


def chsh_from_receipts_path(receipts_path: Path) -> Fraction:
    """Compute CHSH directly from a step receipts JSON file."""

    trials = decode_trials_from_receipts(receipts_path)
    dataset = counts_from_trials(trials)
    return chsh_from_counts(dataset)


__all__ = [
    "ReceiptTrial",
    "decode_trials_from_receipts",
    "counts_from_trials",
    "chsh_from_receipts_path",
]
