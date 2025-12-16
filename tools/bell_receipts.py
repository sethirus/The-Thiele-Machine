#!/usr/bin/env python3
"""Receipt-driven CHSH harness.

Goal: make CHSH falsifiable from *VM step receipts*, not just side-band dataset files.

We generate a deterministic multiset of per-setting trials that exactly realizes a
rational probability table (e.g., artifacts/bell/supra_quantum_16_5.csv). Each trial
is emitted via the dedicated CHSH_TRIAL opcode so receipts are constrained by VM
semantics (not writable by arbitrary PYEXEC code).

This keeps kernel certification CSRs separate from receipt metadata.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Dict, Iterable, List, Mapping, Tuple

import csv

from thielecpu.state import State
from thielecpu.vm import VM

from tools.bell_operational import DatasetCounts, chsh_from_counts
from tools.chsh_receipts import ReceiptTrial as _CanonReceiptTrial
from tools.chsh_receipts import counts_from_trials as _counts_from_trials
from tools.chsh_receipts import decode_trials_from_receipts as _decode_trials_from_receipts

CountKey = Tuple[int, int, int, int]


@dataclass(frozen=True)
class ReceiptTrial:
    x: int
    y: int
    a: int
    b: int


def _lcm(a: int, b: int) -> int:
    from math import gcd

    if a == 0 or b == 0:
        return 0
    return abs(a // gcd(a, b) * b)


def load_probability_table_csv(path: Path) -> Dict[CountKey, Fraction]:
    """Load a (x,y,a,b)->probability table from a CSV.

    Expected columns: x,y,a,b,probability with probability as a Fraction string.
    """

    table: Dict[CountKey, Fraction] = {}
    with path.open("r", encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle)
        required = {"x", "y", "a", "b", "probability"}
        if not required.issubset(set(reader.fieldnames or [])):
            raise ValueError(f"missing required columns: {sorted(required)}")
        for row in reader:
            key = (int(row["x"]), int(row["y"]), int(row["a"]), int(row["b"]))
            table[key] = Fraction(str(row["probability"]))
    return table


def _denominator_lcm(probs: Iterable[Fraction]) -> int:
    denom = 1
    for p in probs:
        denom = _lcm(denom, int(p.denominator))
    return int(denom)


def trials_from_probability_table(table: Mapping[CountKey, Fraction]) -> List[ReceiptTrial]:
    """Expand a probability table into a deterministic list of trials.

    The output list contains exactly N trials per setting, where N is the LCM of all
    denominators appearing in that setting's probabilities.

    Ordering is stable and deterministic: (x,y) in lex order, then (a,b) in lex order.
    """

    trials: List[ReceiptTrial] = []

    # Determine a global denominator that works for all settings.
    denom = _denominator_lcm(table.values())
    if denom <= 0:
        raise ValueError("invalid denominator")

    for x in (0, 1):
        for y in (0, 1):
            total = 0
            for a in (0, 1):
                for b in (0, 1):
                    p = Fraction(table.get((x, y, a, b), Fraction(0, 1)))
                    count = int(p * denom)
                    if count < 0:
                        raise ValueError("negative probability")
                    total += count
                    for _ in range(count):
                        trials.append(ReceiptTrial(x=x, y=y, a=a, b=b))
            if total != denom:
                raise ValueError(f"setting ({x},{y}) total {total} != denom {denom}")

    return trials


def program_from_trials(trials: Iterable[ReceiptTrial]) -> List[Tuple[str, str]]:
    program: List[Tuple[str, str]] = [("PNEW", "{1,2}")]
    for t in trials:
        program.append(("CHSH_TRIAL", f"{t.x} {t.y} {t.a} {t.b}"))
    program.append(("EMIT", "done"))
    return program


def decode_trials_from_receipts(receipts_path: Path) -> List[ReceiptTrial]:
    # Compatibility wrapper: delegate to canonical extractor.
    return [ReceiptTrial(x=t.x, y=t.y, a=t.a, b=t.b) for t in _decode_trials_from_receipts(receipts_path)]


def counts_from_trials(trials: Iterable[ReceiptTrial]) -> DatasetCounts:
    # Compatibility wrapper: delegate to canonical extractor.
    canon_trials = [_CanonReceiptTrial(x=t.x, y=t.y, a=t.a, b=t.b) for t in trials]
    return _counts_from_trials(canon_trials)


def run_receipt_experiment(*, prob_csv: Path, outdir: Path) -> Dict[str, object]:
    """Run a receipt CHSH experiment and return a compact summary."""

    table = load_probability_table_csv(prob_csv)
    trials_expected = trials_from_probability_table(table)
    program = program_from_trials(trials_expected)

    vm = VM(State())
    vm.run(program, outdir)

    receipts_path = outdir / "step_receipts.json"
    trials_observed = decode_trials_from_receipts(receipts_path)

    dataset = counts_from_trials(trials_observed)
    s_value = chsh_from_counts(dataset)

    return {
        "outdir": str(outdir),
        "trials_expected": len(trials_expected),
        "trials_observed": len(trials_observed),
        "n_per_setting": dataset.n_per_setting,
        "chsh": str(s_value),
    }


def main() -> None:
    import argparse
    import json

    parser = argparse.ArgumentParser(description="Run a receipt-driven CHSH experiment.")
    parser.add_argument("--csv", required=True, type=Path, help="Probability table CSV (x,y,a,b,probability)")
    parser.add_argument("--outdir", required=True, type=Path, help="Output directory for VM receipts")
    args = parser.parse_args()

    args.outdir.mkdir(parents=True, exist_ok=True)
    summary = run_receipt_experiment(prob_csv=args.csv, outdir=args.outdir)
    print(json.dumps(summary, indent=2, sort_keys=True))


__all__ = [
    "ReceiptTrial",
    "load_probability_table_csv",
    "trials_from_probability_table",
    "program_from_trials",
    "decode_trials_from_receipts",
    "counts_from_trials",
    "run_receipt_experiment",
    "main",
]


if __name__ == "__main__":
    main()
