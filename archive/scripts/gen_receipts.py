# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

#!/usr/bin/env python3
"""Generate CSV receipts from a program run directory."""

from __future__ import annotations

import argparse
import csv
import json
from pathlib import Path


def _write_mu_ledger(run_dir: Path) -> None:
    ledger_path = run_dir / "mu_ledger.json"
    ledger = json.loads(ledger_path.read_text())
    out_csv = run_dir / "mu_ledger.csv"
    with out_csv.open("w", newline="") as fh:
        writer = csv.DictWriter(
            fh, fieldnames=["step", "delta_mu", "total_mu", "reason"]
        )
        writer.writeheader()
        writer.writerows(ledger)


def _write_summary(run_dir: Path) -> None:
    summary_path = run_dir / "summary.json"
    summary = json.loads(summary_path.read_text())
    out_csv = run_dir / "summary.csv"
    with out_csv.open("w", newline="") as fh:
        writer = csv.DictWriter(fh, fieldnames=sorted(summary))
        writer.writeheader()
        writer.writerow(summary)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("run_dir", nargs="?", default="out/demo", type=Path)
    args = parser.parse_args()

    _write_mu_ledger(args.run_dir)
    _write_summary(args.run_dir)


if __name__ == "__main__":
    main()
