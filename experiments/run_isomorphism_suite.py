"""Run a suite of isomorphism experiments across multiple CA rules.

Usage
-----
    python -m experiments.run_isomorphism_suite --rules 30 90 --steps 256

The script reuses :mod:`the_isomorphism` to execute each run, emitting optional
per-run receipts and an aggregated suite manifest that records provenance for
all rules.  The aggregated manifest is intended to complement the single-run
receipt workflow by demonstrating that the seal/ledger reconciliation holds for
multiple cellular automata.
"""

from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Iterable, List

from the_isomorphism import (
    DEFAULT_RULE,
    DEFAULT_SECRET_KEY,
    EXPORT_ROOT,
    export_receipt,
    perform_isomorphism,
)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Run multiple isomorphism experiments and emit a suite manifest.",
    )
    parser.add_argument(
        "--rules",
        nargs="*",
        type=int,
        default=[DEFAULT_RULE, 90],
        help="Elementary cellular automaton rules to evaluate (default: 30 and 90)",
    )
    parser.add_argument(
        "--cell-count",
        type=int,
        default=256,
        help="Width of the automaton tape",
    )
    parser.add_argument(
        "--steps",
        type=int,
        default=1_000,
        help="Number of steps for each run",
    )
    parser.add_argument(
        "--secret-key",
        type=str,
        default=DEFAULT_SECRET_KEY.decode("utf-8"),
        help="ASCII prophecy key shared across all runs",
    )
    parser.add_argument(
        "--export-dir",
        type=Path,
        default=EXPORT_ROOT,
        help="Directory for per-run receipts (if enabled)",
    )
    parser.add_argument(
        "--suite-export",
        type=Path,
        default=Path("experiments/results/isomorphism_suite.json"),
        help="Path to write the aggregated suite manifest",
    )
    parser.add_argument(
        "--progress-interval",
        type=int,
        default=0,
        help="Optional progress cadence for each run (<=0 suppresses progress)",
    )
    parser.add_argument(
        "--emit-individual-receipts",
        action="store_true",
        help="If set, store a JSON receipt for every run alongside the suite manifest",
    )
    return parser.parse_args()


def _export_suite_manifest(
    runs: Iterable[dict],
    manifest_path: Path,
) -> Path:
    manifest_path.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        "timestamp": datetime.now(timezone.utc).isoformat(),
        "runs": list(runs),
    }
    with manifest_path.open("w", encoding="utf-8") as handle:
        json.dump(payload, handle, indent=2)
    return manifest_path


def main() -> None:
    args = parse_args()
    secret_key = args.secret_key.encode("utf-8")
    progress_interval = args.progress_interval if args.progress_interval > 0 else None

    aggregated_runs: List[dict] = []

    for rule in args.rules:
        print(f"[SUITE] Running rule {rule}")
        record = perform_isomorphism(
            cell_count=args.cell_count,
            steps=args.steps,
            secret_key=secret_key,
            rule=rule,
            progress_interval=progress_interval,
        )
        print(f"        verdict: {record.verdict}")

        receipt_path: Path | None = None
        if args.emit_individual_receipts:
            receipt_path = export_receipt(record, args.export_dir)
            print(f"        receipt written to {receipt_path}")

        aggregated_runs.append(
            {
                "rule": rule,
                "verdict": record.verdict,
                "is_isomorphic": record.is_isomorphic,
                "seal": record.seal,
                "global_certificate": record.global_certificate,
                "computed_isomorphism": record.computed_isomorphism,
                "final_state_hash": record.final_state_hash,
                "ledger_length": record.ledger_length,
                "executed_steps": record.executed_steps,
                "receipt": str(receipt_path) if receipt_path else None,
            }
        )

    manifest_path = _export_suite_manifest(aggregated_runs, args.suite_export)
    print(f"Suite manifest written to {manifest_path}")


if __name__ == "__main__":
    main()
