"""Auditor checks for Landauer phase outputs.

This verifier recomputes μ-ledger aggregates from ``landauer_steps.jsonl``
and ensures that they match the summary CSV emitted by the builder.  It
then enforces the Landauer work balance criterion

    |⟨W⟩/(k_B T ln 2) − Σ μ_answer| ≤ ε

for every trial captured in the run directory.  The script also verifies
that the recorded metadata digest matches the hash of the ledger rows so
that archivists can trust the integrity of the proofpack artefacts.

The module exposes :func:`verify_landauer` for programmatic use and a
CLI interface compatible with the historical ``verifier/check_*`` tools.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
from pathlib import Path
from typing import Dict, Iterable, List, Mapping, MutableMapping, Tuple

from experiments import ledger_io

K_BOLTZMANN = 1.0
LN2 = math.log(2.0)


TrialKey = Tuple[int, float, int, str]


def _load_summary(summary_path: Path) -> Dict[TrialKey, Mapping[str, str]]:
    if not summary_path.exists():
        raise FileNotFoundError(f"Missing Landauer summary CSV: {summary_path}")
    with summary_path.open("r", encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle)
        rows = list(reader)
    if not rows:
        raise ValueError(f"Landauer summary CSV is empty: {summary_path}")
    summary: Dict[TrialKey, Mapping[str, str]] = {}
    for row in rows:
        key = (
            int(row["seed"]),
            float(row["T"]),
            int(row["trial_id"]),
            str(row["protocol"]),
        )
        summary[key] = row
    return summary


def _aggregates_from_ledger(entries: Iterable[ledger_io.LedgerEntry]) -> Dict[TrialKey, MutableMapping[str, float]]:
    aggregates: Dict[TrialKey, MutableMapping[str, float]] = {}
    for entry in entries:
        payload = entry.payload
        key: TrialKey = (
            int(payload["seed"]),
            float(payload["T"]),
            int(payload["trial_id"]),
            str(payload["protocol"]),
        )
        state = aggregates.setdefault(
            key,
            {
                "mu_sum": 0.0,
                "work": 0.0,
            },
        )
        state["mu_sum"] += float(payload.get("mu_answer", 0.0))
        state["work"] = float(payload.get("cumulative_work", state["work"]))
    if not aggregates:
        raise ValueError("No ledger rows found for Landauer run")
    return aggregates


def _find_aggregate(
    aggregates: Mapping[TrialKey, MutableMapping[str, float]], key: TrialKey
) -> MutableMapping[str, float] | None:
    aggregate = aggregates.get(key)
    if aggregate is not None:
        return aggregate
    # Fallback for synthetic replays where the summary protocol differs
    for alt_key, alt_value in aggregates.items():
        if alt_key[:3] == key[:3]:
            return alt_value
    return None


def _verify_metadata(metadata_path: Path, ledger_entries: List[ledger_io.LedgerEntry]) -> bool:
    if not metadata_path.exists():
        raise FileNotFoundError(f"Missing Landauer metadata JSON: {metadata_path}")
    with metadata_path.open("r", encoding="utf-8") as handle:
        metadata = json.load(handle)
    expected = metadata.get("ledger_digest_sha256")
    actual = ledger_io.ledger_digest(ledger_entries)
    return expected == actual


def verify_landauer(
    run_dir: Path,
    epsilon: float = 0.05,
    out_path: Path | None = None,
) -> Tuple[Path, Mapping[str, object]]:
    """Validate Landauer outputs located in ``run_dir``.

    Parameters
    ----------
    run_dir:
        Directory containing ``landauer_steps.jsonl`` and companion files.
    epsilon:
        Tolerance applied to the Landauer work balance check.
    out_path:
        Optional path for the emitted verifier JSON.  Defaults to
        ``verifier/landauer_verifier.json`` when not provided.
    """

    run_dir = Path(run_dir)
    ledger_path = run_dir / "landauer_steps.jsonl"
    summary_path = run_dir / "landauer_summary.csv"
    metadata_path = run_dir / "landauer_metadata.json"

    if not ledger_path.exists():
        raise FileNotFoundError(f"Missing Landauer ledger: {ledger_path}")

    ledger_entries = list(ledger_io.load_ledger(ledger_path))
    summary_rows = _load_summary(summary_path)
    aggregates = _aggregates_from_ledger(ledger_entries)
    metadata_ok = _verify_metadata(metadata_path, ledger_entries)

    trials: List[Dict[str, object]] = []
    status = metadata_ok

    for key, summary in summary_rows.items():
        aggregate = _find_aggregate(aggregates, key)
        if aggregate is None:
            status = False
            trials.append(
                {
                    "key": {
                        "seed": key[0],
                        "T": key[1],
                        "trial_id": key[2],
                        "protocol": key[3],
                    },
                    "error": "missing_ledger_rows",
                }
            )
            continue

        mu_summary = float(summary["sum_mu_bits"])
        work_summary = float(summary["work"])
        work_bits_summary = float(summary["work_over_kTln2"])

        mu_ledger = float(aggregate["mu_sum"])
        work_ledger = float(aggregate["work"])
        temperature = key[1]
        kTln2 = K_BOLTZMANN * temperature * LN2
        work_bits_ledger = work_ledger / kTln2 if kTln2 else float("inf")

        diff_summary = abs(work_bits_summary - mu_summary)
        diff_ledger = abs(work_bits_ledger - mu_ledger)
        within_tolerance = diff_ledger <= epsilon

        trials.append(
            {
                "key": {
                    "seed": key[0],
                    "T": temperature,
                    "trial_id": key[2],
                    "protocol": key[3],
                },
                "mu_summary": mu_summary,
                "mu_ledger": mu_ledger,
                "work": work_summary,
                "work_from_ledger": work_ledger,
                "work_bits_summary": work_bits_summary,
                "work_bits_ledger": work_bits_ledger,
                "diff_summary": diff_summary,
                "diff_ledger": diff_ledger,
                "within_tolerance": within_tolerance,
                "summary_matches_ledger": math.isclose(
                    mu_summary, mu_ledger, rel_tol=5e-6, abs_tol=5e-6
                )
                and math.isclose(work_summary, work_ledger, rel_tol=5e-6, abs_tol=5e-6),
            }
        )

        if not (within_tolerance and trials[-1]["summary_matches_ledger"]):
            status = False

    result: Dict[str, object] = {
        "status": status,
        "epsilon": epsilon,
        "metadata_digest_matches": metadata_ok,
        "trial_count": len(trials),
        "trials": trials,
    }

    out_path = out_path or Path("verifier/landauer_verifier.json")
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with out_path.open("w", encoding="utf-8") as handle:
        json.dump(result, handle, indent=2, sort_keys=True)
        handle.write("\n")
    return out_path, result


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Verify Landauer phase outputs")
    parser.add_argument("run_dir", type=Path, help="Directory containing Landauer artefacts")
    parser.add_argument("--epsilon", type=float, default=0.05, help="Tolerance for work balance")
    parser.add_argument(
        "--out",
        type=Path,
        default=Path("verifier/landauer_verifier.json"),
        help="Path to write verifier JSON",
    )
    return parser


def main(argv: Iterable[str] | None = None) -> None:  # pragma: no cover - CLI wrapper
    parser = _build_parser()
    args = parser.parse_args(argv)
    out_path, _ = verify_landauer(args.run_dir, epsilon=args.epsilon, out_path=args.out)
    print(f"Wrote verifier JSON: {out_path}")


if __name__ == "__main__":  # pragma: no cover - script entry point
    main()

