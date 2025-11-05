"""Auditor checks for the Einstein relation builder outputs."""

from __future__ import annotations

import argparse
import csv
import json
from pathlib import Path
from typing import Dict, Iterable, List, Mapping, MutableMapping, Tuple

from experiments import ledger_io

K_BOLTZMANN = 1.0


TrialKey = Tuple[int, float, int, str]


def _load_summary(summary_path: Path) -> Dict[TrialKey, Mapping[str, str]]:
    if not summary_path.exists():
        raise FileNotFoundError(f"Missing Einstein summary CSV: {summary_path}")
    with summary_path.open("r", encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle)
        rows = list(reader)
    if not rows:
        raise ValueError(f"Einstein summary CSV is empty: {summary_path}")
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
                "sum_dx": 0.0,
                "sum_dx2": 0.0,
                "sum_dx_force": 0.0,
                "sum_force_sq": 0.0,
                "steps": 0.0,
                "mu_sum": 0.0,
                "cost_proxy": 0.0,
                "dt": float(payload.get("dt", 1.0)),
            },
        )
        dx = float(payload.get("dx", 0.0))
        force = float(payload.get("force", 0.0))
        state["sum_dx"] += dx
        state["sum_dx2"] += dx * dx
        state["sum_dx_force"] += dx * force
        state["sum_force_sq"] += force * force
        state["steps"] += 1.0
        state["mu_sum"] += float(payload.get("mu_answer", 0.0))
        state["cost_proxy"] += float(payload.get("abs_position", 0.0))
    if not aggregates:
        raise ValueError("No ledger rows found for Einstein run")
    return aggregates


def _verify_metadata(metadata_path: Path, ledger_entries: List[ledger_io.LedgerEntry]) -> bool:
    if not metadata_path.exists():
        raise FileNotFoundError(f"Missing Einstein metadata JSON: {metadata_path}")
    with metadata_path.open("r", encoding="utf-8") as handle:
        metadata = json.load(handle)
    expected = metadata.get("ledger_digest_sha256")
    actual = ledger_io.ledger_digest(ledger_entries)
    return expected == actual


def verify_einstein(
    run_dir: Path,
    delta: float = 0.05,
    out_path: Path | None = None,
) -> Tuple[Path, Mapping[str, object]]:
    """Validate Einstein relation outputs located in ``run_dir``."""

    run_dir = Path(run_dir)
    ledger_path = run_dir / "einstein_steps.jsonl"
    summary_path = run_dir / "einstein_summary.csv"
    metadata_path = run_dir / "einstein_metadata.json"

    if not ledger_path.exists():
        raise FileNotFoundError(f"Missing Einstein ledger: {ledger_path}")

    ledger_entries = list(ledger_io.load_ledger(ledger_path))
    summary_rows = _load_summary(summary_path)
    aggregates = _aggregates_from_ledger(ledger_entries)
    metadata_ok = _verify_metadata(metadata_path, ledger_entries)

    trials: List[Dict[str, object]] = []
    status = metadata_ok

    for key, summary in summary_rows.items():
        aggregate = aggregates.get(key)
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

        steps = max(int(aggregate["steps"]), 1)
        dt = float(aggregate["dt"])
        mean_dx = aggregate["sum_dx"] / steps
        mean_dx2 = aggregate["sum_dx2"] / steps
        variance_dx = max(0.0, mean_dx2 - mean_dx**2)
        diffusion = variance_dx / (2.0 * dt)
        denom = aggregate["sum_force_sq"] * dt
        mobility = aggregate["sum_dx_force"] / denom if denom > 0.0 else 0.0
        residual = diffusion - mobility * K_BOLTZMANN * key[1]
        drift_velocity = mean_dx / dt
        msd = mean_dx2
        cost_average = aggregate["cost_proxy"] / steps

        summary_diffusion = float(summary["diffusion"])
        summary_mobility = float(summary["mobility"])
        summary_residual = float(summary["residual"])
        summary_mu_sum = float(summary["mu_answer_sum"])
        summary_drift = float(summary["drift_velocity"])
        summary_msd = float(summary["msd"])
        summary_cost = float(summary["cost_proxy"])

        trial_result = {
            "key": {
                "seed": key[0],
                "T": key[1],
                "trial_id": key[2],
                "protocol": key[3],
            },
            "diffusion": diffusion,
            "summary_diffusion": summary_diffusion,
            "mobility": mobility,
            "summary_mobility": summary_mobility,
            "residual": residual,
            "summary_residual": summary_residual,
            "mu_answer_sum": aggregate["mu_sum"],
            "summary_mu_answer_sum": summary_mu_sum,
            "drift_velocity": drift_velocity,
            "summary_drift_velocity": summary_drift,
            "msd": msd,
            "summary_msd": summary_msd,
            "cost_proxy": cost_average,
            "summary_cost_proxy": summary_cost,
            "within_delta": abs(residual) <= delta,
            "summary_matches_ledger": all(
                abs(a - b) <= 5e-6 * max(1.0, abs(b))
                for a, b in [
                    (diffusion, summary_diffusion),
                    (mobility, summary_mobility),
                    (residual, summary_residual),
                    (aggregate["mu_sum"], summary_mu_sum),
                    (drift_velocity, summary_drift),
                    (msd, summary_msd),
                    (cost_average, summary_cost),
                ]
            ),
        }
        trials.append(trial_result)
        if not (trial_result["within_delta"] and trial_result["summary_matches_ledger"]):
            status = False

    result: Dict[str, object] = {
        "status": status,
        "delta": delta,
        "metadata_digest_matches": metadata_ok,
        "trial_count": len(trials),
        "trials": trials,
    }

    out_path = out_path or Path("verifier/einstein_verifier.json")
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with out_path.open("w", encoding="utf-8") as handle:
        json.dump(result, handle, indent=2, sort_keys=True)
        handle.write("\n")
    return out_path, result


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Verify Einstein relation outputs")
    parser.add_argument("run_dir", type=Path, help="Directory containing Einstein artefacts")
    parser.add_argument("--delta", type=float, default=0.05, help="Tolerance for D − μ k_B T")
    parser.add_argument(
        "--out",
        type=Path,
        default=Path("verifier/einstein_verifier.json"),
        help="Path to write verifier JSON",
    )
    return parser


def main(argv: Iterable[str] | None = None) -> None:  # pragma: no cover - CLI wrapper
    parser = _build_parser()
    args = parser.parse_args(argv)
    out_path, _ = verify_einstein(args.run_dir, delta=args.delta, out_path=args.out)
    print(f"Wrote verifier JSON: {out_path}")


if __name__ == "__main__":  # pragma: no cover - script entry point
    main()

