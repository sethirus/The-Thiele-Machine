"""Auditor checks for the Phase C cross-domain echoes builder."""

from __future__ import annotations

import argparse
import csv
import json
import math
from pathlib import Path
from typing import Dict, Iterable, List, Mapping, MutableMapping, Sequence, Tuple

from experiments import ledger_io

STRUCTURE_EXPECTED = {
    "sighted": 1.0,
    "blind": 0.5,
    "destroyed": 0.0,
}

SIGHTED_SLOPE_TOLERANCE = 0.1


TrialKey = Tuple[int, str, int, str]


def _load_summary(summary_path: Path) -> Dict[TrialKey, Mapping[str, str]]:
    if not summary_path.exists():
        raise FileNotFoundError(f"Missing cross-domain summary CSV: {summary_path}")
    with summary_path.open("r", encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle)
        rows = list(reader)
    if not rows:
        raise ValueError(f"Cross-domain summary CSV is empty: {summary_path}")
    summary: Dict[TrialKey, Mapping[str, str]] = {}
    for row in rows:
        key = (
            int(row["seed"]),
            str(row["domain"]),
            int(row["trial_id"]),
            str(row["protocol"]),
        )
        summary[key] = row
    return summary


def _linear_regression(xs: Sequence[float], ys: Sequence[float]) -> Tuple[float, float, float]:
    if len(xs) < 2:
        return 0.0, 0.0, 0.0
    mean_x = sum(xs) / len(xs)
    mean_y = sum(ys) / len(ys)
    var_x = sum((x - mean_x) ** 2 for x in xs)
    if var_x == 0.0:
        return 0.0, mean_y, 0.0
    cov = sum((x - mean_x) * (y - mean_y) for x, y in zip(xs, ys))
    slope = cov / var_x
    intercept = mean_y - slope * mean_x
    rss = sum((y - (intercept + slope * x)) ** 2 for x, y in zip(xs, ys))
    if len(xs) > 2:
        variance = rss / (len(xs) - 2)
        se_slope = math.sqrt(variance / var_x)
    else:
        se_slope = 0.0
    return slope, intercept, se_slope


def _aic_from_rss(rss: float, n: int, k: int) -> float:
    if rss <= 1e-12:
        rss = 1e-12
    return n * math.log(rss / n) + 2 * k


def _aggregates_from_ledger(entries: Iterable[ledger_io.LedgerEntry]) -> Dict[TrialKey, MutableMapping[str, float]]:
    per_trial: Dict[TrialKey, MutableMapping[str, float]] = {}
    mu_totals_by_domain: Dict[str, List[float]] = {}
    runtime_totals_by_domain: Dict[str, List[float]] = {}
    structure_by_domain: Dict[str, float] = {}

    for entry in entries:
        payload = entry.payload
        key: TrialKey = (
            int(payload["seed"]),
            str(payload["domain"]),
            int(payload["trial_id"]),
            str(payload["protocol"]),
        )
        state = per_trial.setdefault(
            key,
            {
                "mu_cumulative": 0.0,
                "runtime_cumulative": 0.0,
                "last_module": -1,
                "structure": float(payload.get("structure_integrity", 0.0)),
            },
        )
        module_index = int(payload.get("module_index", 0))
        if module_index >= state["last_module"]:
            state["mu_cumulative"] = float(payload.get("mu_cumulative", state["mu_cumulative"]))
            state["runtime_cumulative"] = float(payload.get("runtime_cumulative", state["runtime_cumulative"]))
            state["last_module"] = module_index
        structure_by_domain[key[1]] = float(payload.get("structure_integrity", structure_by_domain.get(key[1], 0.0)))

    for (seed, domain, trial_id, protocol), state in per_trial.items():
        mu_totals_by_domain.setdefault(domain, []).append(state["mu_cumulative"])
        runtime_totals_by_domain.setdefault(domain, []).append(state["runtime_cumulative"])

    domain_stats: Dict[str, Tuple[float, float, float, float, float]] = {}
    for domain, mu_values in mu_totals_by_domain.items():
        runtime_values = runtime_totals_by_domain[domain]
        slope, intercept, se_slope = _linear_regression(mu_values, runtime_values)
        slope_ci_low = slope - 1.96 * se_slope
        slope_ci_high = slope + 1.96 * se_slope

        if len(mu_values) >= 2:
            preds_poly = [intercept + slope * x for x in mu_values]
            rss_poly = sum((y - p) ** 2 for y, p in zip(runtime_values, preds_poly))
        else:
            rss_poly = 1e-12

        positive_runtime = [max(y, 1e-9) for y in runtime_values]
        log_y = [math.log(y) for y in positive_runtime]
        exp_slope, log_alpha, _ = _linear_regression(mu_values, log_y)
        preds_exp = [math.exp(log_alpha + exp_slope * x) for x in mu_values]
        rss_exp = sum((y - p) ** 2 for y, p in zip(runtime_values, preds_exp))

        aic_poly = _aic_from_rss(rss_poly, max(len(mu_values), 1), 2)
        aic_exp = _aic_from_rss(rss_exp, max(len(mu_values), 1), 2)
        delta_aic = aic_poly - aic_exp

        domain_stats[domain] = (slope, slope_ci_low, slope_ci_high, aic_exp, aic_poly, delta_aic)

    aggregates: Dict[TrialKey, MutableMapping[str, float]] = {}
    for key, state in per_trial.items():
        domain = key[1]
        slope, slope_ci_low, slope_ci_high, aic_exp, aic_poly, delta_aic = domain_stats[domain]
        aggregates[key] = {
            "mu_total_bits": state["mu_cumulative"],
            "runtime_total": state["runtime_cumulative"],
            "domain_slope": slope,
            "domain_slope_ci_low": slope_ci_low,
            "domain_slope_ci_high": slope_ci_high,
            "domain_aic_exponential": aic_exp,
            "domain_aic_polynomial": aic_poly,
            "domain_delta_aic": delta_aic,
            "structure_integrity": structure_by_domain.get(domain, 0.0),
        }
    if not aggregates:
        raise ValueError("No ledger rows found for cross-domain run")
    return aggregates


def _verify_metadata(metadata_path: Path, ledger_entries: Sequence[ledger_io.LedgerEntry]) -> bool:
    if not metadata_path.exists():
        raise FileNotFoundError(f"Missing cross-domain metadata JSON: {metadata_path}")
    with metadata_path.open("r", encoding="utf-8") as handle:
        metadata = json.load(handle)
    expected = metadata.get("ledger_digest_sha256")
    actual = ledger_io.ledger_digest(ledger_entries)
    return expected == actual


def verify_cross_domain(
    run_dir: Path,
    delta_aic_threshold: float = 10.0,
    out_path: Path | None = None,
) -> Tuple[Path, Mapping[str, object]]:
    """Validate cross-domain outputs located in ``run_dir``."""

    run_dir = Path(run_dir)
    ledger_path = run_dir / "cross_domain_steps.jsonl"
    summary_path = run_dir / "cross_domain_summary.csv"
    metadata_path = run_dir / "cross_domain_metadata.json"

    if not ledger_path.exists():
        raise FileNotFoundError(f"Missing cross-domain ledger: {ledger_path}")

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
                        "domain": key[1],
                        "trial_id": key[2],
                        "protocol": key[3],
                    },
                    "error": "missing_ledger_rows",
                }
            )
            continue

        structure_expected = STRUCTURE_EXPECTED.get(key[3], aggregate["structure_integrity"])
        slope_low = float(summary["domain_slope_ci_low"])
        slope_high = float(summary["domain_slope_ci_high"])
        if key[3] == "sighted":
            slope_ci_check = (slope_low <= 0.0 <= slope_high) or abs(float(summary["domain_slope"])) <= SIGHTED_SLOPE_TOLERANCE
        else:
            slope_ci_check = True
        delta_aic = float(summary["domain_delta_aic"])
        delta_aic_check = delta_aic >= delta_aic_threshold if key[3] == "blind" else True
        structure_value = float(summary["structure_integrity"])
        structure_check = math.isclose(structure_value, structure_expected, rel_tol=1e-6, abs_tol=1e-6)

        trial_result = {
            "key": {
                "seed": key[0],
                "domain": key[1],
                "trial_id": key[2],
                "protocol": key[3],
            },
            "summary": {
                "mu_total_bits": float(summary["mu_total_bits"]),
                "runtime_total": float(summary["runtime_total"]),
                "domain_slope": float(summary["domain_slope"]),
                "domain_slope_ci_low": slope_low,
                "domain_slope_ci_high": slope_high,
                "domain_aic_exponential": float(summary["domain_aic_exponential"]),
                "domain_aic_polynomial": float(summary["domain_aic_polynomial"]),
                "domain_delta_aic": delta_aic,
                "structure_integrity": structure_value,
            },
            "ledger": aggregate,
            "sighted_flatness": slope_ci_check,
            "blind_delta_aic_ok": delta_aic_check,
            "structure_ok": structure_check,
            "summary_matches_ledger": all(
                math.isclose(float(summary[field]), aggregate[field], rel_tol=5e-6, abs_tol=5e-6)
                for field in [
                    "mu_total_bits",
                    "runtime_total",
                    "domain_slope",
                    "domain_slope_ci_low",
                    "domain_slope_ci_high",
                    "domain_aic_exponential",
                    "domain_aic_polynomial",
                    "domain_delta_aic",
                    "structure_integrity",
                ]
            ),
        }
        trials.append(trial_result)
        if not (
            trial_result["summary_matches_ledger"]
            and trial_result["structure_ok"]
            and trial_result["sighted_flatness"]
            and trial_result["blind_delta_aic_ok"]
        ):
            status = False

    result: Dict[str, object] = {
        "status": status,
        "delta_aic_threshold": delta_aic_threshold,
        "metadata_digest_matches": metadata_ok,
        "trial_count": len(trials),
        "trials": trials,
    }

    out_path = out_path or Path("verifier/cross_domain_verifier.json")
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with out_path.open("w", encoding="utf-8") as handle:
        json.dump(result, handle, indent=2, sort_keys=True)
        handle.write("\n")
    return out_path, result


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Verify cross-domain echoes outputs")
    parser.add_argument("run_dir", type=Path, help="Directory containing cross-domain artefacts")
    parser.add_argument(
        "--delta-aic-threshold",
        type=float,
        default=10.0,
        help="Minimum ΔAIC (polynomial − exponential) required for blind runs",
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=Path("verifier/cross_domain_verifier.json"),
        help="Path to write verifier JSON",
    )
    return parser


def main(argv: Iterable[str] | None = None) -> None:  # pragma: no cover - CLI wrapper
    parser = _build_parser()
    args = parser.parse_args(argv)
    out_path, _ = verify_cross_domain(
        run_dir=args.run_dir,
        delta_aic_threshold=args.delta_aic_threshold,
        out_path=args.out,
    )
    print(f"Wrote verifier JSON: {out_path}")


if __name__ == "__main__":  # pragma: no cover - script entry point
    main()

