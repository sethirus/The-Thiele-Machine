"""Auditor checks for the entropy identity diffusion builder."""

from __future__ import annotations

import argparse
import csv
import json
import math
from pathlib import Path
from typing import Dict, Iterable, List, Mapping, MutableMapping, Sequence, Tuple

from experiments import ledger_io


TrialKey = Tuple[int, float, int, str]


def _load_summary(summary_path: Path) -> Dict[TrialKey, Mapping[str, str]]:
    if not summary_path.exists():
        raise FileNotFoundError(f"Missing entropy summary CSV: {summary_path}")
    with summary_path.open("r", encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle)
        rows = list(reader)
    if not rows:
        raise ValueError(f"Entropy summary CSV is empty: {summary_path}")
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


def _load_series(series_path: Path) -> Dict[Tuple[int, float, int], List[Mapping[str, str]]]:
    if not series_path.exists():
        raise FileNotFoundError(f"Missing entropy series CSV: {series_path}")
    with series_path.open("r", encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle)
        rows = list(reader)
    if not rows:
        raise ValueError(f"Entropy series CSV is empty: {series_path}")
    grouped: Dict[Tuple[int, float, int], List[Mapping[str, str]]] = {}
    for row in rows:
        key = (
            int(row["seed"]),
            float(row["T"]),
            int(row["trial_id"]),
        )
        grouped.setdefault(key, []).append(row)
    return grouped


def _theil_sen_statistics(xs: Sequence[float], ys: Sequence[float]) -> Tuple[float, float, float, float]:
    n = len(xs)
    slopes: List[float] = []
    for i in range(n):
        for j in range(i + 1, n):
            if xs[j] == xs[i]:
                continue
            slopes.append((ys[j] - ys[i]) / (xs[j] - xs[i]))
    if not slopes:
        slope = 0.0
        intercept = float(_median(ys)) if ys else 0.0
        return slope, intercept, slope, slope
    slopes.sort()
    slope = _median(slopes)
    intercepts = [ys[idx] - slope * xs[idx] for idx in range(n)]
    intercept = _median(intercepts)
    low = _quantile(slopes, 0.025)
    high = _quantile(slopes, 0.975)
    return slope, intercept, low, high


def _median(values: Sequence[float]) -> float:
    if not values:
        return 0.0
    sorted_vals = sorted(values)
    n = len(sorted_vals)
    mid = n // 2
    if n % 2 == 1:
        return sorted_vals[mid]
    return 0.5 * (sorted_vals[mid - 1] + sorted_vals[mid])


def _quantile(values: Sequence[float], q: float) -> float:
    if not values:
        return 0.0
    if q <= 0.0:
        return values[0]
    if q >= 1.0:
        return values[-1]
    position = q * (len(values) - 1)
    lower = int(math.floor(position))
    upper = int(math.ceil(position))
    if lower == upper:
        return values[lower]
    weight = position - lower
    return values[lower] * (1 - weight) + values[upper] * weight


def _rank(values: Sequence[float]) -> List[float]:
    n = len(values)
    indexed = sorted(range(n), key=lambda idx: values[idx])
    ranks = [0.0] * n
    i = 0
    while i < n:
        j = i
        while j + 1 < n and values[indexed[j + 1]] == values[indexed[i]]:
            j += 1
        rank_value = (i + j + 2) / 2.0
        for k in range(i, j + 1):
            ranks[indexed[k]] = rank_value
        i = j + 1
    return ranks


def _spearman(xs: Sequence[float], ys: Sequence[float]) -> Tuple[float, float]:
    if len(xs) != len(ys):
        raise ValueError("Spearman samples must share length")
    n = len(xs)
    if n < 3:
        return 0.0, 1.0
    rank_x = _rank(xs)
    rank_y = _rank(ys)
    mean_x = sum(rank_x) / n
    mean_y = sum(rank_y) / n
    cov = sum((rank_x[i] - mean_x) * (rank_y[i] - mean_y) for i in range(n))
    std_x = math.sqrt(sum((rank - mean_x) ** 2 for rank in rank_x))
    std_y = math.sqrt(sum((rank - mean_y) ** 2 for rank in rank_y))
    if std_x == 0.0 or std_y == 0.0:
        return 0.0, 1.0
    rho = cov / (std_x * std_y)
    rho = max(-1.0, min(1.0, rho))
    t_stat = abs(rho) * math.sqrt((n - 2) / max(1e-12, 1.0 - rho**2))
    p = math.erfc(t_stat / math.sqrt(2.0))
    return rho, p


def _aggregates_from_ledger(entries: Iterable[ledger_io.LedgerEntry]) -> Dict[TrialKey, MutableMapping[str, object]]:
    aggregates: Dict[TrialKey, MutableMapping[str, object]] = {}
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
                "mu_samples": [],
                "entropy_samples": [],
            },
        )
        state["mu_samples"].append(float(payload.get("mu_answer", 0.0)))
        state["entropy_samples"].append(float(payload.get("entropy_delta", 0.0)))
    if not aggregates:
        raise ValueError("No ledger rows found for entropy run")
    return aggregates


def _verify_metadata(metadata_path: Path, ledger_entries: Sequence[ledger_io.LedgerEntry]) -> bool:
    if not metadata_path.exists():
        raise FileNotFoundError(f"Missing entropy metadata JSON: {metadata_path}")
    with metadata_path.open("r", encoding="utf-8") as handle:
        metadata = json.load(handle)
    expected = metadata.get("ledger_digest_sha256")
    actual = ledger_io.ledger_digest(ledger_entries)
    return expected == actual


def verify_entropy(
    run_dir: Path,
    slope_target: float = 1.0,
    intercept_tolerance: float = 0.05,
    rho_threshold: float = 0.9,
    pvalue_threshold: float = 1e-6,
    out_path: Path | None = None,
) -> Tuple[Path, Mapping[str, object]]:
    """Validate entropy identity outputs located in ``run_dir``."""

    run_dir = Path(run_dir)
    ledger_path = run_dir / "entropy_steps.jsonl"
    summary_path = run_dir / "entropy_summary.csv"
    series_path = run_dir / "entropy_series.csv"
    metadata_path = run_dir / "entropy_metadata.json"

    if not ledger_path.exists():
        raise FileNotFoundError(f"Missing entropy ledger: {ledger_path}")

    ledger_entries = list(ledger_io.load_ledger(ledger_path))
    summary_rows = _load_summary(summary_path)
    series_rows = _load_series(series_path)
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

        mu_samples: List[float] = list(aggregate["mu_samples"])
        entropy_samples: List[float] = list(aggregate["entropy_samples"])
        slope, intercept, low, high = _theil_sen_statistics(mu_samples, entropy_samples)
        rho, p_value = _spearman(mu_samples, entropy_samples)
        mu_sum = sum(mu_samples)
        entropy_sum = sum(entropy_samples)

        summary_mu = float(summary["mu_answer_sum"])
        summary_entropy = float(summary["entropy_sum"])
        summary_residual = float(summary["entropy_residual"])
        summary_slope = float(summary["theil_sen_slope"])
        summary_intercept = float(summary["theil_sen_intercept"])
        summary_low = float(summary["slope_ci_low"])
        summary_high = float(summary["slope_ci_high"])
        summary_rho = float(summary["spearman_rho"])
        summary_p = float(summary["spearman_pvalue"])

        slope_covers_target = (summary_low <= slope_target <= summary_high) and (low <= slope_target <= high)
        intercept_close = abs(summary_intercept) <= intercept_tolerance and abs(intercept) <= intercept_tolerance
        rho_ok = summary_rho >= rho_threshold and rho >= rho_threshold
        p_ok = summary_p <= pvalue_threshold and p_value <= pvalue_threshold

        series_ok = True
        base_key = (key[0], key[1], key[2])
        if base_key in series_rows:
            cumulative_mu = 0.0
            cumulative_entropy = 0.0
            sorted_rows = sorted(series_rows[base_key], key=lambda row: int(row["step"]))
            if len(sorted_rows) != len(mu_samples):
                series_ok = False
            for mu_inc, entropy_inc, row in zip(mu_samples, entropy_samples, sorted_rows):
                cumulative_mu += mu_inc
                cumulative_entropy += entropy_inc
                series_ok = (
                    series_ok
                    and math.isclose(float(row["mu_cumulative"]), cumulative_mu, rel_tol=5e-6, abs_tol=5e-6)
                    and math.isclose(
                        float(row["entropy_cumulative"]), cumulative_entropy, rel_tol=5e-6, abs_tol=5e-6
                    )
                )
        else:
            series_ok = False

        trial_result = {
            "key": {
                "seed": key[0],
                "T": key[1],
                "trial_id": key[2],
                "protocol": key[3],
            },
            "mu_sum": mu_sum,
            "summary_mu_sum": summary_mu,
            "entropy_sum": entropy_sum,
            "summary_entropy_sum": summary_entropy,
            "entropy_residual": entropy_sum - mu_sum,
            "summary_entropy_residual": summary_residual,
            "slope": slope,
            "summary_slope": summary_slope,
            "slope_ci": (low, high),
            "summary_slope_ci": (summary_low, summary_high),
            "intercept": intercept,
            "summary_intercept": summary_intercept,
            "rho": rho,
            "summary_rho": summary_rho,
            "p_value": p_value,
            "summary_p_value": summary_p,
            "slope_covers_target": slope_covers_target,
            "intercept_close": intercept_close,
            "rho_ok": rho_ok,
            "p_value_ok": p_ok,
            "series_matches": series_ok,
            "summary_matches_ledger": all(
                math.isclose(a, b, rel_tol=5e-6, abs_tol=5e-6)
                for a, b in [
                    (mu_sum, summary_mu),
                    (entropy_sum, summary_entropy),
                    (entropy_sum - mu_sum, summary_residual),
                    (slope, summary_slope),
                    (intercept, summary_intercept),
                    (low, summary_low),
                    (high, summary_high),
                    (rho, summary_rho),
                ]
            )
            and p_ok,
        }
        trials.append(trial_result)
        if not (
            trial_result["slope_covers_target"]
            and trial_result["intercept_close"]
            and trial_result["rho_ok"]
            and trial_result["p_value_ok"]
            and trial_result["series_matches"]
            and trial_result["summary_matches_ledger"]
        ):
            status = False

    result: Dict[str, object] = {
        "status": status,
        "slope_target": slope_target,
        "intercept_tolerance": intercept_tolerance,
        "rho_threshold": rho_threshold,
        "pvalue_threshold": pvalue_threshold,
        "metadata_digest_matches": metadata_ok,
        "trial_count": len(trials),
        "trials": trials,
    }

    out_path = out_path or Path("verifier/entropy_verifier.json")
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with out_path.open("w", encoding="utf-8") as handle:
        json.dump(result, handle, indent=2, sort_keys=True)
        handle.write("\n")
    return out_path, result


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Verify entropy identity outputs")
    parser.add_argument("run_dir", type=Path, help="Directory containing entropy artefacts")
    parser.add_argument("--slope-target", type=float, default=1.0, help="Target slope for Theil–Sen estimate")
    parser.add_argument(
        "--intercept-tolerance",
        type=float,
        default=0.05,
        help="Absolute tolerance for the intercept to be considered ~0",
    )
    parser.add_argument("--rho-threshold", type=float, default=0.9, help="Minimum Spearman ρ")
    parser.add_argument(
        "--pvalue-threshold",
        type=float,
        default=1e-6,
        help="Maximum allowed Spearman p-value",
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=Path("verifier/entropy_verifier.json"),
        help="Path to write verifier JSON",
    )
    return parser


def main(argv: Iterable[str] | None = None) -> None:  # pragma: no cover - CLI wrapper
    parser = _build_parser()
    args = parser.parse_args(argv)
    out_path, _ = verify_entropy(
        run_dir=args.run_dir,
        slope_target=args.slope_target,
        intercept_tolerance=args.intercept_tolerance,
        rho_threshold=args.rho_threshold,
        pvalue_threshold=args.pvalue_threshold,
        out_path=args.out,
    )
    print(f"Wrote verifier JSON: {out_path}")


if __name__ == "__main__":  # pragma: no cover - script entry point
    main()

