"""Verifier for anchored public single-particle tracking proofpacks."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Dict, Mapping, MutableMapping

from experiments import ledger_io
from experiments.public_data.spt_protocol import PROTOCOLS
from experiments.public_data.stats import delta_aic_exp_vs_poly, spearman, theil_sen_statistics


def _load_ledger(path: Path) -> list[ledger_io.LedgerEntry]:
    if not path.exists():
        raise FileNotFoundError(f"Missing ledger for protocol: {path}")
    return ledger_io.load_ledger(path)


def _summary_from_ledger(entries: Iterable[ledger_io.LedgerEntry]) -> MutableMapping[str, object]:
    mu_samples = [float(entry.payload.get("mu_answer", 0.0)) for entry in entries]
    entropy_samples = [float(entry.payload.get("entropy_delta", 0.0)) for entry in entries]
    complexity = [float(entry.payload.get("complexity", 0.0)) for entry in entries]
    slope, intercept, low, high = theil_sen_statistics(mu_samples, entropy_samples)
    rho, p_value = spearman(mu_samples, entropy_samples)
    payload: MutableMapping[str, object] = {
        "mu_sum": sum(mu_samples),
        "entropy_sum": sum(entropy_samples),
        "entropy_residual": sum(entropy_samples) - sum(mu_samples),
        "slope": slope,
        "slope_ci_low": low,
        "slope_ci_high": high,
        "slope_intercept": intercept,
        "spearman_rho": rho,
        "spearman_pvalue": p_value,
        "step_count": len(mu_samples),
    }
    payload["delta_aic"] = (
        delta_aic_exp_vs_poly(list(range(1, len(complexity) + 1)), complexity)
        if complexity
        else 0.0
    )
    return payload


def verify_public_spt(
    dataset_dir: Path,
    *,
    spearman_threshold: float = 0.9,
    pvalue_threshold: float = 1e-6,
    delta_aic_threshold: float = 10.0,
    oos_threshold: float = 0.1,
    out_path: Path | None = None,
) -> tuple[Path, Dict[str, object]]:
    dataset_dir = Path(dataset_dir)
    metadata_path = dataset_dir / "public_spt_metadata.json"
    if not metadata_path.exists():
        raise FileNotFoundError(f"Missing public SPT metadata: {metadata_path}")
    metadata = json.loads(metadata_path.read_text())

    oos_metrics_path = dataset_dir / "oos_metrics.json"
    if not oos_metrics_path.exists():
        raise FileNotFoundError(f"Missing OOS metrics: {oos_metrics_path}")
    oos_metrics = json.loads(oos_metrics_path.read_text())
    oos_error = float(oos_metrics.get("oos_median_abs_pct_error", float("inf")))

    ledgers_root = dataset_dir / "ledgers"
    summaries: Dict[str, Mapping[str, object]] = {}
    status = True
    protocol_results: Dict[str, Mapping[str, object]] = {}

    for protocol in PROTOCOLS:
        ledger_entries = _load_ledger(ledgers_root / f"{protocol}.jsonl")
        summary = _summary_from_ledger(ledger_entries)
        protocol_results[protocol] = summary
        rho = float(summary["spearman_rho"])
        p_value = float(summary["spearman_pvalue"])
        slope_low = float(summary["slope_ci_low"])
        slope_high = float(summary["slope_ci_high"])
        if protocol == "destroyed":
            destroyed_ok = slope_low <= 0.0 <= slope_high and rho < spearman_threshold
            status = status and destroyed_ok
        else:
            rho_ok = rho >= spearman_threshold and p_value <= pvalue_threshold
            slope_ok = slope_low <= 1.0 <= slope_high
            status = status and rho_ok and slope_ok
        if protocol == "blind":
            delta_aic = float(summary.get("delta_aic", 0.0))
            status = status and delta_aic >= delta_aic_threshold

    status = status and oos_error <= oos_threshold

    result: Dict[str, object] = {
        "status": status,
        "dataset": metadata.get("dataset"),
        "protocols": protocol_results,
        "oos_median_abs_pct_error": oos_error,
        "spearman_threshold": spearman_threshold,
        "pvalue_threshold": pvalue_threshold,
        "delta_aic_threshold": delta_aic_threshold,
        "oos_threshold": oos_threshold,
    }

    out_path = out_path or (dataset_dir / "verifier" / "public_spt.json")
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with out_path.open("w", encoding="utf-8") as handle:
        json.dump(result, handle, indent=2, sort_keys=True)
        handle.write("\n")
    return out_path, result


__all__ = ["verify_public_spt"]

