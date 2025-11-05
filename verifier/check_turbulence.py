from __future__ import annotations

import json
from pathlib import Path
from typing import Dict, Iterable, Mapping, MutableMapping

from experiments import ledger_io
from experiments.public_data.stats import (
    delta_aic_exp_vs_poly,
    spearman,
    theil_sen_statistics,
)
from experiments.turbulence import PROTOCOLS


def _load_ledger(path: Path) -> list[ledger_io.LedgerEntry]:
    if not path.exists():
        raise FileNotFoundError(f"Missing turbulence ledger: {path}")
    return ledger_io.load_ledger(path)


def _summary_from_entries(entries: Iterable[ledger_io.LedgerEntry]) -> MutableMapping[str, object]:
    mu_cumulative: list[float] = []
    entropy_cumulative: list[float] = []
    runtime_cumulative: list[float] = []
    runtime_increments: list[float] = []
    mu_total = 0.0
    entropy_total = 0.0
    runtime_total = 0.0

    for entry in entries:
        mu_total += float(entry.payload.get("mu_answer", 0.0))
        entropy_total += float(entry.payload.get("entropy_delta", 0.0))
        runtime_total += float(entry.payload.get("runtime_increment", 0.0))
        runtime_increments.append(float(entry.payload.get("runtime_increment", 0.0)))
        mu_cumulative.append(mu_total)
        entropy_cumulative.append(entropy_total)
        runtime_cumulative.append(runtime_total)

    rho, p_value = spearman(mu_cumulative, entropy_cumulative)
    slope, intercept, low, high = theil_sen_statistics(mu_cumulative, runtime_cumulative)
    del intercept
    indices = [float(index + 1) for index in range(len(runtime_cumulative))]
    delta_aic = (
        delta_aic_exp_vs_poly(indices, runtime_increments) if indices else 0.0
    )
    payload: MutableMapping[str, object] = {
        "mu_sum": mu_total,
        "entropy_sum": entropy_total,
        "runtime_sum": runtime_total,
        "spearman_rho": rho,
        "spearman_pvalue": p_value,
        "runtime_slope": slope,
        "runtime_ci_low": low,
        "runtime_ci_high": high,
        "delta_aic": delta_aic,
        "step_count": len(mu_cumulative),
    }
    return payload


def verify_turbulence(
    dataset_dir: Path,
    *,
    spearman_threshold: float = 0.9,
    pvalue_threshold: float = 1e-6,
    delta_aic_threshold: float = 10.0,
    destroyed_rho_drop: float = 0.2,
    slope_tolerance: float = 0.1,
    out_path: Path | None = None,
) -> tuple[Path, Dict[str, object]]:
    dataset_dir = Path(dataset_dir)
    metadata_path = dataset_dir / "turbulence_metadata.json"
    if not metadata_path.exists():
        raise FileNotFoundError(f"Missing turbulence metadata: {metadata_path}")
    metadata = json.loads(metadata_path.read_text(encoding="utf-8"))

    ledgers_root = dataset_dir / "ledgers"
    declared_protocols = metadata.get("protocols")
    if isinstance(declared_protocols, list):
        active_protocols = [protocol for protocol in PROTOCOLS if protocol in declared_protocols]
        if not active_protocols:
            active_protocols = list(PROTOCOLS)
    else:
        active_protocols = list(PROTOCOLS)

    protocol_summaries: Dict[str, Mapping[str, object]] = {}
    status = True
    sighted_rho: float | None = None

    for protocol in active_protocols:
        entries = _load_ledger(ledgers_root / f"{protocol}.jsonl")
        summary = _summary_from_entries(entries)
        protocol_summaries[protocol] = summary

        rho = float(summary.get("spearman_rho", 0.0))
        p_value = float(summary.get("spearman_pvalue", 1.0))
        slope_low = float(summary.get("runtime_ci_low", 0.0))
        slope_high = float(summary.get("runtime_ci_high", 0.0))

        if protocol == "sighted":
            sighted_rho = rho
            status = status and rho >= spearman_threshold and p_value <= pvalue_threshold
            slope = float(summary.get("runtime_slope", 0.0))
            status = status and abs(slope) <= slope_tolerance
        elif protocol == "blind":
            delta_aic = float(summary.get("delta_aic", 0.0))
            status = status and rho >= spearman_threshold and p_value <= pvalue_threshold
            status = status and delta_aic >= delta_aic_threshold
        elif protocol == "destroyed":
            slope = float(summary.get("runtime_slope", 0.0))
            status = status and abs(slope) <= slope_tolerance
            if sighted_rho is not None:
                status = status and rho <= sighted_rho - destroyed_rho_drop

    result: Dict[str, object] = {
        "status": status,
        "dataset": metadata.get("dataset"),
        "field": metadata.get("field"),
        "time_count": metadata.get("time_count"),
        "point_count": metadata.get("point_count"),
        "protocols": protocol_summaries,
        "protocols_checked": active_protocols,
        "skipped_protocols": [protocol for protocol in PROTOCOLS if protocol not in active_protocols],
        "spearman_threshold": spearman_threshold,
        "pvalue_threshold": pvalue_threshold,
        "delta_aic_threshold": delta_aic_threshold,
        "destroyed_rho_drop": destroyed_rho_drop,
        "slope_tolerance": slope_tolerance,
    }

    out_path = out_path or (dataset_dir / "verifier" / "turbulence.json")
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with out_path.open("w", encoding="utf-8") as handle:
        json.dump(result, handle, indent=2, sort_keys=True)
        handle.write("\n")
    return out_path, result


__all__ = ["verify_turbulence"]
