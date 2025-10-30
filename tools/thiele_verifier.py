"""Unified THIELE proofpack verifier.

This module orchestrates the phase-specific verifier scripts so that a
single ``THIELE_OK`` verdict can be emitted for a proofpack directory.
It discovers builder artefacts, dispatches to the existing Landauer,
Einstein, entropy-identity, CWD, and cross-domain verifiers, and
aggregates their JSON payloads into ``verifier/proofpack_verifier.json``.

The CLI entry point mirrors the historical ``tools/thiele_verifier.py``
concept: ``python -m tools.thiele_verifier <proofpack_dir>``.  On
success, ``THIELE_OK`` is printed to stdout and the process exits with
status code ``0``.  Any missing artefacts or verifier failure leads to a
non-zero exit code and the aggregated report includes the failure
metadata so auditors can triage.
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Iterable, Mapping, MutableMapping, Sequence

from verifier.check_cross_domain import verify_cross_domain
from verifier.check_cwd import verify_cwd
from verifier.check_einstein import verify_einstein
from verifier.check_entropy import verify_entropy
from verifier.check_landauer import verify_landauer
from verifier.check_public_spt import verify_public_spt
from verifier.check_turbulence import verify_turbulence


@dataclass
class RunResult:
    """Container for a single verifier invocation."""

    run_dir: Path
    status: bool
    verifier_json: Path
    payload: Mapping[str, object]
    error: str | None = None


def _safe_float(value: object) -> float | None:
    try:
        return float(value)
    except (TypeError, ValueError):
        return None


def _collect_floats(items: Sequence[object], key: str) -> list[float]:
    values: list[float] = []
    for item in items:
        if not isinstance(item, Mapping):
            continue
        raw = _safe_float(item.get(key))
        if raw is not None and math.isfinite(raw):
            values.append(raw)
    return values


def _collect_bools(items: Sequence[object], key: str) -> list[bool]:
    values: list[bool] = []
    for item in items:
        if isinstance(item, Mapping) and key in item:
            values.append(bool(item.get(key)))
    return values


def _landauer_run_highlights(payload: Mapping[str, object]) -> Dict[str, object]:
    trials = payload.get("trials", [])
    trial_seq: Sequence[object] = trials if isinstance(trials, Sequence) else ()
    diffs = [abs(value) for value in _collect_floats(trial_seq, "diff_ledger")]
    tolerance = _collect_bools(trial_seq, "within_tolerance")
    highlights: Dict[str, object] = {}
    if diffs:
        highlights["max_bits_gap"] = max(diffs)
        highlights["mean_bits_gap"] = sum(diffs) / len(diffs)
    if tolerance:
        highlights["tolerance_pass_rate"] = sum(1 for flag in tolerance if flag) / len(tolerance)
    if "metadata_digest_matches" in payload:
        highlights["metadata_digest_ok"] = bool(payload.get("metadata_digest_matches"))
    return highlights


def _landauer_phase_highlights(runs: Sequence[RunResult]) -> Dict[str, object]:
    max_gaps: list[float] = []
    mean_gaps: list[float] = []
    pass_rates: list[float] = []
    metadata: list[bool] = []
    for run in runs:
        if not isinstance(run.payload, Mapping):
            continue
        highlights = _landauer_run_highlights(run.payload)
        if "max_bits_gap" in highlights:
            max_gaps.append(float(highlights["max_bits_gap"]))
        if "mean_bits_gap" in highlights:
            mean_gaps.append(float(highlights["mean_bits_gap"]))
        if "tolerance_pass_rate" in highlights:
            pass_rates.append(float(highlights["tolerance_pass_rate"]))
        if "metadata_digest_ok" in highlights:
            metadata.append(bool(highlights["metadata_digest_ok"]))
    summary: Dict[str, object] = {}
    if max_gaps:
        summary["max_bits_gap"] = max(max_gaps)
    if mean_gaps:
        summary["mean_bits_gap"] = sum(mean_gaps) / len(mean_gaps)
    if pass_rates:
        summary["tolerance_pass_rate"] = sum(pass_rates) / len(pass_rates)
    if metadata:
        summary["metadata_digest_ok"] = all(metadata)
    return summary


def _einstein_run_highlights(payload: Mapping[str, object]) -> Dict[str, object]:
    trials = payload.get("trials", [])
    trial_seq: Sequence[object] = trials if isinstance(trials, Sequence) else ()
    residuals = [abs(value) for value in _collect_floats(trial_seq, "residual")]
    drift = [abs(value) for value in _collect_floats(trial_seq, "drift_velocity")]
    highlights: Dict[str, object] = {}
    if residuals:
        highlights["max_abs_residual"] = max(residuals)
        highlights["mean_abs_residual"] = sum(residuals) / len(residuals)
    if drift:
        highlights["max_abs_drift_velocity"] = max(drift)
    if "metadata_digest_matches" in payload:
        highlights["metadata_digest_ok"] = bool(payload.get("metadata_digest_matches"))
    return highlights


def _einstein_phase_highlights(runs: Sequence[RunResult]) -> Dict[str, object]:
    max_residuals: list[float] = []
    mean_residuals: list[float] = []
    max_drifts: list[float] = []
    metadata: list[bool] = []
    for run in runs:
        if not isinstance(run.payload, Mapping):
            continue
        highlights = _einstein_run_highlights(run.payload)
        if "max_abs_residual" in highlights:
            max_residuals.append(float(highlights["max_abs_residual"]))
        if "mean_abs_residual" in highlights:
            mean_residuals.append(float(highlights["mean_abs_residual"]))
        if "max_abs_drift_velocity" in highlights:
            max_drifts.append(float(highlights["max_abs_drift_velocity"]))
        if "metadata_digest_ok" in highlights:
            metadata.append(bool(highlights["metadata_digest_ok"]))
    summary: Dict[str, object] = {}
    if max_residuals:
        summary["max_abs_residual"] = max(max_residuals)
    if mean_residuals:
        summary["mean_abs_residual"] = sum(mean_residuals) / len(mean_residuals)
    if max_drifts:
        summary["max_abs_drift_velocity"] = max(max_drifts)
    if metadata:
        summary["metadata_digest_ok"] = all(metadata)
    return summary


def _entropy_run_highlights(payload: Mapping[str, object]) -> Dict[str, object]:
    trials = payload.get("trials", [])
    trial_seq: Sequence[object] = trials if isinstance(trials, Sequence) else ()
    slope_low: list[float] = []
    slope_high: list[float] = []
    rho_values: list[float] = []
    p_values: list[float] = []
    for trial in trial_seq:
        if not isinstance(trial, Mapping):
            continue
        ci = trial.get("slope_ci")
        if isinstance(ci, Sequence) and len(ci) >= 2:
            low = _safe_float(ci[0])
            high = _safe_float(ci[1])
            if low is not None:
                slope_low.append(low)
            if high is not None:
                slope_high.append(high)
        rho = _safe_float(trial.get("rho"))
        if rho is not None:
            rho_values.append(rho)
        p_val = _safe_float(trial.get("p_value"))
        if p_val is not None:
            p_values.append(p_val)
    highlights: Dict[str, object] = {}
    if slope_low:
        highlights["min_slope_ci"] = min(slope_low)
    if slope_high:
        highlights["max_slope_ci"] = max(slope_high)
    if rho_values:
        highlights["min_rho"] = min(rho_values)
    if p_values:
        highlights["max_p_value"] = max(p_values)
    if "metadata_digest_matches" in payload:
        highlights["metadata_digest_ok"] = bool(payload.get("metadata_digest_matches"))
    return highlights


def _entropy_phase_highlights(runs: Sequence[RunResult]) -> Dict[str, object]:
    lows: list[float] = []
    highs: list[float] = []
    rho_values: list[float] = []
    p_values: list[float] = []
    metadata: list[bool] = []
    for run in runs:
        if not isinstance(run.payload, Mapping):
            continue
        highlights = _entropy_run_highlights(run.payload)
        if "min_slope_ci" in highlights:
            lows.append(float(highlights["min_slope_ci"]))
        if "max_slope_ci" in highlights:
            highs.append(float(highlights["max_slope_ci"]))
        if "min_rho" in highlights:
            rho_values.append(float(highlights["min_rho"]))
        if "max_p_value" in highlights:
            p_values.append(float(highlights["max_p_value"]))
        if "metadata_digest_ok" in highlights:
            metadata.append(bool(highlights["metadata_digest_ok"]))
    summary: Dict[str, object] = {}
    if lows:
        summary["min_slope_ci"] = min(lows)
    if highs:
        summary["max_slope_ci"] = max(highs)
    if rho_values:
        summary["min_rho"] = min(rho_values)
    if p_values:
        summary["max_p_value"] = max(p_values)
    if metadata:
        summary["metadata_digest_ok"] = all(metadata)
    return summary


def _cwd_highlights(payload: Mapping[str, object]) -> Dict[str, object]:
    penalty_checks = payload.get("penalty_checks", [])
    check_seq: Sequence[object] = penalty_checks if isinstance(penalty_checks, Sequence) else ()
    margins: list[float] = []
    penalties: list[float] = []
    destroyed_flags: list[bool] = []
    for check in check_seq:
        if not isinstance(check, Mapping):
            continue
        diff = _safe_float(check.get("diff_bits"))
        mi = _safe_float(check.get("mutual_information_bits"))
        if diff is not None and mi is not None:
            margins.append(diff - mi)
        penalty = _safe_float(check.get("penalty_bits_blind"))
        if penalty is not None:
            penalties.append(penalty)
        if check.get("error") == "destroyed_success_rate_too_high":
            destroyed_flags.append(True)
    metadata_matches = payload.get("metadata_digest_matches")
    metadata_ok: bool | None
    if isinstance(metadata_matches, Mapping):
        metadata_ok = all(bool(flag) for flag in metadata_matches.values())
    else:
        metadata_ok = None
    highlights: Dict[str, object] = {}
    if margins:
        highlights["min_penalty_margin_bits"] = min(margins)
    if penalties:
        highlights["min_blind_penalty_bits"] = min(penalties)
    if metadata_ok is not None:
        highlights["metadata_digest_ok"] = metadata_ok
    if destroyed_flags:
        highlights["destroyed_guard_triggered"] = True
    return highlights


def _cross_domain_run_highlights(payload: Mapping[str, object], protocol: str) -> Dict[str, object]:
    trials = payload.get("trials", [])
    trial_seq: Sequence[object] = trials if isinstance(trials, Sequence) else ()
    highlights: Dict[str, object] = {}
    delta_aics: list[float] = []
    slopes: list[float] = []
    structures: list[float] = []
    for trial in trial_seq:
        if not isinstance(trial, Mapping):
            continue
        summary = trial.get("summary")
        if not isinstance(summary, Mapping):
            continue
        if "domain_delta_aic" in summary:
            value = _safe_float(summary.get("domain_delta_aic"))
            if value is not None:
                delta_aics.append(value)
        if "domain_slope" in summary:
            slope_val = _safe_float(summary.get("domain_slope"))
            if slope_val is not None:
                slopes.append(slope_val)
        if "structure_integrity" in summary:
            structure_val = _safe_float(summary.get("structure_integrity"))
            if structure_val is not None:
                structures.append(structure_val)
    if protocol == "blind" and delta_aics:
        highlights["min_delta_aic"] = min(delta_aics)
    if protocol == "sighted" and slopes:
        highlights["max_abs_slope"] = max(abs(value) for value in slopes)
    if protocol == "destroyed" and structures:
        highlights["mean_structure_integrity"] = sum(structures) / len(structures)
    if "metadata_digest_matches" in payload:
        highlights["metadata_digest_ok"] = bool(payload.get("metadata_digest_matches"))
    return highlights


def _cross_domain_phase_highlights(phase_map: Mapping[str, RunResult]) -> Dict[str, object]:
    summary: Dict[str, object] = {}
    blind = phase_map.get("blind")
    if blind is not None and isinstance(blind.payload, Mapping):
        highlight = _cross_domain_run_highlights(blind.payload, "blind")
        if "min_delta_aic" in highlight:
            summary["blind_min_delta_aic"] = highlight["min_delta_aic"]
    sighted = phase_map.get("sighted")
    if sighted is not None and isinstance(sighted.payload, Mapping):
        highlight = _cross_domain_run_highlights(sighted.payload, "sighted")
        if "max_abs_slope" in highlight:
            summary["sighted_max_abs_slope"] = highlight["max_abs_slope"]
    destroyed = phase_map.get("destroyed")
    if destroyed is not None and isinstance(destroyed.payload, Mapping):
        highlight = _cross_domain_run_highlights(destroyed.payload, "destroyed")
        if "mean_structure_integrity" in highlight:
            summary["destroyed_mean_structure"] = highlight["mean_structure_integrity"]
    metadata = [
        bool(run.payload.get("metadata_digest_matches"))
        for run in phase_map.values()
        if isinstance(run.payload, Mapping) and "metadata_digest_matches" in run.payload
    ]
    if metadata:
        summary["metadata_digest_ok"] = all(metadata)
    return summary


def _public_dataset_highlights(payload: Mapping[str, object]) -> Dict[str, object]:
    protocols = payload.get("protocols", {})
    highlights: Dict[str, object] = {}
    if isinstance(protocols, Mapping):
        for protocol, summary in protocols.items():
            if not isinstance(summary, Mapping):
                continue
            if protocol == "blind" and "delta_aic" in summary:
                value = _safe_float(summary.get("delta_aic"))
                if value is not None:
                    highlights["blind_delta_aic"] = value
            if protocol == "sighted":
                low = _safe_float(summary.get("slope_ci_low"))
                high = _safe_float(summary.get("slope_ci_high"))
                if low is not None and high is not None:
                    highlights["sighted_slope_ci"] = (low, high)
            if protocol == "destroyed":
                rho = _safe_float(summary.get("spearman_rho"))
                if rho is not None:
                    highlights["destroyed_rho"] = rho
    oos = _safe_float(payload.get("oos_median_abs_pct_error"))
    if oos is not None:
        highlights["oos_error"] = oos
    return highlights


def _public_data_phase_highlights(datasets: Sequence[RunResult]) -> Dict[str, object]:
    oos_errors: list[float] = []
    blind_delta_aic: list[float] = []
    destroyed_rho: list[float] = []
    for run in datasets:
        if not isinstance(run.payload, Mapping):
            continue
        highlights = _public_dataset_highlights(run.payload)
        if "oos_error" in highlights:
            oos_errors.append(float(highlights["oos_error"]))
        if "blind_delta_aic" in highlights:
            blind_delta_aic.append(float(highlights["blind_delta_aic"]))
        if "destroyed_rho" in highlights:
            destroyed_rho.append(float(highlights["destroyed_rho"]))
    summary: Dict[str, object] = {}
    summary["dataset_count"] = len(datasets)
    if oos_errors:
        summary["max_oos_error"] = max(oos_errors)
    if blind_delta_aic:
        summary["blind_min_delta_aic"] = min(blind_delta_aic)
    if destroyed_rho:
        summary["destroyed_max_rho"] = max(destroyed_rho)
    return summary


def _turbulence_dataset_highlights(payload: Mapping[str, object]) -> Dict[str, object]:
    highlights: Dict[str, object] = {}
    protocols = payload.get("protocols")
    if not isinstance(protocols, Mapping):
        return highlights
    sighted = protocols.get("sighted") if isinstance(protocols, Mapping) else None
    blind = protocols.get("blind") if isinstance(protocols, Mapping) else None
    destroyed = protocols.get("destroyed") if isinstance(protocols, Mapping) else None
    if isinstance(sighted, Mapping):
        rho = _safe_float(sighted.get("spearman_rho"))
        slope = _safe_float(sighted.get("runtime_slope"))
        if rho is not None:
            highlights["sighted_rho"] = rho
        if slope is not None:
            highlights["sighted_runtime_slope"] = slope
    if isinstance(blind, Mapping):
        delta_aic = _safe_float(blind.get("delta_aic"))
        if delta_aic is not None:
            highlights["blind_delta_aic"] = delta_aic
    if isinstance(destroyed, Mapping) and isinstance(sighted, Mapping):
        sighted_rho = _safe_float(sighted.get("spearman_rho"))
        destroyed_rho = _safe_float(destroyed.get("spearman_rho"))
        if sighted_rho is not None and destroyed_rho is not None:
            highlights["rho_drop"] = sighted_rho - destroyed_rho
    time_count = payload.get("time_count")
    point_count = payload.get("point_count")
    if isinstance(time_count, (int, float)):
        highlights["time_count"] = int(time_count)
    if isinstance(point_count, (int, float)):
        highlights["point_count"] = int(point_count)
    skipped = payload.get("skipped_protocols")
    if isinstance(skipped, Sequence):
        highlights["skipped_protocols"] = list(skipped)
    return highlights


def _turbulence_phase_highlights(runs: Sequence[RunResult]) -> Dict[str, object]:
    dataset_count = len(runs)
    pass_rate = sum(1 for run in runs if run.status) / dataset_count if dataset_count else 1.0
    delta_aics: list[float] = []
    rho_drops: list[float] = []
    time_counts: list[int] = []
    point_counts: list[int] = []
    for run in runs:
        if not isinstance(run.payload, Mapping):
            continue
        highlights = _turbulence_dataset_highlights(run.payload)
        if "blind_delta_aic" in highlights:
            delta_aics.append(float(highlights["blind_delta_aic"]))
        if "rho_drop" in highlights:
            rho_drops.append(float(highlights["rho_drop"]))
        if "time_count" in highlights:
            time_counts.append(int(highlights["time_count"]))
        if "point_count" in highlights:
            point_counts.append(int(highlights["point_count"]))
    summary: Dict[str, object] = {"dataset_count": dataset_count, "pass_rate": pass_rate}
    if delta_aics:
        summary["min_delta_aic"] = min(delta_aics)
    if rho_drops:
        summary["mean_rho_drop"] = sum(rho_drops) / len(rho_drops)
    if time_counts:
        summary["max_time_count"] = max(time_counts)
    if point_counts:
        summary["max_point_count"] = max(point_counts)
    return summary


def _relative(path: Path, root: Path) -> str:
    try:
        return str(path.relative_to(root))
    except ValueError:
        return str(path)


def _discover_by_metadata(root: Path, filename: str) -> Iterable[Path]:
    return sorted(path.parent for path in root.rglob(filename))


def _discover_protocol_runs(root: Path, filename: str) -> Dict[str, Path]:
    runs: Dict[str, Path] = {}
    for metadata_path in root.rglob(filename):
        try:
            with metadata_path.open("r", encoding="utf-8") as handle:
                metadata = json.load(handle)
        except json.JSONDecodeError as exc:  # pragma: no cover - defensive
            raise ValueError(f"Malformed metadata JSON: {metadata_path}: {exc}") from exc
        protocol = str(metadata.get("protocol", "")).lower()
        if not protocol:
            continue
        runs.setdefault(protocol, metadata_path.parent)
    return runs


def _run_landauer(root: Path, verifier_dir: Path, epsilon: float) -> Dict[str, object]:
    run_dirs = list(_discover_by_metadata(root, "landauer_metadata.json"))
    if not run_dirs:
        raise FileNotFoundError("No Landauer runs found in proofpack")
    phase_runs: list[RunResult] = []
    for index, run_dir in enumerate(run_dirs):
        out_path = verifier_dir / f"landauer_{index}.json"
        try:
            _, payload = verify_landauer(run_dir, epsilon=epsilon, out_path=out_path)
            status = bool(payload.get("status"))
            run_result = RunResult(run_dir=run_dir, status=status, verifier_json=out_path, payload=payload)
        except Exception as exc:  # pragma: no cover - exercised via integration tests
            payload = {"status": False, "error": str(exc)}
            run_result = RunResult(
                run_dir=run_dir,
                status=False,
                verifier_json=out_path,
                payload=payload,
                error=str(exc),
            )
        phase_runs.append(run_result)
    phase_highlights = _landauer_phase_highlights(phase_runs)
    return {
        "status": all(run.status for run in phase_runs),
        "runs": [
            {
                "run_dir": _relative(run.run_dir, root),
                "status": run.status,
                "verifier_json": _relative(run.verifier_json, root),
                "trial_count": run.payload.get("trial_count"),
                "error": run.error,
                "highlights": _landauer_run_highlights(run.payload),
            }
            for run in phase_runs
        ],
        "highlights": phase_highlights,
    }


def _run_einstein(root: Path, verifier_dir: Path, delta: float) -> Dict[str, object]:
    run_dirs = list(_discover_by_metadata(root, "einstein_metadata.json"))
    if not run_dirs:
        raise FileNotFoundError("No Einstein runs found in proofpack")
    phase_runs: list[RunResult] = []
    for index, run_dir in enumerate(run_dirs):
        out_path = verifier_dir / f"einstein_{index}.json"
        try:
            _, payload = verify_einstein(run_dir, delta=delta, out_path=out_path)
            status = bool(payload.get("status"))
            run_result = RunResult(run_dir=run_dir, status=status, verifier_json=out_path, payload=payload)
        except Exception as exc:  # pragma: no cover
            payload = {"status": False, "error": str(exc)}
            run_result = RunResult(
                run_dir=run_dir,
                status=False,
                verifier_json=out_path,
                payload=payload,
                error=str(exc),
            )
        phase_runs.append(run_result)
    phase_highlights = _einstein_phase_highlights(phase_runs)
    return {
        "status": all(run.status for run in phase_runs),
        "runs": [
            {
                "run_dir": _relative(run.run_dir, root),
                "status": run.status,
                "verifier_json": _relative(run.verifier_json, root),
                "trial_count": run.payload.get("trial_count"),
                "error": run.error,
                "highlights": _einstein_run_highlights(run.payload),
            }
            for run in phase_runs
        ],
        "highlights": phase_highlights,
    }


def _run_entropy(root: Path, verifier_dir: Path) -> Dict[str, object]:
    run_dirs = list(_discover_by_metadata(root, "entropy_metadata.json"))
    if not run_dirs:
        raise FileNotFoundError("No entropy identity runs found in proofpack")
    phase_runs: list[RunResult] = []
    for index, run_dir in enumerate(run_dirs):
        out_path = verifier_dir / f"entropy_{index}.json"
        try:
            _, payload = verify_entropy(run_dir, out_path=out_path)
            status = bool(payload.get("status"))
            run_result = RunResult(run_dir=run_dir, status=status, verifier_json=out_path, payload=payload)
        except Exception as exc:  # pragma: no cover
            payload = {"status": False, "error": str(exc)}
            run_result = RunResult(
                run_dir=run_dir,
                status=False,
                verifier_json=out_path,
                payload=payload,
                error=str(exc),
            )
        phase_runs.append(run_result)
    phase_highlights = _entropy_phase_highlights(phase_runs)
    return {
        "status": all(run.status for run in phase_runs),
        "runs": [
            {
                "run_dir": _relative(run.run_dir, root),
                "status": run.status,
                "verifier_json": _relative(run.verifier_json, root),
                "trial_count": run.payload.get("trial_count"),
                "error": run.error,
                "highlights": _entropy_run_highlights(run.payload),
            }
            for run in phase_runs
        ],
        "highlights": phase_highlights,
    }


def _run_cwd(root: Path, verifier_dir: Path, epsilon: float, eta: float) -> Dict[str, object]:
    runs = _discover_protocol_runs(root, "cwd_metadata.json")
    required = {"sighted", "blind", "destroyed"}
    missing = sorted(required - runs.keys())
    if missing:
        raise FileNotFoundError(f"Missing CWD runs for protocols: {', '.join(missing)}")
    out_path = verifier_dir / "cwd.json"
    try:
        _, payload = verify_cwd(
            sighted_dir=runs["sighted"],
            blind_dir=runs["blind"],
            destroyed_dir=runs["destroyed"],
            epsilon=epsilon,
            eta=eta,
            out_path=out_path,
        )
        status = bool(payload.get("status"))
        error = None
    except Exception as exc:  # pragma: no cover
        payload = {"status": False, "error": str(exc)}
        status = False
        error = str(exc)
    return {
        "status": status,
        "verifier_json": _relative(out_path, root),
        "protocol_runs": {protocol: _relative(path, root) for protocol, path in runs.items()},
        "error": error,
        "highlights": _cwd_highlights(payload),
    }


def _run_cross_domain(root: Path, verifier_dir: Path, delta_aic: float) -> Dict[str, object]:
    runs = _discover_protocol_runs(root, "cross_domain_metadata.json")
    required = {"sighted", "blind", "destroyed"}
    missing = sorted(required - runs.keys())
    if missing:
        raise FileNotFoundError(
            f"Missing cross-domain runs for protocols: {', '.join(missing)}"
        )
    phase_map: Dict[str, RunResult] = {}
    for protocol, run_dir in sorted(runs.items()):
        out_path = verifier_dir / f"cross_domain_{protocol}.json"
        try:
            _, payload = verify_cross_domain(run_dir, delta_aic_threshold=delta_aic, out_path=out_path)
            status = bool(payload.get("status"))
            run_result = RunResult(run_dir=run_dir, status=status, verifier_json=out_path, payload=payload)
        except Exception as exc:  # pragma: no cover
            payload = {"status": False, "error": str(exc)}
            run_result = RunResult(
                run_dir=run_dir,
                status=False,
                verifier_json=out_path,
                payload=payload,
                error=str(exc),
            )
        phase_map[protocol] = run_result
    phase_highlights = _cross_domain_phase_highlights(phase_map)
    return {
        "status": all(run.status for run in phase_map.values()),
        "runs": [
            {
                "protocol": protocol,
                "run_dir": _relative(runs[protocol], root),
                "status": phase_map[protocol].status,
                "verifier_json": _relative(verifier_dir / f"cross_domain_{protocol}.json", root),
                "error": phase_map[protocol].error,
                "highlights": _cross_domain_run_highlights(phase_map[protocol].payload, protocol),
            }
            for protocol in sorted(phase_map)
        ],
        "highlights": phase_highlights,
    }


def _run_public_spt(
    root: Path,
    verifier_dir: Path,
    spearman_threshold: float,
    pvalue_threshold: float,
    delta_aic: float,
    oos_threshold: float,
) -> Dict[str, object]:
    dataset_dirs = sorted(
        path.parent
        for path in root.rglob("public_spt_metadata.json")
        if path.parent.is_dir()
    )
    if not dataset_dirs:
        return {"status": True, "datasets": [], "highlights": {"dataset_count": 0}}

    datasets: list[RunResult] = []
    for index, dataset_dir in enumerate(dataset_dirs):
        out_path = verifier_dir / f"public_spt_{index}.json"
        try:
            _, payload = verify_public_spt(
                dataset_dir,
                spearman_threshold=spearman_threshold,
                pvalue_threshold=pvalue_threshold,
                delta_aic_threshold=delta_aic,
                oos_threshold=oos_threshold,
                out_path=out_path,
            )
            status = bool(payload.get("status"))
            run_result = RunResult(
                run_dir=dataset_dir,
                status=status,
                verifier_json=out_path,
                payload=payload,
            )
        except Exception as exc:  # pragma: no cover - surfaced in integration tests
            payload = {"status": False, "error": str(exc)}
            run_result = RunResult(
                run_dir=dataset_dir,
                status=False,
                verifier_json=out_path,
                payload=payload,
                error=str(exc),
            )
        datasets.append(run_result)

    phase_highlights = _public_data_phase_highlights(datasets)
    return {
        "status": all(run.status for run in datasets),
        "datasets": [
            {
                "dataset_dir": _relative(run.run_dir, root),
                "status": run.status,
                "verifier_json": _relative(run.verifier_json, root),
                "error": run.error,
                "dataset": run.payload.get("dataset"),
                "highlights": _public_dataset_highlights(run.payload),
            }
            for run in datasets
        ],
        "highlights": phase_highlights,
    }


def _run_turbulence(
    root: Path,
    verifier_dir: Path,
    spearman_threshold: float,
    pvalue_threshold: float,
    delta_aic: float,
    destroyed_rho_drop: float,
) -> Dict[str, object]:
    dataset_dirs = sorted(
        path.parent for path in root.rglob("turbulence_metadata.json") if path.parent.is_dir()
    )
    if not dataset_dirs:
        return {"status": True, "datasets": [], "highlights": {"dataset_count": 0}}

    datasets: list[RunResult] = []
    for index, dataset_dir in enumerate(dataset_dirs):
        out_path = verifier_dir / f"turbulence_{index}.json"
        try:
            _, payload = verify_turbulence(
                dataset_dir,
                spearman_threshold=spearman_threshold,
                pvalue_threshold=pvalue_threshold,
                delta_aic_threshold=delta_aic,
                destroyed_rho_drop=destroyed_rho_drop,
                out_path=out_path,
            )
            status = bool(payload.get("status"))
            run_result = RunResult(
                run_dir=dataset_dir,
                status=status,
                verifier_json=out_path,
                payload=payload,
            )
        except Exception as exc:  # pragma: no cover - surfaced in integration tests
            payload = {"status": False, "error": str(exc)}
            run_result = RunResult(
                run_dir=dataset_dir,
                status=False,
                verifier_json=out_path,
                payload=payload,
                error=str(exc),
            )
        datasets.append(run_result)

    phase_highlights = _turbulence_phase_highlights(datasets)
    return {
        "status": all(run.status for run in datasets),
        "datasets": [
            {
                "dataset_dir": _relative(run.run_dir, root),
                "status": run.status,
                "verifier_json": _relative(run.verifier_json, root),
                "error": run.error,
                "dataset": run.payload.get("dataset"),
                "highlights": _turbulence_dataset_highlights(run.payload),
            }
            for run in datasets
        ],
        "highlights": phase_highlights,
    }


def verify_proofpack(
    proofpack_dir: Path,
    *,
    epsilon: float = 0.05,
    delta: float = 0.05,
    eta: float = 0.05,
    delta_aic: float = 10.0,
    spearman_threshold: float = 0.9,
    pvalue_threshold: float = 1e-6,
    oos_threshold: float = 0.1,
) -> Dict[str, object]:
    """Run all verifiers for ``proofpack_dir`` and aggregate the results."""

    proofpack_dir = Path(proofpack_dir)
    if not proofpack_dir.exists() or not proofpack_dir.is_dir():
        raise FileNotFoundError(f"Proofpack directory does not exist: {proofpack_dir}")

    verifier_dir = proofpack_dir / "verifier"
    verifier_dir.mkdir(parents=True, exist_ok=True)

    phases: MutableMapping[str, Mapping[str, object]] = {}

    phases["landauer"] = _run_landauer(proofpack_dir, verifier_dir, epsilon=epsilon)
    phases["einstein"] = _run_einstein(proofpack_dir, verifier_dir, delta=delta)
    phases["entropy"] = _run_entropy(proofpack_dir, verifier_dir)
    phases["cwd"] = _run_cwd(proofpack_dir, verifier_dir, epsilon=epsilon, eta=eta)
    phases["cross_domain"] = _run_cross_domain(
        proofpack_dir, verifier_dir, delta_aic=delta_aic
    )
    public_data = _run_public_spt(
        proofpack_dir,
        verifier_dir,
        spearman_threshold=spearman_threshold,
        pvalue_threshold=pvalue_threshold,
        delta_aic=delta_aic,
        oos_threshold=oos_threshold,
    )

    turbulence = _run_turbulence(
        proofpack_dir,
        verifier_dir,
        spearman_threshold=spearman_threshold,
        pvalue_threshold=pvalue_threshold,
        delta_aic=delta_aic,
        destroyed_rho_drop=0.2,
    )

    overall_status = (
        all(phase["status"] for phase in phases.values())
        and public_data["status"]
        and turbulence["status"]
    )

    aggregated = {
        "status": overall_status,
        "epsilon": epsilon,
        "delta": delta,
        "eta": eta,
        "delta_aic": delta_aic,
        "spearman_threshold": spearman_threshold,
        "pvalue_threshold": pvalue_threshold,
        "oos_threshold": oos_threshold,
        "phases": phases,
        "public_data": public_data,
        "turbulence": turbulence,
    }

    verdict = "THIELE_OK" if overall_status else "THIELE_FAIL"
    ok_flag = verifier_dir / "THIELE_OK"
    fail_flag = verifier_dir / "THIELE_FAIL"
    # Remove stale verdict files so re-runs remain idempotent.
    for flag in (ok_flag, fail_flag):
        if flag.exists():
            flag.unlink()
    verdict_path = verifier_dir / verdict
    with verdict_path.open("w", encoding="utf-8") as handle:
        handle.write(f"{verdict}\n")

    aggregated["verdict"] = verdict
    aggregated["verdict_path"] = str(verdict_path.relative_to(proofpack_dir))

    aggregate_path = verifier_dir / "proofpack_verifier.json"
    with aggregate_path.open("w", encoding="utf-8") as handle:
        json.dump(aggregated, handle, indent=2, sort_keys=True)
        handle.write("\n")

    return aggregated

def _format_highlights(aggregated: Mapping[str, object]) -> str:
    lines: list[str] = []
    phases = aggregated.get("phases", {})
    if isinstance(phases, Mapping):
        for name in sorted(phases):
            phase = phases[name]
            highlights = phase.get("highlights") if isinstance(phase, Mapping) else None
            if isinstance(highlights, Mapping) and highlights:
                lines.append(f"{name.replace('_', ' ').title()} highlights:")
                for key, value in sorted(highlights.items()):
                    label = key.replace('_', ' ')
                    lines.append(f"  - {label}: {value}")
    public_data = aggregated.get("public_data")
    if isinstance(public_data, Mapping):
        highlights = public_data.get("highlights")
        if isinstance(highlights, Mapping) and highlights:
            lines.append("Public data highlights:")
            for key, value in sorted(highlights.items()):
                label = key.replace('_', ' ')
                lines.append(f"  - {label}: {value}")
        datasets = public_data.get("datasets")
        if isinstance(datasets, Sequence):
            for dataset in datasets:
                if not isinstance(dataset, Mapping):
                    continue
                highlights = dataset.get("highlights")
                if not (isinstance(highlights, Mapping) and highlights):
                    continue
                dataset_name = dataset.get("dataset") or dataset.get("dataset_dir") or "dataset"
                lines.append(f"  Dataset {dataset_name}:")
                for key, value in sorted(highlights.items()):
                    label = key.replace('_', ' ')
                    lines.append(f"    - {label}: {value}")
    return "\n".join(lines)



def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Unified THIELE proofpack verifier")
    parser.add_argument("proofpack_dir", type=Path, help="Directory containing experiment artefacts")
    parser.add_argument("--epsilon", type=float, default=0.05, help="Tolerance for Landauer and CWD checks")
    parser.add_argument("--delta", type=float, default=0.05, help="Tolerance for Einstein relation checks")
    parser.add_argument("--eta", type=float, default=0.05, help="Margin for CWD penalty bound")
    parser.add_argument(
        "--delta-aic",
        type=float,
        default=10.0,
        dest="delta_aic",
        help="ΔAIC threshold for blind cross-domain runs",
    )
    parser.add_argument(
        "--spearman-threshold",
        type=float,
        default=0.9,
        help="Minimum Spearman ρ for sighted/blind public datasets",
    )
    parser.add_argument(
        "--spearman-p-threshold",
        type=float,
        default=1e-6,
        help="Maximum p-value for public-data correlations",
    )
    parser.add_argument(
        "--oos-threshold",
        type=float,
        default=0.1,
        help="Maximum median absolute percent error for OOS predictions",
    )
    parser.add_argument(
        "--highlights",
        action="store_true",
        help="Print aggregated highlights extracted from verifier payloads",
    )
    return parser


def main(argv: Iterable[str] | None = None) -> None:  # pragma: no cover - CLI wrapper
    parser = _build_parser()
    args = parser.parse_args(argv)
    try:
        result = verify_proofpack(
            args.proofpack_dir,
            epsilon=args.epsilon,
            delta=args.delta,
            eta=args.eta,
            delta_aic=args.delta_aic,
            spearman_threshold=args.spearman_threshold,
            pvalue_threshold=args.spearman_p_threshold,
            oos_threshold=args.oos_threshold,
        )
    except Exception as exc:
        print(f"THIELE_FAIL: {exc}", file=sys.stderr)
        sys.exit(1)

    if args.highlights:
        formatted = _format_highlights(result)
        if formatted:
            print(formatted)

    if result["status"]:
        print("THIELE_OK")
        sys.exit(0)

    print("THIELE_FAIL", file=sys.stderr)
    sys.exit(1)


if __name__ == "__main__":  # pragma: no cover - script entry point
    main()

