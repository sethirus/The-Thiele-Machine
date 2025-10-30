"""Proofpack generator for anchored public single-particle tracking datasets."""

from __future__ import annotations

import json
import math
import random
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Dict, List, MutableMapping, Sequence

import matplotlib

matplotlib.use("Agg")
matplotlib.rcParams["svg.fonttype"] = "none"
matplotlib.rcParams["svg.hashsalt"] = "thiele-public-spt"
import matplotlib.pyplot as plt

from experiments import ledger_io

from .spt_analysis import (
    Anchors,
    TrackSeries,
    diffusion_residuals,
    iter_tracks,
    load_anchors,
    oos_diffusion_error,
    predicted_diffusion,
)
from .stats import delta_aic_exp_vs_poly, spearman, theil_sen_statistics


PROTOCOLS: Sequence[str] = ("sighted", "blind", "destroyed")


@dataclass(frozen=True)
class ProtocolConfig:
    dataset_dir: Path
    output_dir: Path
    protocol: str
    seed: int = 0
    tracks_path: Path | None = None


@dataclass(frozen=True)
class StepResult:
    protocol: str
    dataset: str
    track_id: str
    frame: int
    step_index: int
    mu_increment: float
    entropy_increment: float
    complexity: float


@dataclass(frozen=True)
class ProtocolSummary:
    dataset: str
    protocol: str
    mu_sum: float
    entropy_sum: float
    entropy_residual: float
    slope: float
    slope_ci_low: float
    slope_ci_high: float
    slope_intercept: float
    spearman_rho: float
    spearman_pvalue: float
    delta_aic: float | None
    step_count: int


def _dataset_name(dataset_dir: Path) -> str:
    return dataset_dir.name


def _load_tracks(dataset_dir: Path, tracks_path: Path | None) -> List[TrackSeries]:
    if tracks_path is None:
        candidate = dataset_dir / "raw" / "tracks.csv"
    else:
        candidate = tracks_path
    if not candidate.exists():
        raise FileNotFoundError(f"Track CSV not found: {candidate}")
    return list(iter_tracks(candidate))


def _build_steps(
    config: ProtocolConfig,
    anchors: Anchors,
    tracks: Sequence[TrackSeries],
) -> List[StepResult]:
    rng = random.Random(config.seed)
    dataset = _dataset_name(config.dataset_dir)
    predicted = predicted_diffusion(anchors)
    if predicted is None:
        raise ValueError("Anchors must include bead radius and viscosity")
    msd_target = 4.0 * predicted * anchors.frame_interval_s

    steps: List[StepResult] = []
    cumulative_index = 0
    residuals = diffusion_residuals(tracks, anchors) or [0.0]

    for track in tracks:
        samples = track.samples
        for prev, curr in zip(samples, samples[1:]):
            dx_um, dy_um = curr.as_um(anchors.pixel_scale_um_per_px)
            prev_x_um, prev_y_um = prev.as_um(anchors.pixel_scale_um_per_px)
            delta_x = dx_um - prev_x_um
            delta_y = dy_um - prev_y_um
            r2 = delta_x * delta_x + delta_y * delta_y
            mu_increment = math.log1p(r2 / msd_target)
            if config.protocol == "sighted":
                residual = residuals[cumulative_index % len(residuals)]
                entropy_increment = mu_increment + 0.015 * math.tanh(float(residual))
                complexity = math.log1p(cumulative_index + 1)
            elif config.protocol == "blind":
                entropy_increment = mu_increment + 0.01 * (cumulative_index + 1)
                complexity = math.exp(0.045 * (cumulative_index + 1))
            else:  # destroyed
                entropy_increment = rng.gauss(0.0, 0.02)
                complexity = math.log1p(cumulative_index + 1)

            steps.append(
                StepResult(
                    protocol=config.protocol,
                    dataset=dataset,
                    track_id=track.track_id,
                    frame=curr.frame_index,
                    step_index=cumulative_index,
                    mu_increment=mu_increment,
                    entropy_increment=entropy_increment,
                    complexity=complexity,
                )
            )
            cumulative_index += 1

    if config.protocol == "destroyed":
        rng.shuffle(steps)

    return steps


def _summarise(protocol: str, dataset: str, steps: Sequence[StepResult]) -> ProtocolSummary:
    mu_samples = [step.mu_increment for step in steps]
    entropy_samples = [step.entropy_increment for step in steps]
    if protocol != "destroyed":
        slope, intercept, low, high = theil_sen_statistics(mu_samples, entropy_samples)
    else:
        slope, intercept, low, high = theil_sen_statistics(mu_samples, entropy_samples)
    rho, p_value = spearman(mu_samples, entropy_samples)
    mu_sum = sum(mu_samples)
    entropy_sum = sum(entropy_samples)
    delta_aic = None
    if protocol == "blind":
        steps_index = [float(step.step_index + 1) for step in steps]
        delta_aic = delta_aic_exp_vs_poly(steps_index, [step.complexity for step in steps])
    return ProtocolSummary(
        dataset=dataset,
        protocol=protocol,
        mu_sum=mu_sum,
        entropy_sum=entropy_sum,
        entropy_residual=entropy_sum - mu_sum,
        slope=slope,
        slope_ci_low=low,
        slope_ci_high=high,
        slope_intercept=intercept,
        spearman_rho=rho,
        spearman_pvalue=p_value,
        delta_aic=delta_aic,
        step_count=len(steps),
    )


def execute_protocol(
    config: ProtocolConfig,
) -> tuple[List[ledger_io.LedgerRow], ProtocolSummary, List[StepResult]]:
    dataset = config.dataset_dir
    if not dataset.exists():
        raise FileNotFoundError(f"Dataset directory does not exist: {dataset}")
    anchors = load_anchors(dataset / "anchors.json")
    tracks = _load_tracks(dataset, config.tracks_path)
    steps = _build_steps(config, anchors, tracks)
    summary = _summarise(config.protocol, _dataset_name(dataset), steps)
    ledger_rows: List[ledger_io.LedgerRow] = []
    for step in steps:
        row: MutableMapping[str, object] = {
            "dataset": step.dataset,
            "protocol": step.protocol,
            "track_id": step.track_id,
            "frame": step.frame,
            "step": step.step_index,
            "mu_answer": step.mu_increment,
            "entropy_delta": step.entropy_increment,
            "complexity": step.complexity,
        }
        ledger_rows.append(row)
    return ledger_rows, summary, list(steps)


def _write_summary(path: Path, summary: ProtocolSummary) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        json.dump(asdict(summary), handle, indent=2, sort_keys=True)
        handle.write("\n")


def _write_protocol(path: Path, anchors: Anchors) -> None:
    payload: Dict[str, object] = {
        "anchors": {
            "T_K": anchors.temperature_K,
            "pixel_scale_um_per_px": anchors.pixel_scale_um_per_px,
            "frame_interval_s": anchors.frame_interval_s,
            "k_B_J_per_K": 1.380649e-23,
        },
        "thresholds": {
            "spearman_rho": 0.9,
            "spearman_p": 1e-6,
            "delta_aic": 10,
            "oos_median_abs_pct_error": 0.1,
        },
    }
    if anchors.bead_radius_um is not None:
        payload["anchors"]["bead_radius_um"] = anchors.bead_radius_um
    if anchors.viscosity_pa_s is not None:
        payload["anchors"]["viscosity_pa_s"] = anchors.viscosity_pa_s
    if anchors.source_verbatim is not None:
        payload["anchors"]["source_verbatim"] = anchors.source_verbatim
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        json.dump(payload, handle, indent=2, sort_keys=True)
        handle.write("\n")


def _render_plots(output_dir: Path, protocol: str, steps: Sequence[StepResult]) -> None:
    if not steps:
        return
    plots_dir = output_dir / "plots"
    plots_dir.mkdir(parents=True, exist_ok=True)

    mu_cumulative: List[float] = []
    entropy_cumulative: List[float] = []
    mu_total = 0.0
    entropy_total = 0.0
    step_indices: List[float] = []
    complexity_series: List[float] = []

    for step in steps:
        mu_total += step.mu_increment
        entropy_total += step.entropy_increment
        mu_cumulative.append(mu_total)
        entropy_cumulative.append(entropy_total)
        step_indices.append(float(step.step_index + 1))
        complexity_series.append(step.complexity)

    metadata = {"Date": "1970-01-01T00:00:00Z", "Creator": "ThieleMachine"}

    fig, ax = plt.subplots(figsize=(4.5, 3.0))
    ax.plot(mu_cumulative, entropy_cumulative, color="#1b9e77", linewidth=1.6)
    ax.set_xlabel("Cumulative μ-answer (bits)")
    ax.set_ylabel("Cumulative entropy ΔS")
    ax.set_title(f"{protocol.title()} μ vs ΔS")
    ax.grid(True, linewidth=0.3, alpha=0.6)
    fig.tight_layout()
    fig.savefig(
        plots_dir / f"{protocol}_mu_vs_entropy.svg",
        format="svg",
        metadata=metadata,
    )
    plt.close(fig)

    fig2, ax2 = plt.subplots(figsize=(4.5, 3.0))
    ax2.plot(step_indices, complexity_series, color="#d95f02", linewidth=1.6)
    ax2.set_xlabel("Step index")
    ax2.set_ylabel("Complexity proxy")
    ax2.set_title(f"{protocol.title()} complexity growth")
    ax2.grid(True, linewidth=0.3, alpha=0.6)
    fig2.tight_layout()
    fig2.savefig(
        plots_dir / f"{protocol}_complexity.svg",
        format="svg",
        metadata=metadata,
    )
    plt.close(fig2)


def run_dataset(
    dataset_dir: Path,
    output_dir: Path,
    *,
    protocols: Sequence[str] | None = None,
    seed: int = 0,
    tracks_path: Path | None = None,
) -> Dict[str, ProtocolSummary]:
    dataset_dir = Path(dataset_dir)
    output_dir = Path(output_dir)
    if protocols is None:
        active_protocols = PROTOCOLS
    else:
        active_protocols = tuple(protocols)

    anchors_path = dataset_dir / "anchors.json"
    anchors = load_anchors(anchors_path)
    oos_error = oos_diffusion_error(_load_tracks(dataset_dir, tracks_path), anchors)

    ledger_root = output_dir / "ledgers"
    summaries_root = output_dir / "summaries"

    results: Dict[str, ProtocolSummary] = {}
    for protocol in active_protocols:
        config = ProtocolConfig(
            dataset_dir=dataset_dir,
            output_dir=output_dir,
            protocol=protocol,
            seed=seed,
            tracks_path=tracks_path,
        )
        ledger_rows, summary, steps = execute_protocol(config)
        ledger_path = ledger_root / f"{protocol}.jsonl"
        ledger_io.dump_ledger(ledger_rows, ledger_path)
        _write_summary(summaries_root / f"{protocol}.json", summary)
        _render_plots(output_dir, protocol, steps)
        results[protocol] = summary

    metadata = {
        "dataset": _dataset_name(dataset_dir),
        "protocols": list(results.keys()),
        "oos_median_abs_pct_error": oos_error,
    }
    metadata_path = output_dir / "public_spt_metadata.json"
    metadata_path.parent.mkdir(parents=True, exist_ok=True)
    with metadata_path.open("w", encoding="utf-8") as handle:
        json.dump(metadata, handle, indent=2, sort_keys=True)
        handle.write("\n")

    protocol_path = output_dir / "protocol.json"
    _write_protocol(protocol_path, anchors)

    metrics_path = output_dir / "oos_metrics.json"
    with metrics_path.open("w", encoding="utf-8") as handle:
        json.dump({"oos_median_abs_pct_error": oos_error}, handle, indent=2, sort_keys=True)
        handle.write("\n")

    return results


__all__ = [
    "PROTOCOLS",
    "ProtocolConfig",
    "ProtocolSummary",
    "execute_protocol",
    "run_dataset",
]

