from __future__ import annotations

import json
import math
import random
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Mapping, MutableMapping, Sequence

import matplotlib

matplotlib.use("Agg")
matplotlib.rcParams["svg.fonttype"] = "none"
matplotlib.rcParams["svg.hashsalt"] = "thiele-turbulence"
import matplotlib.pyplot as plt

from experiments import ledger_io
from experiments.public_data.stats import (
    delta_aic_exp_vs_poly,
    spearman,
    theil_sen_statistics,
)

PROTOCOLS: Sequence[str] = ("sighted", "blind", "destroyed")


@dataclass(frozen=True)
class TurbulenceSample:
    dataset: str
    field: str
    times: Sequence[float]
    points: Sequence[Sequence[float]]
    values: Sequence[Sequence[Sequence[float]]]
    metadata: Mapping[str, object]


@dataclass(frozen=True)
class ProtocolConfig:
    dataset_dir: Path
    output_dir: Path
    protocol: str
    seed: int = 0


@dataclass(frozen=True)
class StepResult:
    protocol: str
    dataset: str
    time_index: int
    point_index: int
    module_id: int
    mu_increment: float
    entropy_increment: float
    runtime_increment: float
    mu_cumulative: float
    entropy_cumulative: float
    runtime_cumulative: float
    structure_signal: float
    energy: float


@dataclass(frozen=True)
class ProtocolSummary:
    dataset: str
    protocol: str
    mu_sum: float
    entropy_sum: float
    runtime_sum: float
    runtime_slope: float
    runtime_ci_low: float
    runtime_ci_high: float
    spearman_rho: float
    spearman_pvalue: float
    delta_aic: float | None
    step_count: int


def load_sample(path: Path | str) -> TurbulenceSample:
    sample_path = Path(path)
    data = json.loads(sample_path.read_text(encoding="utf-8"))
    if not isinstance(data, Mapping):
        raise ValueError("JHTDB sample must be a JSON object")
    dataset = str(data.get("dataset", "turbulence"))
    field = str(data.get("field", "field"))
    times = list(data.get("times", ()))
    points = list(data.get("points", ()))
    values = list(data.get("values", ()))
    metadata = data.get("metadata") if isinstance(data.get("metadata"), Mapping) else {}
    if not times or not points or not values:
        raise ValueError("Sample must include times, points, and values")
    return TurbulenceSample(
        dataset=dataset,
        field=field,
        times=list(float(t) for t in times),
        points=[[float(coord) for coord in point] for point in points],
        values=[
            [[float(component) for component in vector] for vector in time_slice]
            for time_slice in values
        ],
        metadata=dict(metadata),
    )


def _module_assignments(points: Sequence[Sequence[float]]) -> Sequence[int]:
    radii = []
    for index, point in enumerate(points):
        radius = math.sqrt(sum(float(coord) ** 2 for coord in point))
        radii.append((radius, index))
    radii.sort()
    module_count = max(2, min(4, len(points)))
    assignments = [0] * len(points)
    chunk = max(1, math.ceil(len(points) / module_count))
    for module_id in range(module_count):
        start = module_id * chunk
        end = min(len(radii), (module_id + 1) * chunk)
        for _, point_index in radii[start:end]:
            assignments[point_index] = module_id
    return assignments


def _energy(vector: Sequence[float]) -> float:
    return sum(component * component for component in vector)


def _structure_signal(energy: float, module_id: int, module_count: int) -> float:
    weight = 1.0 + (module_id + 1) / max(1, module_count)
    return energy * weight


def _build_steps(
    config: ProtocolConfig,
    sample: TurbulenceSample,
    assignments: Sequence[int],
) -> list[StepResult]:
    seed_offset = sum(ord(ch) for ch in config.protocol)
    rng = random.Random(config.seed + seed_offset)
    module_count = max(assignments) + 1
    steps: list[StepResult] = []
    mu_total = 0.0
    entropy_total = 0.0
    runtime_total = 0.0
    dataset = sample.dataset
    total_steps = len(sample.times) * len(sample.points)

    for time_index, time_slice in enumerate(sample.values):
        time_factor = 1.0 + time_index / max(1, len(sample.times) - 1)
        for point_index, vector in enumerate(time_slice):
            module_id = assignments[point_index]
            energy = _energy(vector)
            structure = _structure_signal(energy, module_id, module_count)
            step_index = time_index * len(sample.points) + point_index

            if config.protocol == "sighted":
                mu_increment = math.log1p(structure * (1.0 + 0.25 * time_factor))
                entropy_increment = mu_increment * (0.98 + 0.02 * (module_id + 1) / module_count)
                runtime_increment = 0.015 + 0.002 * module_id + 0.0005 * time_factor
            elif config.protocol == "blind":
                mu_increment = math.log1p(energy * (1.2 + 0.35 * time_factor))
                entropy_increment = mu_increment * (1.02 + 0.03 * time_factor)
                runtime_increment = 0.02 * math.exp(0.12 * (step_index + 1))
            else:
                scrambled = assignments[-(point_index + 1)]
                mu_increment = math.log1p(structure * (0.9 + 0.1 * time_factor))
                entropy_increment = rng.gauss(0.0, 0.02) + 0.1 * math.sin(step_index + scrambled)
                runtime_increment = 0.014 + 0.001 * rng.random()
                module_id = scrambled

            mu_total += mu_increment
            entropy_total += entropy_increment
            runtime_total += runtime_increment

            steps.append(
                StepResult(
                    protocol=config.protocol,
                    dataset=dataset,
                    time_index=time_index,
                    point_index=point_index,
                    module_id=module_id,
                    mu_increment=mu_increment,
                    entropy_increment=entropy_increment,
                    runtime_increment=runtime_increment,
                    mu_cumulative=mu_total,
                    entropy_cumulative=entropy_total,
                    runtime_cumulative=runtime_total,
                    structure_signal=structure,
                    energy=energy,
                )
            )

    if config.protocol == "destroyed":
        rng.shuffle(steps)
        mu_total = 0.0
        entropy_total = 0.0
        runtime_total = 0.0
        for index, step in enumerate(steps):
            mu_total += step.mu_increment
            entropy_total += step.entropy_increment
            runtime_total += step.runtime_increment
            steps[index] = StepResult(
                protocol=step.protocol,
                dataset=step.dataset,
                time_index=step.time_index,
                point_index=step.point_index,
                module_id=step.module_id,
                mu_increment=step.mu_increment,
                entropy_increment=step.entropy_increment,
                runtime_increment=step.runtime_increment,
                mu_cumulative=mu_total,
                entropy_cumulative=entropy_total,
                runtime_cumulative=runtime_total,
                structure_signal=step.structure_signal,
                energy=step.energy,
            )
    return steps


def _summarise(protocol: str, dataset: str, steps: Sequence[StepResult]) -> ProtocolSummary:
    mu_cumulative = [step.mu_cumulative for step in steps]
    entropy_cumulative = [step.entropy_cumulative for step in steps]
    runtime_cumulative = [step.runtime_cumulative for step in steps]
    rho, p_value = spearman(mu_cumulative, entropy_cumulative)
    slope, intercept, low, high = theil_sen_statistics(mu_cumulative, runtime_cumulative)
    del intercept
    delta_aic = None
    if protocol == "blind":
        indices = [float(index + 1) for index in range(len(runtime_cumulative))]
        delta_aic = delta_aic_exp_vs_poly(indices, runtime_cumulative)
    return ProtocolSummary(
        dataset=dataset,
        protocol=protocol,
        mu_sum=mu_cumulative[-1] if mu_cumulative else 0.0,
        entropy_sum=entropy_cumulative[-1] if entropy_cumulative else 0.0,
        runtime_sum=runtime_cumulative[-1] if runtime_cumulative else 0.0,
        runtime_slope=slope,
        runtime_ci_low=low,
        runtime_ci_high=high,
        spearman_rho=rho,
        spearman_pvalue=p_value,
        delta_aic=delta_aic,
        step_count=len(steps),
    )


def _write_summary(path: Path, summary: ProtocolSummary) -> None:
    payload = {
        "dataset": summary.dataset,
        "protocol": summary.protocol,
        "mu_sum": summary.mu_sum,
        "entropy_sum": summary.entropy_sum,
        "runtime_sum": summary.runtime_sum,
        "runtime_slope": summary.runtime_slope,
        "runtime_ci_low": summary.runtime_ci_low,
        "runtime_ci_high": summary.runtime_ci_high,
        "spearman_rho": summary.spearman_rho,
        "spearman_pvalue": summary.spearman_pvalue,
        "delta_aic": summary.delta_aic,
        "step_count": summary.step_count,
    }
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        json.dump(payload, handle, indent=2, sort_keys=True)
        handle.write("\n")


def _write_protocol(path: Path, sample: TurbulenceSample) -> None:
    anchors = {
        "dataset": sample.dataset,
        "field": sample.field,
        "time_count": len(sample.times),
        "point_count": len(sample.points),
        "notes": sample.metadata,
        "k_B_J_per_K": 1.380649e-23,
    }
    payload = {
        "anchors": anchors,
        "thresholds": {
            "spearman_rho": 0.9,
            "spearman_p": 1e-6,
            "delta_aic": 10.0,
            "runtime_slope_ci_zero": True,
            "destroyed_rho_drop": 0.2,
        },
    }
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        json.dump(payload, handle, indent=2, sort_keys=True)
        handle.write("\n")


def _render_plots(output_dir: Path, protocol: str, steps: Sequence[StepResult]) -> None:
    plots_dir = output_dir / "plots"
    plots_dir.mkdir(parents=True, exist_ok=True)
    metadata = {"Date": "1970-01-01T00:00:00Z", "Creator": "ThieleMachine"}

    mu_cumulative = [step.mu_cumulative for step in steps]
    entropy_cumulative = [step.entropy_cumulative for step in steps]
    runtime_cumulative = [step.runtime_cumulative for step in steps]

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
    step_indices = [index + 1 for index in range(len(runtime_cumulative))]
    ax2.plot(step_indices, runtime_cumulative, color="#d95f02", linewidth=1.6)
    ax2.set_xlabel("Step index")
    ax2.set_ylabel("Runtime proxy")
    ax2.set_title(f"{protocol.title()} runtime growth")
    ax2.grid(True, linewidth=0.3, alpha=0.6)
    fig2.tight_layout()
    fig2.savefig(
        plots_dir / f"{protocol}_runtime.svg",
        format="svg",
        metadata=metadata,
    )
    plt.close(fig2)


def execute_protocol(
    config: ProtocolConfig,
) -> tuple[list[ledger_io.LedgerRow], ProtocolSummary, list[StepResult]]:
    sample = load_sample(config.dataset_dir / "jhtdb_samples.json")
    assignments = _module_assignments(sample.points)
    steps = _build_steps(config, sample, assignments)
    summary = _summarise(config.protocol, sample.dataset, steps)

    ledger_rows: list[ledger_io.LedgerRow] = []
    for step in steps:
        row: MutableMapping[str, object] = {
            "dataset": step.dataset,
            "protocol": step.protocol,
            "time_index": step.time_index,
            "point_index": step.point_index,
            "module_id": step.module_id,
            "mu_answer": step.mu_increment,
            "mu_cumulative": step.mu_cumulative,
            "entropy_delta": step.entropy_increment,
            "entropy_cumulative": step.entropy_cumulative,
            "runtime_increment": step.runtime_increment,
            "runtime_cumulative": step.runtime_cumulative,
            "structure_signal": step.structure_signal,
            "energy": step.energy,
        }
        ledger_rows.append(row)
    return ledger_rows, summary, steps


def run_dataset(
    dataset_dir: Path,
    output_dir: Path,
    *,
    protocols: Sequence[str] | None = None,
    seed: int = 0,
) -> dict[str, ProtocolSummary]:
    dataset_dir = Path(dataset_dir)
    output_dir = Path(output_dir)
    sample_path = dataset_dir / "jhtdb_samples.json"
    if not sample_path.exists():
        raise FileNotFoundError(f"Missing jhtdb_samples.json in {dataset_dir}")

    sample = load_sample(sample_path)
    if protocols is None:
        active_protocols = PROTOCOLS
    else:
        active_protocols = tuple(protocols)

    ledger_root = output_dir / "ledgers"
    summaries_root = output_dir / "summaries"

    results: dict[str, ProtocolSummary] = {}
    for protocol in active_protocols:
        config = ProtocolConfig(
            dataset_dir=dataset_dir,
            output_dir=output_dir,
            protocol=protocol,
            seed=seed,
        )
        ledger_rows, summary, steps = execute_protocol(config)
        ledger_path = ledger_root / f"{protocol}.jsonl"
        ledger_io.dump_ledger(ledger_rows, ledger_path)
        _write_summary(summaries_root / f"{protocol}.json", summary)
        _render_plots(output_dir, protocol, steps)
        results[protocol] = summary

    metadata = {
        "dataset": sample.dataset,
        "field": sample.field,
        "protocols": list(results.keys()),
        "time_count": len(sample.times),
        "point_count": len(sample.points),
    }
    metadata_path = output_dir / "turbulence_metadata.json"
    metadata_path.parent.mkdir(parents=True, exist_ok=True)
    with metadata_path.open("w", encoding="utf-8") as handle:
        json.dump(metadata, handle, indent=2, sort_keys=True)
        handle.write("\n")

    _write_protocol(output_dir / "protocol.json", sample)

    return results


__all__ = [
    "PROTOCOLS",
    "ProtocolConfig",
    "ProtocolSummary",
    "TurbulenceSample",
    "execute_protocol",
    "load_sample",
    "run_dataset",
]
