"""Discover compact self-laws from Thiele VM runtime traces."""

from __future__ import annotations

import hashlib
import json
import math
import statistics
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Mapping, Sequence

DEFAULT_TRACE_INDEX = Path("artifacts/self_traces/self_trace_index.json")
BLIND_BITS_PER_STEP = 8.0
DEFAULT_EPSILON_BITS = 0.05


@dataclass
class TraceSample:
    workload: str
    step: int
    op: str
    pc: int
    mu_total: float
    mu_operational: float
    mu_information: float
    delta_mu_total: float
    delta_mu_operational: float
    delta_mu_information: float


def load_trace_index(index_path: Path = DEFAULT_TRACE_INDEX) -> Mapping[str, object]:
    if not index_path.exists():
        raise FileNotFoundError(f"trace index {index_path} is missing")
    return json.loads(index_path.read_text(encoding="utf-8"))


def _load_trace_events(path: Path) -> List[Mapping[str, object]]:
    events: List[Mapping[str, object]] = []
    with path.open(encoding="utf-8") as handle:
        for line in handle:
            line = line.strip()
            if not line:
                continue
            events.append(json.loads(line))
    return events


def _samples_from_trace(entry: Mapping[str, object]) -> List[TraceSample]:
    path = Path(entry["path"])
    workload = str(entry.get("workload", path.stem))
    events = _load_trace_events(path)
    samples: List[TraceSample] = []
    for event in events:
        if event.get("event") != "trace_step":
            continue
        mu_payload = event.get("mu", {})
        delta_payload = event.get("delta", {})
        sample = TraceSample(
            workload=workload,
            step=int(event.get("step", len(samples) + 1)),
            op=str(event.get("op", "UNKNOWN")),
            pc=int(event.get("pc", 0)),
            mu_total=float(mu_payload.get("mu_total", 0.0)),
            mu_operational=float(mu_payload.get("mu_operational", 0.0)),
            mu_information=float(mu_payload.get("mu_information", 0.0)),
            delta_mu_total=float(delta_payload.get("mu_total", 0.0)),
            delta_mu_operational=float(delta_payload.get("mu_operational", 0.0)),
            delta_mu_information=float(delta_payload.get("mu_information", 0.0)),
        )
        samples.append(sample)
    return samples


def load_samples(index_payload: Mapping[str, object]) -> List[TraceSample]:
    entries = index_payload.get("traces", [])
    samples: List[TraceSample] = []
    for entry in entries:
        samples.extend(_samples_from_trace(entry))
    if not samples:
        raise ValueError("no trace samples found")
    return samples


def _operation_coefficients(samples: Sequence[TraceSample]) -> Dict[str, float]:
    per_op: Dict[str, List[float]] = {}
    for sample in samples:
        per_op.setdefault(sample.op, []).append(sample.delta_mu_total)
    coefficients: Dict[str, float] = {}
    for op, deltas in per_op.items():
        if not deltas:
            continue
        mean_delta = statistics.fmean(deltas)
        if abs(mean_delta) < 1e-9:
            continue
        coefficients[op] = round(mean_delta, 6)
    return coefficients


def _expression(coefficients: Mapping[str, float]) -> str:
    if not coefficients:
        return "Δμ_total = 0"
    terms = [f"{value:.6f}·[op={op}]" for op, value in coefficients.items()]
    return "Δμ_total = " + " + ".join(terms)


def discover_self_model(
    index_path: Path = DEFAULT_TRACE_INDEX,
    *,
    blind_bits_per_step: float = BLIND_BITS_PER_STEP,
    epsilon_bits: float = DEFAULT_EPSILON_BITS,
) -> Mapping[str, object]:
    index_payload = load_trace_index(index_path)
    samples = load_samples(index_payload)
    coefficients = _operation_coefficients(samples)
    model_bits = 8.0 * (1 + len(coefficients))

    residual_bits = 0.0
    squared_errors: Dict[str, List[float]] = {}
    for sample in samples:
        predicted = coefficients.get(sample.op, 0.0)
        error = sample.delta_mu_total - predicted
        squared_errors.setdefault(sample.workload, []).append(error * error)
        residual_bits += math.log2(1.0 + error * error)

    mu_total_bits = model_bits + residual_bits - epsilon_bits
    blind_total_bits = len(samples) * blind_bits_per_step
    mu_gap_bits = blind_total_bits - mu_total_bits

    workloads = sorted({sample.workload for sample in samples})
    workload_metrics: Dict[str, Mapping[str, float]] = {}
    if workloads:
        question_share = model_bits / len(workloads)
        epsilon_share = epsilon_bits / len(workloads)
    else:
        question_share = model_bits
        epsilon_share = epsilon_bits
    for workload in workloads:
        errors = squared_errors.get(workload, [])
        blind_bits = len(errors) * blind_bits_per_step
        residual_share = sum(math.log2(1.0 + err) for err in errors)
        mu_total_share = question_share + residual_share - epsilon_share
        rmse = math.sqrt(sum(errors) / len(errors)) if errors else 0.0
        workload_metrics[workload] = {
            "samples": float(len(errors)),
            "blind_total_bits": blind_bits,
            "mu_question_bits": question_share,
            "mu_answer_bits": residual_share,
            "mu_total_bits": mu_total_share,
            "mu_gap_bits": blind_bits - mu_total_share,
            "rmse": rmse,
        }

    summary: Dict[str, object] = {
        "coefficients": coefficients,
        "expression": _expression(coefficients),
        "mu_question_bits": model_bits,
        "mu_answer_bits": residual_bits,
        "mu_total_bits": mu_total_bits,
        "mu_gap_bits": mu_gap_bits,
        "blind_bits_per_step": blind_bits_per_step,
        "blind_total_bits": blind_total_bits,
        "epsilon_bits": epsilon_bits,
        "workloads": workload_metrics,
        "samples": len(samples),
        "unique_ops": sorted(coefficients.keys()),
        "trace_index": {
            "path": str(index_path),
            "sha256": hashlib.sha256(index_path.read_bytes()).hexdigest(),
            "entries": len(index_payload.get("traces", [])),
        },
    }
    return summary


__all__ = [
    "TraceSample",
    "discover_self_model",
    "load_trace_index",
    "load_samples",
    "DEFAULT_TRACE_INDEX",
    "BLIND_BITS_PER_STEP",
    "DEFAULT_EPSILON_BITS",
]
