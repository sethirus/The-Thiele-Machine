#!/usr/bin/env python3
"""Core utilities for discovering turbulence laws under the NUSD framework."""

from __future__ import annotations

import dataclasses
import itertools
import json
import math
import statistics
from fractions import Fraction
from pathlib import Path
from typing import Dict, List, Mapping, Sequence, Tuple

import numpy as np

try:  # local imports when executed from other tooling
    from tools.nusd_domains import ar1_fit, simulate_turbulence_series
except ModuleNotFoundError:  # pragma: no cover - executed within tools/
    from nusd_domains import ar1_fit, simulate_turbulence_series  # type: ignore


@dataclasses.dataclass
class SeriesBundle:
    """Container for a turbulence time-series and its derived quantities."""

    name: str
    energies: List[float]
    gradients: List[float]

    @classmethod
    def from_seed(cls, seed: int, samples: int) -> "SeriesBundle":
        energies, gradients = simulate_turbulence_series(seed, samples)
        return cls(name=f"synthetic_seed_{seed}", energies=energies, gradients=gradients)

    @classmethod
    def from_dataset(cls, path: Path) -> "SeriesBundle":
        payload = json.loads(path.read_text(encoding="utf-8"))
        values = payload.get("values")
        if not isinstance(values, list) or not values:
            raise ValueError("dataset JSON must provide a non-empty 'values' array")
        energies: List[float] = []
        for frame in values:
            if not isinstance(frame, list):
                raise ValueError("each frame must be a list of velocity vectors")
            frame_energy = 0.0
            count = 0
            for vector in frame:
                if not isinstance(vector, list) or len(vector) != 3:
                    raise ValueError("velocity samples must be 3-vectors")
                frame_energy += 0.5 * sum(component * component for component in vector)
                count += 1
            if count == 0:
                raise ValueError("velocity frame must contain at least one vector")
            energies.append(frame_energy / count)
        gradients: List[float] = []
        for index in range(1, len(energies)):
            gradients.append(energies[index] - energies[index - 1])
        metadata = payload.get("metadata", {})
        label = metadata.get("note") if isinstance(metadata, dict) else None
        name = str(path)
        if label:
            name = f"{name}::{label}"
        return cls(name=name, energies=energies, gradients=gradients)


@dataclasses.dataclass
class LawCandidate:
    """Represents a symbolic turbulence law."""

    terms: Tuple[str, ...]
    intercept: Fraction
    coefficients: Tuple[Fraction, ...]
    residual_bits: float
    model_bits: float
    baseline_bits: float

    @property
    def total_bits(self) -> float:
        return self.model_bits + self.residual_bits

    def as_dict(self) -> Dict[str, object]:
        return {
            "terms": list(self.terms),
            "intercept": serialize_fraction(self.intercept),
            "coefficients": [serialize_fraction(value) for value in self.coefficients],
            "model_bits": self.model_bits,
            "residual_bits": self.residual_bits,
            "baseline_bits": self.baseline_bits,
            "total_bits": self.total_bits,
        }


@dataclasses.dataclass
class EvaluationResult:
    """Performance of a law on an unseen dataset."""

    bundle: SeriesBundle
    residual_bits: float
    baseline_bits: float
    delta_vs_baseline: float

    def as_dict(self) -> Dict[str, object]:
        return {
            "series": self.bundle.name,
            "residual_bits": self.residual_bits,
            "baseline_bits": self.baseline_bits,
            "delta_vs_baseline": self.delta_vs_baseline,
        }


def serialize_fraction(value: Fraction) -> Dict[str, int]:
    return {"numerator": value.numerator, "denominator": value.denominator}


def _basis_values(current: float, previous: float, older: float) -> Mapping[str, float]:
    gradient = current - previous
    gradient_prev = previous - older
    cascade = gradient - gradient_prev
    average_energy = 0.5 * (current + previous)
    squared_gradient = gradient * gradient
    abs_gradient = abs(gradient)
    return {
        "E_t": current,
        "E_t_minus_1": previous,
        "gradient": gradient,
        "gradient_prev": gradient_prev,
        "cascade": cascade,
        "grad_sq": squared_gradient,
        "grad_abs": abs_gradient,
        "grad_energy": gradient * average_energy,
        "avg_energy": average_energy,
    }


def _design_matrix(energies: Sequence[float], terms: Sequence[str]) -> Tuple[np.ndarray, np.ndarray]:
    if len(energies) < 4:
        raise ValueError("need at least four samples to build the design matrix")
    rows: List[List[float]] = []
    targets: List[float] = []
    for index in range(2, len(energies) - 1):
        older = energies[index - 2]
        previous = energies[index - 1]
        current = energies[index]
        next_value = energies[index + 1]
        basis = _basis_values(current, previous, older)
        row = [1.0]  # intercept column
        for term in terms:
            if term not in basis:
                raise ValueError(f"unknown basis term {term}")
            row.append(basis[term])
        rows.append(row)
        targets.append(next_value)
    return np.array(rows, dtype=float), np.array(targets, dtype=float)


def _solve_model(matrix: np.ndarray, targets: np.ndarray) -> Tuple[float, ...]:
    solution, *_ = np.linalg.lstsq(matrix, targets, rcond=None)
    return tuple(float(value) for value in solution)


def _mdl_for_coefficients(coefficients: Sequence[Fraction]) -> float:
    penalty = 0.0
    for coeff in coefficients:
        penalty += math.log2(1.0 + abs(coeff.numerator))
        penalty += math.log2(1.0 + coeff.denominator)
    return penalty


def _mdl_for_residuals(residuals: Sequence[float]) -> float:
    energy = sum(value * value for value in residuals)
    return math.log2(1.0 + energy)


def _baseline_bits(targets: Sequence[float]) -> float:
    if len(targets) == 0:
        return 0.0
    mean_future = statistics.mean(targets)
    residuals = [value - mean_future for value in targets]
    return _mdl_for_residuals(residuals)


def _approximate_fraction(value: float, max_denominator: int = 1024) -> Fraction:
    return Fraction(value).limit_denominator(max_denominator)


def _evaluate_combination(energies: Sequence[float], terms: Tuple[str, ...]) -> LawCandidate:
    matrix, targets = _design_matrix(energies, terms)
    coefficients = _solve_model(matrix, targets)
    intercept_fraction = _approximate_fraction(coefficients[0])
    coeff_fractions = tuple(_approximate_fraction(value) for value in coefficients[1:])
    predictions = matrix @ np.array([float(intercept_fraction)] + [float(value) for value in coeff_fractions])
    residuals = [target - prediction for target, prediction in zip(targets, predictions)]
    residual_bits = _mdl_for_residuals(residuals)
    model_bits = _mdl_for_coefficients((intercept_fraction,) + coeff_fractions)
    baseline_bits = _baseline_bits(targets)
    return LawCandidate(terms, intercept_fraction, coeff_fractions, residual_bits, model_bits, baseline_bits)


def search_law(
    bundles: Sequence[SeriesBundle],
    *,
    max_terms: int = 3,
) -> LawCandidate:
    """Search for the lowest-MDL turbulence law over the provided bundles."""

    if not bundles:
        raise ValueError("need at least one series bundle")
    candidate_terms = [
        "E_t",
        "E_t_minus_1",
        "gradient",
        "gradient_prev",
        "cascade",
        "grad_sq",
        "grad_abs",
        "grad_energy",
        "avg_energy",
    ]
    aggregated: List[float] = []
    for bundle in bundles:
        aggregated.extend(bundle.energies)
    best_candidate: LawCandidate | None = None
    for term_count in range(1, max_terms + 1):
        for combination in itertools.combinations(candidate_terms, term_count):
            candidate = _evaluate_combination(aggregated, combination)
            if best_candidate is None or candidate.total_bits < best_candidate.total_bits:
                best_candidate = candidate
    assert best_candidate is not None
    return best_candidate


def evaluate_law(candidate: LawCandidate, bundle: SeriesBundle) -> EvaluationResult:
    terms = candidate.terms
    intercept = float(candidate.intercept)
    coeffs = [float(value) for value in candidate.coefficients]
    matrix, targets = _design_matrix(bundle.energies, terms)
    predictions = matrix @ np.array([intercept] + coeffs)
    residuals = [target - prediction for target, prediction in zip(targets, predictions)]
    residual_bits = _mdl_for_residuals(residuals)
    baseline_bits = _baseline_bits(targets)
    return EvaluationResult(
        bundle=bundle,
        residual_bits=residual_bits,
        baseline_bits=baseline_bits,
        delta_vs_baseline=baseline_bits - residual_bits,
    )


def ar1_baseline(bundle: SeriesBundle) -> LawCandidate:
    energies = bundle.energies
    slope, intercept = ar1_fit(energies)
    intercept_fraction = _approximate_fraction(intercept)
    slope_fraction = _approximate_fraction(slope)
    matrix, targets = _design_matrix(energies, ("E_t",))
    predictions = matrix @ np.array([float(intercept_fraction), float(slope_fraction)])
    residuals = [target - prediction for target, prediction in zip(targets, predictions)]
    residual_bits = _mdl_for_residuals(residuals)
    model_bits = _mdl_for_coefficients((intercept_fraction, slope_fraction))
    baseline_bits = _baseline_bits(targets)
    return LawCandidate(("E_t",), intercept_fraction, (slope_fraction,), residual_bits, model_bits, baseline_bits)


def blind_baseline(bits_per_sample: float, bundle: SeriesBundle) -> LawCandidate:
    matrix, targets = _design_matrix(bundle.energies, tuple())
    model_bits = len(targets) * bits_per_sample + math.log2(1.0 + bits_per_sample)
    residual_bits = _baseline_bits(targets)
    intercept = Fraction(0, 1)
    return LawCandidate(tuple(), intercept, tuple(), residual_bits, model_bits, residual_bits)


def summarise_evaluations(results: Sequence[EvaluationResult]) -> Mapping[str, float]:
    if not results:
        return {"count": 0, "mean_delta_bits": 0.0}
    deltas = [result.delta_vs_baseline for result in results]
    return {
        "count": float(len(results)),
        "mean_delta_bits": float(statistics.mean(deltas)),
        "median_delta_bits": float(statistics.median(deltas)),
        "min_delta_bits": float(min(deltas)),
        "max_delta_bits": float(max(deltas)),
    }


def law_expression(candidate: LawCandidate) -> str:
    terms = ["E_{t+1} = "]
    components: List[str] = []
    intercept = candidate.intercept
    if intercept.numerator != 0:
        components.append(f"{float(intercept):+.6f}")
    for name, coefficient in zip(candidate.terms, candidate.coefficients):
        components.append(f"{float(coefficient):+.6f}·{name}")
    if not components:
        components.append("0")
    terms.append(" ".join(components))
    return "".join(terms)


def dataset_digest(bundle: SeriesBundle) -> str:
    payload = json.dumps(bundle.energies, separators=(",", ":"), ensure_ascii=False)
    return _sha256(payload)


def _sha256(payload: str) -> str:
    import hashlib

    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


def bundle_summary(bundle: SeriesBundle) -> Mapping[str, object]:
    return {
        "series": bundle.name,
        "samples": len(bundle.energies),
        "digest": dataset_digest(bundle),
        "mean_energy": float(statistics.mean(bundle.energies)) if bundle.energies else 0.0,
        "variance_energy": float(statistics.pvariance(bundle.energies)) if len(bundle.energies) > 1 else 0.0,
    }


def prepare_bundles_from_seeds(seeds: Sequence[int], samples: int) -> List[SeriesBundle]:
    return [SeriesBundle.from_seed(seed, samples) for seed in seeds]


def load_external_bundle(path: Path) -> SeriesBundle:
    return SeriesBundle.from_dataset(path)


__all__ = [
    "SeriesBundle",
    "LawCandidate",
    "EvaluationResult",
    "search_law",
    "evaluate_law",
    "summarise_evaluations",
    "law_expression",
    "bundle_summary",
    "prepare_bundles_from_seeds",
    "load_external_bundle",
    "ar1_baseline",
    "blind_baseline",
    "serialize_fraction",
    "dataset_digest",
]
