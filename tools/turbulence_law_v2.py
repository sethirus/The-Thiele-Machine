#!/usr/bin/env python3
"""Symbolic turbulence law search utilities (NUSD Turbulence Law v2)."""

from __future__ import annotations

import dataclasses
import itertools
import json
import math
from fractions import Fraction
from pathlib import Path
from typing import Callable, Dict, Iterable, List, Mapping, MutableMapping, Sequence, Tuple

import numpy as np

try:
    from tools.turbulence_law import SeriesBundle, bundle_summary, dataset_digest
except ModuleNotFoundError:  # pragma: no cover - script execution from tools/
    from turbulence_law import SeriesBundle, bundle_summary, dataset_digest  # type: ignore

# ---------------------------------------------------------------------------
# Feature construction
# ---------------------------------------------------------------------------


def _structure_penalty(name: str, depth: int) -> float:
    return math.log2(1.0 + len(name)) + 1.0 + 0.5 * depth


@dataclasses.dataclass(frozen=True)
class FeatureDefinition:
    """A symbolic feature that may appear in the turbulence law."""

    name: str
    generator: Callable[[Mapping[str, float]], float]
    depth: int = 0

    @property
    def structure_bits(self) -> float:
        return _structure_penalty(self.name, self.depth)

    def value(self, basis: Mapping[str, float]) -> float:
        value = self.generator(basis)
        if not math.isfinite(value):
            return 0.0
        if abs(value) > 1e9:
            return math.copysign(1e9, value)
        return value


def _basis_from_values(older2: float, older: float, previous: float, current: float) -> Dict[str, float]:
    grad_prev2 = older - older2
    grad_prev = previous - older
    grad = current - previous
    cascade = grad - grad_prev
    avg = 0.5 * (current + previous)
    moving_avg3 = (current + previous + older) / 3.0
    moving_var3 = (
        ((current - moving_avg3) ** 2)
        + ((previous - moving_avg3) ** 2)
        + ((older - moving_avg3) ** 2)
    ) / 3.0
    eps = 1e-6
    basis = {
        "E_t": current,
        "E_t_minus_1": previous,
        "E_t_minus_2": older,
        "E_t_minus_3": older2,
        "grad": grad,
        "grad_prev": grad_prev,
        "grad_prev2": grad_prev2,
        "cascade": cascade,
        "avg": avg,
        "moving_avg3": moving_avg3,
        "moving_var3": moving_var3,
        "grad_abs": abs(grad),
        "grad_sq": grad * grad,
        "cascade_sq": cascade * cascade,
        "grad_energy": grad * avg,
        "energy_product": current * previous,
        "grad_ratio": grad / (eps + abs(previous)),
        "cascade_ratio": cascade / (eps + abs(grad_prev)),
        "energy_ratio": current / (eps + abs(previous)),
        "log_energy": math.log1p(abs(current)),
        "sqrt_energy": math.sqrt(abs(current) + eps),
        "inv_energy": 1.0 / (1.0 + abs(current)),
        "grad_prev_ratio": grad_prev / (eps + abs(older)),
        "cross_gradient": grad * grad_prev,
        "cross_cascade": cascade * grad_prev,
    }
    return basis


BASE_FEATURES: Tuple[FeatureDefinition, ...] = (
    FeatureDefinition("E_t", lambda b: b["E_t"]),
    FeatureDefinition("E_t_minus_1", lambda b: b["E_t_minus_1"]),
    FeatureDefinition("E_t_minus_2", lambda b: b["E_t_minus_2"]),
    FeatureDefinition("grad", lambda b: b["grad"]),
    FeatureDefinition("grad_prev", lambda b: b["grad_prev"]),
    FeatureDefinition("cascade", lambda b: b["cascade"]),
    FeatureDefinition("avg", lambda b: b["avg"]),
    FeatureDefinition("moving_avg3", lambda b: b["moving_avg3"]),
    FeatureDefinition("moving_var3", lambda b: b["moving_var3"]),
    FeatureDefinition("grad_abs", lambda b: b["grad_abs"]),
    FeatureDefinition("grad_sq", lambda b: b["grad_sq"]),
    FeatureDefinition("cascade_sq", lambda b: b["cascade_sq"]),
    FeatureDefinition("grad_energy", lambda b: b["grad_energy"]),
    FeatureDefinition("energy_product", lambda b: b["energy_product"]),
    FeatureDefinition("grad_ratio", lambda b: b["grad_ratio"]),
    FeatureDefinition("cascade_ratio", lambda b: b["cascade_ratio"]),
    FeatureDefinition("energy_ratio", lambda b: b["energy_ratio"]),
    FeatureDefinition("log_energy", lambda b: b["log_energy"]),
    FeatureDefinition("sqrt_energy", lambda b: b["sqrt_energy"]),
    FeatureDefinition("inv_energy", lambda b: b["inv_energy"]),
    FeatureDefinition("grad_prev_ratio", lambda b: b["grad_prev_ratio"]),
    FeatureDefinition("cross_gradient", lambda b: b["cross_gradient"]),
    FeatureDefinition("cross_cascade", lambda b: b["cross_cascade"]),
)


def _square_feature(feature: FeatureDefinition) -> FeatureDefinition:
    return FeatureDefinition(
        f"{feature.name}^2",
        lambda basis, name=feature.name: basis[name] * basis[name],
        depth=feature.depth + 1,
    )


def _product_feature(lhs: FeatureDefinition, rhs: FeatureDefinition) -> FeatureDefinition:
    ordered = tuple(sorted((lhs.name, rhs.name)))
    name = "*".join(ordered)
    depth = max(lhs.depth, rhs.depth) + 1
    return FeatureDefinition(
        name,
        lambda basis, a=ordered[0], b=ordered[1]: basis[a] * basis[b],
        depth=depth,
    )


DERIVED_FEATURES: Tuple[FeatureDefinition, ...] = tuple(
    itertools.chain(
        (_square_feature(feature) for feature in BASE_FEATURES if feature.name in {"avg", "grad_energy", "moving_avg3"}),
        (
            _product_feature(lhs, rhs)
            for lhs, rhs in itertools.combinations(
                [feature for feature in BASE_FEATURES if feature.name in {"grad", "cascade", "avg", "grad_energy", "grad_ratio", "inv_energy", "moving_avg3"}],
                2,
            )
        ),
    )
)


ALL_CANDIDATE_FEATURES: Tuple[FeatureDefinition, ...] = BASE_FEATURES + DERIVED_FEATURES

# ---------------------------------------------------------------------------
# Model fitting and MDL accounting
# ---------------------------------------------------------------------------


def _mdl_for_coefficients(coefficients: Sequence[Fraction]) -> float:
    penalty = 0.0
    for coeff in coefficients:
        penalty += math.log2(1.0 + abs(coeff.numerator))
        penalty += math.log2(1.0 + coeff.denominator)
    return penalty


def _mdl_for_residuals(residuals: Sequence[float]) -> float:
    size = len(residuals)
    if size == 0:
        return 0.0
    energy = float(np.sum(np.square(residuals)))
    return math.log2(1.0 + energy)


def _baseline_bits(targets: Sequence[float]) -> float:
    if len(targets) == 0:
        return 0.0
    mean_future = float(np.mean(targets))
    residuals = np.array(targets, dtype=float) - mean_future
    return _mdl_for_residuals(residuals)


def _blind_model_bits(sample_count: int, bits_per_sample: float) -> float:
    if sample_count <= 0:
        return 0.0
    return sample_count * bits_per_sample + math.log2(1.0 + bits_per_sample)


def _approximate_fraction(value: float, max_denominator: int = 64) -> Fraction:
    return Fraction(value).limit_denominator(max_denominator)


@dataclasses.dataclass
class SymbolicLawCandidate:
    terms: Tuple[FeatureDefinition, ...]
    intercept: Fraction
    coefficients: Tuple[Fraction, ...]
    residual_bits: float
    structure_bits: float
    coefficient_bits: float
    baseline_bits: float
    rmse: float
    mae: float
    sample_count: int

    @property
    def model_bits(self) -> float:
        return self.structure_bits + self.coefficient_bits

    @property
    def total_bits(self) -> float:
        return self.model_bits + self.residual_bits

    @property
    def expression(self) -> str:
        pieces: List[str] = ["E_{t+1} = "]
        components: List[str] = []
        if self.intercept.numerator != 0:
            components.append(f"{float(self.intercept):+.6f}")
        for feature, coefficient in zip(self.terms, self.coefficients):
            components.append(f"{float(coefficient):+.6f}·{feature.name}")
        if not components:
            components.append("0")
        pieces.append(" ".join(components))
        return "".join(pieces)

    def as_dict(self) -> Mapping[str, object]:
        return {
            "terms": [feature.name for feature in self.terms],
            "intercept": _fraction_payload(self.intercept),
            "coefficients": [_fraction_payload(value) for value in self.coefficients],
            "residual_bits": self.residual_bits,
            "structure_bits": self.structure_bits,
            "coefficient_bits": self.coefficient_bits,
            "baseline_bits": self.baseline_bits,
            "model_bits": self.model_bits,
            "total_bits": self.total_bits,
            "rmse": self.rmse,
            "mae": self.mae,
            "sample_count": self.sample_count,
            "expression": self.expression,
        }


@dataclasses.dataclass
class EvaluationMetrics:
    bundle: SeriesBundle
    residual_bits: float
    baseline_bits: float
    rmse: float
    mae: float
    spectrum_error: float
    sample_count: int

    @property
    def mu_answer(self) -> float:
        return self.baseline_bits - self.residual_bits

    def as_dict(self) -> Mapping[str, object]:
        return {
            "series": self.bundle.name,
            "residual_bits": self.residual_bits,
            "baseline_bits": self.baseline_bits,
            "mu_gap_bits": self.baseline_bits - self.residual_bits,
            "rmse": self.rmse,
            "mae": self.mae,
            "spectrum_error": self.spectrum_error,
            "sample_count": self.sample_count,
        }


@dataclasses.dataclass
class BaselineMetrics:
    name: str
    mu_question_bits: float
    mu_answer_bits: float
    mu_total_bits: float
    rmse: float
    mae: float

    def as_dict(self) -> Mapping[str, object]:
        return {
            "name": self.name,
            "mu_question_bits": self.mu_question_bits,
            "mu_answer_bits": self.mu_answer_bits,
            "mu_total_bits": self.mu_total_bits,
            "rmse": self.rmse,
            "mae": self.mae,
        }


@dataclasses.dataclass
class DiscoverySummary:
    candidate: SymbolicLawCandidate
    evaluations: List[EvaluationMetrics]
    baselines: Mapping[str, List[BaselineMetrics]]
    training_bundles: List[SeriesBundle]
    evaluation_bundles: List[SeriesBundle]

    def as_dict(self) -> Mapping[str, object]:
        return {
            "candidate": self.candidate.as_dict(),
            "training_bundles": [bundle_summary(bundle) for bundle in self.training_bundles],
            "evaluation_bundles": [bundle_summary(bundle) for bundle in self.evaluation_bundles],
            "evaluations": [metric.as_dict() for metric in self.evaluations],
            "baselines": {key: [baseline.as_dict() for baseline in value] for key, value in self.baselines.items()},
        }


# ---------------------------------------------------------------------------
# Sample preparation
# ---------------------------------------------------------------------------


def _gather_samples(bundle: SeriesBundle) -> Tuple[List[Mapping[str, float]], List[float]]:
    basis_samples: List[Mapping[str, float]] = []
    targets: List[float] = []
    energies = bundle.energies
    if len(energies) < 5:
        return basis_samples, targets
    for index in range(3, len(energies) - 1):
        older2 = energies[index - 3]
        older = energies[index - 2]
        previous = energies[index - 1]
        current = energies[index]
        next_value = energies[index + 1]
        basis_samples.append(_basis_from_values(older2, older, previous, current))
        targets.append(next_value)
    return basis_samples, targets


def _aggregate_samples(bundles: Sequence[SeriesBundle]) -> Tuple[List[Mapping[str, float]], List[float]]:
    basis_samples: List[Mapping[str, float]] = []
    targets: List[float] = []
    for bundle in bundles:
        basis, target = _gather_samples(bundle)
        basis_samples.extend(basis)
        targets.extend(target)
    return basis_samples, targets


# ---------------------------------------------------------------------------
# Model fitting helpers
# ---------------------------------------------------------------------------


def _build_design_matrix(basis_samples: Sequence[Mapping[str, float]], terms: Sequence[FeatureDefinition]) -> np.ndarray:
    rows: List[List[float]] = []
    for basis in basis_samples:
        row = [1.0]
        for feature in terms:
            row.append(feature.value(basis))
        rows.append(row)
    return np.array(rows, dtype=float)


def _solve_least_squares(matrix: np.ndarray, targets: Sequence[float]) -> Tuple[float, ...]:
    solution, *_ = np.linalg.lstsq(matrix, np.array(targets, dtype=float), rcond=None)
    return tuple(float(value) for value in solution)


def _fit_candidate(
    basis_samples: Sequence[Mapping[str, float]],
    targets: Sequence[float],
    terms: Sequence[FeatureDefinition],
    *,
    bits_per_sample: float,
) -> SymbolicLawCandidate:
    if not targets:
        raise ValueError("insufficient samples to fit a law")
    matrix = _build_design_matrix(basis_samples, terms)
    solved = _solve_least_squares(matrix, targets)
    intercept_fraction = _approximate_fraction(solved[0])
    coeffs = tuple(_approximate_fraction(value) for value in solved[1:])
    coeff_vector = np.array([float(intercept_fraction)] + [float(value) for value in coeffs])
    predictions = matrix @ coeff_vector
    residuals = [target - prediction for target, prediction in zip(targets, predictions)]
    residual_bits = _mdl_for_residuals(residuals)
    coefficient_bits = _mdl_for_coefficients((intercept_fraction,) + coeffs)
    structure_bits = sum(feature.structure_bits for feature in terms) + math.log2(1.0 + len(terms))
    baseline_model_bits = _blind_model_bits(len(targets), bits_per_sample)
    baseline_residual_bits = _baseline_bits(targets)
    baseline_bits = baseline_model_bits + baseline_residual_bits
    rmse = float(math.sqrt(np.mean([value * value for value in residuals]))) if residuals else 0.0
    mae = float(np.mean([abs(value) for value in residuals])) if residuals else 0.0
    return SymbolicLawCandidate(
        terms=tuple(terms),
        intercept=intercept_fraction,
        coefficients=coeffs,
        residual_bits=residual_bits,
        structure_bits=structure_bits,
        coefficient_bits=coefficient_bits,
        baseline_bits=baseline_bits,
        rmse=rmse,
        mae=mae,
        sample_count=len(targets),
    )


def greedy_symbolic_search(
    bundles: Sequence[SeriesBundle],
    *,
    candidate_pool: Sequence[FeatureDefinition] | None = None,
    max_terms: int = 4,
    min_gain_bits: float = 0.05,
    bits_per_sample: float = 16.0,
) -> SymbolicLawCandidate:
    """Greedy MDL search for a turbulence law."""

    if not bundles:
        raise ValueError("at least one bundle is required")
    basis_samples, targets = _aggregate_samples(bundles)
    if len(targets) < 8:
        raise ValueError("insufficient aggregated samples for search")
    pool = list(candidate_pool or ALL_CANDIDATE_FEATURES)
    selected: List[FeatureDefinition] = []
    best_candidate = _fit_candidate(basis_samples, targets, selected, bits_per_sample=bits_per_sample)
    while pool and len(selected) < max_terms:
        improvements: List[Tuple[SymbolicLawCandidate, FeatureDefinition]] = []
        for feature in pool:
            candidate_terms = selected + [feature]
            candidate = _fit_candidate(basis_samples, targets, candidate_terms, bits_per_sample=bits_per_sample)
            improvements.append((candidate, feature))
        improvements.sort(key=lambda item: (item[0].total_bits, item[0].residual_bits))
        candidate, feature = improvements[0]
        improves_total = candidate.total_bits + min_gain_bits < best_candidate.total_bits
        improves_residual = candidate.residual_bits + min_gain_bits < best_candidate.residual_bits
        if improves_total or improves_residual:
            selected.append(feature)
            pool.remove(feature)
            best_candidate = candidate
        else:
            break
    return best_candidate


# ---------------------------------------------------------------------------
# Evaluation utilities
# ---------------------------------------------------------------------------


def _bundle_predictions(bundle: SeriesBundle, candidate: SymbolicLawCandidate) -> Tuple[np.ndarray, np.ndarray]:
    basis_samples, targets = _gather_samples(bundle)
    if not targets:
        return np.zeros(0, dtype=float), np.zeros(0, dtype=float)
    matrix = _build_design_matrix(basis_samples, candidate.terms)
    coeff_vector = np.array([float(candidate.intercept)] + [float(value) for value in candidate.coefficients])
    predictions = matrix @ coeff_vector
    return np.array(targets, dtype=float), predictions


def evaluate_candidate(
    bundle: SeriesBundle,
    candidate: SymbolicLawCandidate,
    *,
    bits_per_sample: float,
) -> EvaluationMetrics:
    targets, predictions = _bundle_predictions(bundle, candidate)
    if targets.size == 0:
        return EvaluationMetrics(bundle, 0.0, 0.0, 0.0, 0.0, 0.0, 0)
    residuals = targets - predictions
    residual_bits = _mdl_for_residuals(residuals)
    baseline_bits = _blind_model_bits(len(targets), bits_per_sample) + _baseline_bits(targets)
    rmse = float(math.sqrt(np.mean(residuals ** 2)))
    mae = float(np.mean(np.abs(residuals)))
    actual_fft = np.abs(np.fft.rfft(targets))
    predicted_fft = np.abs(np.fft.rfft(predictions))
    min_len = min(len(actual_fft), len(predicted_fft))
    spectrum_error = float(np.mean(np.abs(actual_fft[:min_len] - predicted_fft[:min_len])))
    return EvaluationMetrics(bundle, residual_bits, baseline_bits, rmse, mae, spectrum_error, targets.size)


# ---------------------------------------------------------------------------
# Baseline computation
# ---------------------------------------------------------------------------


def _fit_linear_baseline(
    bundle: SeriesBundle,
    feature_names: Sequence[str],
    label: str,
    *,
    bits_per_sample: float,
) -> BaselineMetrics:
    basis_samples, targets = _gather_samples(bundle)
    if not targets:
        return BaselineMetrics(label, 0.0, 0.0, 0.0, 0.0, 0.0)
    features = [FeatureDefinition(name, lambda b, n=name: b[n]) for name in feature_names]
    candidate = _fit_candidate(basis_samples, targets, features, bits_per_sample=bits_per_sample)
    return BaselineMetrics(
        name=label,
        mu_question_bits=candidate.model_bits,
        mu_answer_bits=candidate.residual_bits,
        mu_total_bits=candidate.total_bits,
        rmse=candidate.rmse,
        mae=candidate.mae,
    )


def ar_baseline(bundle: SeriesBundle, order: int, *, bits_per_sample: float) -> BaselineMetrics:
    if order == 1:
        return _fit_linear_baseline(bundle, ["E_t"], f"AR(1)", bits_per_sample=bits_per_sample)
    if order == 2:
        return _fit_linear_baseline(bundle, ["E_t", "E_t_minus_1"], f"AR(2)", bits_per_sample=bits_per_sample)
    raise ValueError(f"unsupported AR order {order}")


def smagorinsky_like_baseline(bundle: SeriesBundle, *, bits_per_sample: float) -> BaselineMetrics:
    return _fit_linear_baseline(bundle, ["E_t", "grad_sq"], "Smagorinsky-like", bits_per_sample=bits_per_sample)


def blind_baseline(bundle: SeriesBundle, bits_per_sample: float) -> BaselineMetrics:
    targets = _gather_samples(bundle)[1]
    if not targets:
        return BaselineMetrics("Blind", 0.0, 0.0, 0.0, 0.0, 0.0)
    model_bits = len(targets) * bits_per_sample + math.log2(1.0 + bits_per_sample)
    residual_bits = _baseline_bits(targets)
    rmse = float(np.sqrt(np.mean((targets - np.mean(targets)) ** 2)))
    mae = float(np.mean(np.abs(targets - np.mean(targets))))
    return BaselineMetrics("Blind", model_bits, residual_bits, model_bits + residual_bits, rmse, mae)


def compute_baselines(bundle: SeriesBundle, *, bits_per_sample: float) -> List[BaselineMetrics]:
    return [
        blind_baseline(bundle, bits_per_sample),
        ar_baseline(bundle, 1, bits_per_sample=bits_per_sample),
        ar_baseline(bundle, 2, bits_per_sample=bits_per_sample),
        smagorinsky_like_baseline(bundle, bits_per_sample=bits_per_sample),
    ]


# ---------------------------------------------------------------------------
# Discovery orchestration
# ---------------------------------------------------------------------------


def discover_symbolic_law(
    training_bundles: Sequence[SeriesBundle],
    evaluation_bundles: Sequence[SeriesBundle],
    *,
    max_terms: int = 4,
    min_gain_bits: float = 0.05,
    candidate_pool: Sequence[FeatureDefinition] | None = None,
    blind_bits_per_sample: float = 16.0,
) -> DiscoverySummary:
    candidate = greedy_symbolic_search(
        training_bundles,
        candidate_pool=candidate_pool,
        max_terms=max_terms,
        min_gain_bits=min_gain_bits,
        bits_per_sample=blind_bits_per_sample,
    )
    evaluations: List[EvaluationMetrics] = []
    for bundle in list(training_bundles) + list(evaluation_bundles):
        evaluations.append(evaluate_candidate(bundle, candidate, bits_per_sample=blind_bits_per_sample))
    baseline_map: Dict[str, List[BaselineMetrics]] = {}
    for bundle in list(training_bundles) + list(evaluation_bundles):
        baseline_map[bundle.name] = compute_baselines(bundle, bits_per_sample=blind_bits_per_sample)
    return DiscoverySummary(candidate, evaluations, baseline_map, list(training_bundles), list(evaluation_bundles))


# ---------------------------------------------------------------------------
# Public helpers
# ---------------------------------------------------------------------------


def load_dataset(path: Path) -> SeriesBundle:
    return SeriesBundle.from_dataset(path)


def bundle_metadata(bundle: SeriesBundle) -> Mapping[str, object]:
    summary = dict(bundle_summary(bundle))
    summary["digest"] = dataset_digest(bundle)
    return summary


def _fraction_payload(value: Fraction) -> Mapping[str, int]:
    return {"numerator": value.numerator, "denominator": value.denominator}


__all__ = [
    "FeatureDefinition",
    "SymbolicLawCandidate",
    "EvaluationMetrics",
    "BaselineMetrics",
    "DiscoverySummary",
    "discover_symbolic_law",
    "greedy_symbolic_search",
    "evaluate_candidate",
    "compute_baselines",
    "load_dataset",
    "bundle_metadata",
    "SeriesBundle",
    "ALL_CANDIDATE_FEATURES",
]
