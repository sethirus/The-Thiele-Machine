"""Symbolic discovery of a turbulence closure law using NUSD MDL accounting."""

from __future__ import annotations

import itertools
import json
import math
import hashlib
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Callable, Dict, List, Mapping, Sequence, Tuple

import numpy as np

try:  # pragma: no cover - module executed as a script within tools/
    from tools.turbulence_law import SeriesBundle, load_external_bundle, prepare_bundles_from_seeds
except ModuleNotFoundError:  # pragma: no cover - execution from repo root
    from turbulence_law import (  # type: ignore
        SeriesBundle,
        load_external_bundle,
        prepare_bundles_from_seeds,
    )


EPSILON = 1e-6


def _structure_penalty(name: str, depth: int) -> float:
    return math.log2(1.0 + len(name)) + 0.5 * depth + 1.0


@dataclass(frozen=True)
class Feature:
    """Symbolic feature that may appear in the closure."""

    name: str
    generator: Callable[[Mapping[str, float]], float]
    depth: int = 0

    @property
    def structure_bits(self) -> float:
        return _structure_penalty(self.name, self.depth)

    def value(self, basis: Mapping[str, float]) -> float:
        value = float(self.generator(basis))
        if not math.isfinite(value):
            return 0.0
        if abs(value) > 1e9:
            return math.copysign(1e9, value)
        return value


def _basis_for_index(energies: Sequence[float], gradients: Sequence[float], index: int) -> Dict[str, float]:
    current = energies[index]
    prev = energies[index - 1]
    prev2 = energies[index - 2]
    prev3 = energies[index - 3]

    grad_prev = gradients[index - 1]
    grad_prev2 = gradients[index - 2]
    grad_prev3 = gradients[index - 3]

    cascade_prev = grad_prev - grad_prev2
    cascade_prev2 = grad_prev2 - grad_prev3

    avg_energy = 0.5 * (current + prev)
    slope_ratio = grad_prev / (EPSILON + abs(prev))
    curvature = cascade_prev - cascade_prev2

    basis = {
        "E_t": current,
        "E_t_minus_1": prev,
        "E_t_minus_2": prev2,
        "E_t_minus_3": prev3,
        "grad_prev": grad_prev,
        "grad_prev2": grad_prev2,
        "grad_prev3": grad_prev3,
        "grad_abs": abs(grad_prev),
        "grad_sq": grad_prev * grad_prev,
        "cascade_prev": cascade_prev,
        "cascade_prev2": cascade_prev2,
        "curvature": curvature,
        "avg_energy": avg_energy,
        "energy_gradient": avg_energy * grad_prev,
        "strain_like": abs(grad_prev) / (EPSILON + math.sqrt(abs(avg_energy) + EPSILON)),
        "slope_ratio": slope_ratio,
        "cascade_ratio": cascade_prev / (EPSILON + abs(grad_prev2)),
        "grad_ratio": grad_prev / (EPSILON + abs(grad_prev2)),
        "energy_ratio": current / (EPSILON + abs(prev)),
        "energy_diff": current - prev2,
        "energy_band": current + prev - prev2 - prev3,
        "grad_energy_mix": grad_prev * (current - prev2),
    }
    return basis


BASE_FEATURES: Tuple[Feature, ...] = (
    Feature("grad_prev", lambda b: b["grad_prev"]),
    Feature("grad_prev2", lambda b: b["grad_prev2"]),
    Feature("grad_prev3", lambda b: b["grad_prev3"]),
    Feature("grad_abs", lambda b: b["grad_abs"]),
    Feature("grad_sq", lambda b: b["grad_sq"]),
    Feature("cascade_prev", lambda b: b["cascade_prev"]),
    Feature("cascade_prev2", lambda b: b["cascade_prev2"]),
    Feature("curvature", lambda b: b["curvature"]),
    Feature("avg_energy", lambda b: b["avg_energy"]),
    Feature("energy_gradient", lambda b: b["energy_gradient"]),
    Feature("strain_like", lambda b: b["strain_like"]),
    Feature("slope_ratio", lambda b: b["slope_ratio"]),
    Feature("cascade_ratio", lambda b: b["cascade_ratio"]),
    Feature("grad_ratio", lambda b: b["grad_ratio"]),
    Feature("energy_ratio", lambda b: b["energy_ratio"]),
    Feature("energy_diff", lambda b: b["energy_diff"]),
    Feature("energy_band", lambda b: b["energy_band"]),
    Feature("grad_energy_mix", lambda b: b["grad_energy_mix"]),
)


def _square_feature(feature: Feature) -> Feature:
    return Feature(
        f"{feature.name}^2",
        lambda basis, name=feature.name: basis[name] * basis[name],
        depth=feature.depth + 1,
    )


def _product_feature(lhs: Feature, rhs: Feature) -> Feature:
    ordered = tuple(sorted((lhs.name, rhs.name)))
    return Feature(
        "*".join(ordered),
        lambda basis, a=ordered[0], b=ordered[1]: basis[a] * basis[b],
        depth=max(lhs.depth, rhs.depth) + 1,
    )


DERIVED_FEATURES: Tuple[Feature, ...] = tuple(
    itertools.chain(
        (_square_feature(feature) for feature in BASE_FEATURES if feature.name in {"grad_prev", "avg_energy", "strain_like"}),
        (
            _product_feature(lhs, rhs)
            for lhs, rhs in itertools.combinations(
                [feature for feature in BASE_FEATURES if feature.name in {"grad_prev", "avg_energy", "strain_like", "cascade_prev"}],
                2,
            )
        ),
    )
)


ALL_FEATURES: Tuple[Feature, ...] = BASE_FEATURES + DERIVED_FEATURES


@dataclass
class ClosureCandidate:
    features: Tuple[Feature, ...]
    intercept: Fraction
    coefficients: Tuple[Fraction, ...]
    model_bits: float
    residual_bits: float

    @property
    def total_bits(self) -> float:
        return self.model_bits + self.residual_bits

    def expression(self) -> str:
        if not self.features:
            return f"grad_next = {self.intercept.numerator}/{self.intercept.denominator}"
        coeffs = [float(value) for value in self.coefficients]
        terms = [feature.name for feature in self.features]
        pieces = [f"{coeff:+.6g}·{term}" for coeff, term in zip(coeffs, terms)]
        return f"grad_next = {float(self.intercept):+.6g} " + " ".join(pieces)


@dataclass
class BaselineResult:
    name: str
    mu_question_bits: float
    mu_answer_bits: float
    mu_total_bits: float
    rmse: float

    def as_dict(self) -> Mapping[str, float | str]:
        return {
            "name": self.name,
            "mu_question_bits": self.mu_question_bits,
            "mu_answer_bits": self.mu_answer_bits,
            "mu_total_bits": self.mu_total_bits,
            "rmse": self.rmse,
        }


def _mdl_for_coefficients(values: Sequence[Fraction]) -> float:
    penalty = 0.0
    for coeff in values:
        penalty += math.log2(1.0 + abs(coeff.numerator))
        penalty += math.log2(1.0 + coeff.denominator)
    return penalty


def _mdl_for_residuals(residuals: Sequence[float]) -> float:
    array = np.asarray(residuals, dtype=float)
    if array.size == 0:
        return 0.0
    energy = float(np.sum(np.square(array)))
    return math.log2(1.0 + energy)


def _approximate(value: float, max_denominator: int = 64) -> Fraction:
    return Fraction(value).limit_denominator(max_denominator)


def _build_design_matrix(bundle: SeriesBundle) -> Tuple[np.ndarray, np.ndarray, List[Dict[str, float]]]:
    energies = bundle.energies
    gradients = bundle.gradients
    if len(gradients) < 6:
        return np.empty((0, 1)), np.empty((0,)), []
    rows: List[List[float]] = []
    targets: List[float] = []
    bases: List[Dict[str, float]] = []
    for index in range(3, len(gradients)):
        basis = _basis_for_index(energies, gradients, index)
        rows.append([1.0])
        targets.append(gradients[index])
        bases.append(basis)
    return np.array(rows, dtype=float), np.array(targets, dtype=float), bases


def _evaluate_candidate(
    bases: Sequence[Mapping[str, float]],
    targets: Sequence[float],
    feature_set: Tuple[Feature, ...],
) -> Tuple[Fraction, Tuple[Fraction, ...], float, Sequence[float]]:
    if not bases:
        intercept = Fraction(0)
        return intercept, tuple(), 0.0, []
    matrix = np.ones((len(bases), len(feature_set) + 1), dtype=float)
    for row, basis in enumerate(bases):
        for column, feature in enumerate(feature_set, start=1):
            matrix[row, column] = feature.value(basis)
    solution, *_ = np.linalg.lstsq(matrix, np.asarray(targets, dtype=float), rcond=None)
    intercept = _approximate(float(solution[0]))
    coefficients = tuple(_approximate(float(value)) for value in solution[1:])
    coeff_vector = np.array([float(intercept)] + [float(value) for value in coefficients])
    predictions = matrix @ coeff_vector
    residuals = [float(target - prediction) for target, prediction in zip(targets, predictions)]
    residual_bits = _mdl_for_residuals(residuals)
    return intercept, coefficients, residual_bits, residuals


def _aggregate_bases(bundles: Sequence[SeriesBundle]) -> Tuple[List[Mapping[str, float]], List[float]]:
    bases: List[Mapping[str, float]] = []
    targets: List[float] = []
    for bundle in bundles:
        _, bundle_targets, bundle_bases = _build_design_matrix(bundle)
        bases.extend(bundle_bases)
        targets.extend(float(value) for value in bundle_targets)
    return bases, targets


def _baseline_blind(targets: Sequence[float], bits_per_sample: float) -> BaselineResult:
    sample_count = len(targets)
    if sample_count == 0:
        return BaselineResult("blind", 0.0, 0.0, 0.0, 0.0)
    mu_question = sample_count * bits_per_sample + math.log2(1.0 + bits_per_sample)
    mean_future = float(np.mean(targets))
    residuals = np.asarray(targets, dtype=float) - mean_future
    mu_answer = _mdl_for_residuals(residuals)
    rmse = float(np.sqrt(np.mean(np.square(residuals)))) if sample_count else 0.0
    return BaselineResult("blind", mu_question, mu_answer, mu_question + mu_answer, rmse)


def _baseline_ar(series: Sequence[float], order: int) -> Tuple[float, float, Sequence[float]]:
    if len(series) <= order:
        return 0.0, 0.0, []
    matrix = []
    targets = []
    for index in range(order, len(series)):
        matrix.append([series[index - k - 1] for k in range(order)])
        targets.append(series[index])
    matrix_np = np.asarray(matrix, dtype=float)
    targets_np = np.asarray(targets, dtype=float)
    coeffs, *_ = np.linalg.lstsq(matrix_np, targets_np, rcond=None)
    intercept = float(np.mean(targets_np) - np.dot(np.mean(matrix_np, axis=0), coeffs))
    predictions = matrix_np @ coeffs + intercept
    residuals = targets_np - predictions
    coeff_fracs = tuple(_approximate(float(value)) for value in coeffs)
    mu_q = _mdl_for_coefficients(( _approximate(intercept),) + coeff_fracs)
    mu_a = _mdl_for_residuals(residuals)
    return mu_q, mu_a, residuals


def _baseline_smag(series: Sequence[float], energies: Sequence[float]) -> BaselineResult:
    if len(series) < 3:
        return BaselineResult("smagorinsky", 0.0, 0.0, 0.0, 0.0)
    gradients = np.asarray(series[:-1], dtype=float)
    energy = np.asarray(energies[1:-1], dtype=float)
    design = np.vstack([gradients, gradients * np.abs(gradients), np.sqrt(np.abs(energy) + EPSILON)]).T
    targets = np.asarray(series[1:], dtype=float)
    coeffs, *_ = np.linalg.lstsq(design, targets, rcond=None)
    predictions = design @ coeffs
    residuals = targets - predictions
    coeff_fracs = tuple(_approximate(float(value)) for value in coeffs)
    mu_q = _mdl_for_coefficients(coeff_fracs)
    mu_a = _mdl_for_residuals(residuals)
    return BaselineResult("smagorinsky", mu_q, mu_a, mu_q + mu_a, float(np.sqrt(np.mean(residuals ** 2))))


def _baseline_nn(series: Sequence[float], features: Sequence[Mapping[str, float]]) -> BaselineResult:
    if len(features) < 4:
        return BaselineResult("tiny_nn", 0.0, 0.0, 0.0, 0.0)
    keys = ["grad_prev", "avg_energy", "strain_like"]
    x = np.array([[basis[key] for key in keys] for basis in features[:-1]], dtype=float)
    y = np.array(series[1:len(x) + 1], dtype=float)
    rng = np.random.default_rng(1337)
    hidden = rng.normal(scale=0.1, size=(3, x.shape[1]))
    hidden_bias = np.zeros(3)
    output = rng.normal(scale=0.1, size=3)
    output_bias = 0.0
    learning_rate = 0.01
    for _ in range(400):
        h = np.tanh((x @ hidden.T) + hidden_bias)
        preds = h @ output + output_bias
        error = preds - y
        grad_output = h.T @ error / len(x)
        grad_output_bias = float(np.mean(error))
        dh = np.outer(error, output) * (1.0 - h**2)
        grad_hidden = dh.T @ x / len(x)
        grad_hidden_bias = np.mean(dh, axis=0)
        output -= learning_rate * grad_output
        output_bias -= learning_rate * grad_output_bias
        hidden -= learning_rate * grad_hidden
        hidden_bias -= learning_rate * grad_hidden_bias
    h = np.tanh((x @ hidden.T) + hidden_bias)
    preds = h @ output + output_bias
    residuals = y - preds
    mu_q = math.log2(1.0 + np.sum(np.abs(hidden))) + math.log2(1.0 + np.sum(np.abs(output)))
    mu_a = _mdl_for_residuals(residuals)
    return BaselineResult("tiny_nn", mu_q, mu_a, mu_q + mu_a, float(np.sqrt(np.mean(residuals ** 2))))


def compute_baselines(bundle: SeriesBundle, blind_bits_per_sample: float) -> List[BaselineResult]:
    _, targets, bases = _build_design_matrix(bundle)
    gradients = bundle.gradients
    if len(gradients) < 6:
        return []
    blind = _baseline_blind(targets, blind_bits_per_sample)
    ar1_model, ar1_residual_bits, ar1_residuals = _baseline_ar(gradients, 1)
    ar1 = BaselineResult(
        "ar1",
        ar1_model,
        ar1_residual_bits,
        ar1_model + ar1_residual_bits,
        float(np.sqrt(np.mean(np.square(ar1_residuals)))) if len(ar1_residuals) else 0.0,
    )
    ar2_model, ar2_residual_bits, ar2_residuals = _baseline_ar(gradients, 2)
    ar2 = BaselineResult(
        "ar2",
        ar2_model,
        ar2_residual_bits,
        ar2_model + ar2_residual_bits,
        float(np.sqrt(np.mean(np.square(ar2_residuals)))) if len(ar2_residuals) else 0.0,
    )
    smag = _baseline_smag(gradients, bundle.energies)
    nn = _baseline_nn(gradients, bases)
    return [blind, ar1, ar2, smag, nn]


def _evaluate_bundle(bundle: SeriesBundle, candidate: ClosureCandidate) -> Dict[str, float]:
    _, targets, bases = _build_design_matrix(bundle)
    if len(targets) == 0:
        return {"mu_answer_bits": 0.0, "rmse": 0.0, "sample_count": 0.0}
    matrix = np.ones((len(bases), len(candidate.features) + 1), dtype=float)
    for row, basis in enumerate(bases):
        for column, feature in enumerate(candidate.features, start=1):
            matrix[row, column] = feature.value(basis)
    coeff_vector = np.array([float(candidate.intercept)] + [float(value) for value in candidate.coefficients])
    predictions = matrix @ coeff_vector
    residuals = np.asarray(targets, dtype=float) - predictions
    return {
        "mu_answer_bits": _mdl_for_residuals(residuals),
        "rmse": float(np.sqrt(np.mean(np.square(residuals)))) if len(residuals) else 0.0,
        "sample_count": float(len(residuals)),
    }


def discover_closure(
    training: Sequence[SeriesBundle],
    evaluation: Sequence[SeriesBundle],
    *,
    max_terms: int,
    min_gain_bits: float,
    blind_bits_per_sample: float,
) -> Tuple[ClosureCandidate, Dict[str, List[BaselineResult]], Dict[str, Dict[str, float]], Dict[str, Dict[str, float]]]:
    bases, targets = _aggregate_bases(training)
    if not targets:
        raise ValueError("training bundles did not produce samples")

    selected: List[Feature] = []
    intercept, coefficients, residual_bits, residuals = _evaluate_candidate(bases, targets, tuple(selected))
    model_bits = _mdl_for_coefficients((intercept,) + coefficients)
    best = ClosureCandidate(tuple(selected), intercept, coefficients, model_bits, residual_bits)

    remaining = [feature for feature in ALL_FEATURES if feature not in selected]
    while len(selected) < max_terms and remaining:
        best_gain = 0.0
        best_feature: Feature | None = None
        best_candidate: ClosureCandidate | None = None
        for feature in remaining:
            trial_features = tuple(selected + [feature])
            trial_intercept, trial_coeffs, trial_residual_bits, _ = _evaluate_candidate(bases, targets, trial_features)
            trial_model_bits = _mdl_for_coefficients((trial_intercept,) + trial_coeffs)
            candidate = ClosureCandidate(trial_features, trial_intercept, trial_coeffs, trial_model_bits, trial_residual_bits)
            gain = best.total_bits - candidate.total_bits - feature.structure_bits
            if gain > best_gain:
                best_gain = gain
                best_feature = feature
                best_candidate = candidate
        if best_feature is None or best_candidate is None or best_gain < min_gain_bits:
            break
        selected.append(best_feature)
        remaining = [feature for feature in remaining if feature is not best_feature]
        best = best_candidate

    training_metrics: Dict[str, Dict[str, float]] = {bundle.name: _evaluate_bundle(bundle, best) for bundle in training}
    evaluation_metrics: Dict[str, Dict[str, float]] = {bundle.name: _evaluate_bundle(bundle, best) for bundle in evaluation}

    baselines: Dict[str, List[BaselineResult]] = {}
    for bundle in itertools.chain(training, evaluation):
        baselines[bundle.name] = compute_baselines(bundle, blind_bits_per_sample=blind_bits_per_sample)

    return best, baselines, training_metrics, evaluation_metrics


def load_dataset(path: Path) -> SeriesBundle:
    return load_external_bundle(path)


def bundle_metadata(bundle: SeriesBundle) -> Mapping[str, object]:
    digest = dataset_digest(bundle)
    return {
        "name": bundle.name,
        "samples": len(bundle.energies),
        "gradients": len(bundle.gradients),
        "digest": digest,
    }


def dataset_digest(bundle: SeriesBundle) -> str:
    payload = {
        "name": bundle.name,
        "energies": bundle.energies[:32],
        "gradients": bundle.gradients[:32],
    }
    return hashlib.sha256(json.dumps(payload, sort_keys=True).encode("utf-8")).hexdigest()


__all__ = [
    "ClosureCandidate",
    "Feature",
    "discover_closure",
    "bundle_metadata",
    "compute_baselines",
    "load_dataset",
    "prepare_bundles_from_seeds",
]
