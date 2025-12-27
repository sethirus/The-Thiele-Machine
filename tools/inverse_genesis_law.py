#!/usr/bin/env python3
"""Inverse Genesis: discover conservation laws (invariants) from raw trajectories.

This module is intentionally self-contained and dependency-light (NumPy only).
It provides:
- Synthetic chaotic double-pendulum dataset generation (RK4)
- Greedy MDL-guided symbolic search for a time-invariant scalar H(q, qdot)

The goal is not to "fit" physics parameters, but to discover an invariant
expression that is (approximately) constant over time while being minimal in
description length.
"""

from __future__ import annotations

import dataclasses
import hashlib
import math
from fractions import Fraction
from typing import Callable, Dict, Iterable, List, Mapping, MutableMapping, Sequence, Tuple

import numpy as np


def _structure_penalty(name: str, depth: int) -> float:
    return math.log2(1.0 + len(name)) + 1.0 + 0.5 * depth


def _mdl_for_coefficients(coefficients: Sequence[Fraction]) -> float:
    penalty = 0.0
    for coeff in coefficients:
        penalty += math.log2(1.0 + abs(coeff.numerator))
        penalty += math.log2(1.0 + coeff.denominator)
    return penalty


def _mdl_for_residuals(residuals: np.ndarray) -> float:
    if residuals.size == 0:
        return 0.0
    energy = float(np.sum(np.square(residuals)))
    return math.log2(1.0 + energy)


def _approximate_fraction(value: float, max_denominator: int = 64) -> Fraction:
    if not math.isfinite(value):
        return Fraction(0, 1)
    # Cap extremes so the rational approximation doesn't explode.
    if abs(value) > 1e9:
        value = math.copysign(1e9, value)
    return Fraction(value).limit_denominator(max_denominator)


def _canonical_json_bytes(material: Mapping[str, object]) -> bytes:
    import json

    return json.dumps(material, sort_keys=True, ensure_ascii=False, separators=(",", ":")).encode("utf-8")


@dataclasses.dataclass(frozen=True)
class DoublePendulumParams:
    m1: float = 1.0
    m2: float = 1.0
    l1: float = 1.0
    l2: float = 1.0
    g: float = 9.81


@dataclasses.dataclass
class DoublePendulumDataset:
    """Raw time series of a double pendulum in generalized coordinates."""

    t: np.ndarray
    theta1: np.ndarray
    theta2: np.ndarray
    omega1: np.ndarray
    omega2: np.ndarray
    params: DoublePendulumParams
    noise_std: float

    def __post_init__(self) -> None:
        n = len(self.t)
        for arr in (self.theta1, self.theta2, self.omega1, self.omega2):
            if len(arr) != n:
                raise ValueError("dataset arrays must have the same length")

    @property
    def samples(self) -> int:
        return int(self.t.size)

    def digest(self) -> str:
        payload = {
            "t": self.t.tolist(),
            "theta1": self.theta1.tolist(),
            "theta2": self.theta2.tolist(),
            "omega1": self.omega1.tolist(),
            "omega2": self.omega2.tolist(),
            "params": dataclasses.asdict(self.params),
            "noise_std": float(self.noise_std),
        }
        return hashlib.sha256(_canonical_json_bytes(payload)).hexdigest()

    def summary(self) -> Mapping[str, object]:
        return {
            "samples": self.samples,
            "digest": self.digest(),
            "dt_mean": float(np.mean(np.diff(self.t))) if self.t.size > 1 else 0.0,
            "noise_std": float(self.noise_std),
            "params": dataclasses.asdict(self.params),
        }


@dataclasses.dataclass(frozen=True)
class DoublePendulumEnsemble:
    """Multiple trajectories used to disambiguate non-trivial invariants.

    With a single trajectory, the constant function is an (unhelpful) invariant.
    Using multiple trajectories with different energy levels forces the discovered
    invariant to vary across the ensemble while remaining constant within each run.
    """

    trajectories: Tuple[DoublePendulumDataset, ...]

    @property
    def samples_total(self) -> int:
        return int(sum(ds.samples for ds in self.trajectories))

    def digest(self) -> str:
        payload = {"digests": [ds.digest() for ds in self.trajectories]}
        return hashlib.sha256(_canonical_json_bytes(payload)).hexdigest()

    def summary(self) -> Mapping[str, object]:
        return {
            "trajectories": [dict(ds.summary()) for ds in self.trajectories],
            "digest": self.digest(),
            "samples_total": self.samples_total,
        }


def _double_pendulum_derivatives(state: np.ndarray, params: DoublePendulumParams) -> np.ndarray:
    """Return [dtheta1, dtheta2, domega1, domega2]."""

    theta1, theta2, omega1, omega2 = state
    m1, m2, l1, l2, g = params.m1, params.m2, params.l1, params.l2, params.g

    delta = theta1 - theta2
    denom = l1 * (2 * m1 + m2 - m2 * math.cos(2 * delta))
    denom2 = l2 * (2 * m1 + m2 - m2 * math.cos(2 * delta))
    if abs(denom) < 1e-12 or abs(denom2) < 1e-12:
        return np.array([omega1, omega2, 0.0, 0.0], dtype=float)

    dtheta1 = omega1
    dtheta2 = omega2

    domega1 = (
        -g * (2 * m1 + m2) * math.sin(theta1)
        - m2 * g * math.sin(theta1 - 2 * theta2)
        - 2 * math.sin(delta) * m2 * (omega2 * omega2 * l2 + omega1 * omega1 * l1 * math.cos(delta))
    ) / denom

    domega2 = (
        2
        * math.sin(delta)
        * (
            omega1 * omega1 * l1 * (m1 + m2)
            + g * (m1 + m2) * math.cos(theta1)
            + omega2 * omega2 * l2 * m2 * math.cos(delta)
        )
    ) / denom2

    return np.array([dtheta1, dtheta2, domega1, domega2], dtype=float)


def simulate_double_pendulum(
    *,
    params: DoublePendulumParams,
    dt: float,
    steps: int,
    theta1_0: float,
    theta2_0: float,
    omega1_0: float,
    omega2_0: float,
    noise_std: float,
    seed: int,
) -> DoublePendulumDataset:
    """Generate a noisy chaotic trajectory via RK4 integration."""

    if dt <= 0:
        raise ValueError("dt must be positive")
    if steps < 16:
        raise ValueError("steps must be at least 16")

    rng = np.random.default_rng(int(seed))

    t = np.linspace(0.0, dt * (steps - 1), steps, dtype=float)
    theta1 = np.zeros(steps, dtype=float)
    theta2 = np.zeros(steps, dtype=float)
    omega1 = np.zeros(steps, dtype=float)
    omega2 = np.zeros(steps, dtype=float)

    state = np.array([theta1_0, theta2_0, omega1_0, omega2_0], dtype=float)

    for i in range(steps):
        theta1[i], theta2[i], omega1[i], omega2[i] = state
        if i == steps - 1:
            break

        k1 = _double_pendulum_derivatives(state, params)
        k2 = _double_pendulum_derivatives(state + 0.5 * dt * k1, params)
        k3 = _double_pendulum_derivatives(state + 0.5 * dt * k2, params)
        k4 = _double_pendulum_derivatives(state + dt * k3, params)
        state = state + (dt / 6.0) * (k1 + 2 * k2 + 2 * k3 + k4)

    if noise_std > 0:
        theta1 = theta1 + rng.normal(0.0, noise_std, size=steps)
        theta2 = theta2 + rng.normal(0.0, noise_std, size=steps)
        omega1 = omega1 + rng.normal(0.0, noise_std, size=steps)
        omega2 = omega2 + rng.normal(0.0, noise_std, size=steps)

    return DoublePendulumDataset(
        t=t,
        theta1=theta1,
        theta2=theta2,
        omega1=omega1,
        omega2=omega2,
        params=params,
        noise_std=float(noise_std),
    )


@dataclasses.dataclass(frozen=True)
class FeatureDefinition:
    name: str
    generator: Callable[[Mapping[str, np.ndarray]], np.ndarray]
    depth: int = 0

    @property
    def structure_bits(self) -> float:
        return _structure_penalty(self.name, self.depth)

    def value(self, basis: Mapping[str, np.ndarray]) -> np.ndarray:
        try:
            value = self.generator(basis)
        except Exception:
            return np.zeros_like(next(iter(basis.values())))
        value = np.asarray(value, dtype=float)
        if value.shape != next(iter(basis.values())).shape:
            return np.zeros_like(next(iter(basis.values())))
        value = np.where(np.isfinite(value), value, 0.0)
        value = np.clip(value, -1e9, 1e9)
        return value


def _basis_for_dataset(dataset: DoublePendulumDataset) -> Mapping[str, np.ndarray]:
    theta1 = dataset.theta1
    theta2 = dataset.theta2
    omega1 = dataset.omega1
    omega2 = dataset.omega2
    delta = theta1 - theta2
    eps = 1e-9

    return {
        "theta1": theta1,
        "theta2": theta2,
        "omega1": omega1,
        "omega2": omega2,
        "delta": delta,
        "cos_theta1": np.cos(theta1),
        "cos_theta2": np.cos(theta2),
        "cos_delta": np.cos(delta),
        "sin_theta1": np.sin(theta1),
        "sin_theta2": np.sin(theta2),
        "sin_delta": np.sin(delta),
        "omega1_sq": omega1 * omega1,
        "omega2_sq": omega2 * omega2,
        "omega1_omega2": omega1 * omega2,
        "omega1_omega2_cos_delta": omega1 * omega2 * np.cos(delta),
        "inv_1_plus_abs_delta": 1.0 / (1.0 + np.abs(delta) + eps),
    }


def _surrogate_signal(basis: Mapping[str, np.ndarray]) -> np.ndarray:
    """A deterministic, purely data-derived signal used to fix the scale.

    We never observe true energy directly. To avoid the degenerate constant
    invariant, we fit coefficients against a weak surrogate built from the raw
    coordinates/velocities; then score invariance by within-trajectory variance.
    """

    # Small weights so this does not dominate the invariance objective.
    return (
        1.0
        + 0.01 * (basis["omega1_sq"] + basis["omega2_sq"])
        + 0.005 * (1.0 - basis["cos_theta1"])
        + 0.005 * (1.0 - basis["cos_theta2"])
    )


BASE_FEATURES: Tuple[FeatureDefinition, ...] = (
    FeatureDefinition("omega1_sq", lambda b: b["omega1_sq"]),
    FeatureDefinition("omega2_sq", lambda b: b["omega2_sq"]),
    FeatureDefinition("omega1_omega2_cos_delta", lambda b: b["omega1_omega2_cos_delta"], depth=1),
    FeatureDefinition("cos_theta1", lambda b: b["cos_theta1"], depth=1),
    FeatureDefinition("cos_theta2", lambda b: b["cos_theta2"], depth=1),
    FeatureDefinition("cos_delta", lambda b: b["cos_delta"], depth=1),
    FeatureDefinition("sin_delta", lambda b: b["sin_delta"], depth=1),
)


@dataclasses.dataclass
class InvariantCandidate:
    terms: Tuple[FeatureDefinition, ...]
    intercept: Fraction
    coefficients: Tuple[Fraction, ...]
    structure_bits: float
    coefficient_bits: float
    residual_bits: float
    baseline_bits: float
    sample_count: int
    mean_abs: float
    std: float

    @property
    def model_bits(self) -> float:
        return self.structure_bits + self.coefficient_bits

    @property
    def total_bits(self) -> float:
        return self.model_bits + self.residual_bits

    @property
    def compression_ratio(self) -> float:
        if self.total_bits <= 0:
            return 0.0
        return float(self.baseline_bits) / float(self.total_bits)

    @property
    def expression(self) -> str:
        pieces: List[str] = ["H(q, qdot) = "]
        parts: List[str] = []
        if self.intercept.numerator != 0:
            parts.append(f"{float(self.intercept):+.6f}")
        for feature, coefficient in zip(self.terms, self.coefficients):
            parts.append(f"{float(coefficient):+.6f}·{feature.name}")
        if not parts:
            parts.append("0")
        pieces.append(" ".join(parts))
        return "".join(pieces)

    def as_dict(self) -> Mapping[str, object]:
        return {
            "terms": [feature.name for feature in self.terms],
            "intercept": {"numerator": self.intercept.numerator, "denominator": self.intercept.denominator},
            "coefficients": [
                {"numerator": coef.numerator, "denominator": coef.denominator} for coef in self.coefficients
            ],
            "structure_bits": self.structure_bits,
            "coefficient_bits": self.coefficient_bits,
            "residual_bits": self.residual_bits,
            "baseline_bits": self.baseline_bits,
            "model_bits": self.model_bits,
            "total_bits": self.total_bits,
            "compression_ratio": self.compression_ratio,
            "sample_count": self.sample_count,
            "mean_abs": self.mean_abs,
            "std": self.std,
            "relative_std": (self.std / (self.mean_abs + 1e-12)) if self.mean_abs else 0.0,
            "expression": self.expression,
        }


def _fit_invariant(
    basis: Mapping[str, np.ndarray],
    terms: Sequence[FeatureDefinition],
    *,
    bits_per_sample: float,
) -> InvariantCandidate:
    n = int(next(iter(basis.values())).size)
    if n < 32:
        raise ValueError("need at least 32 samples")

    # Design matrix: [1, f1, f2, ...]
    columns: List[np.ndarray] = [np.ones(n, dtype=float)]
    for feature in terms:
        columns.append(feature.value(basis))
    matrix = np.stack(columns, axis=1)

    # IMPORTANT: fitting invariants from a *single trajectory* is degenerate.
    # This helper is kept for standalone use, but the ensemble fitter below is
    # what the NUSD domain uses.

    surrogate = _surrogate_signal(basis)
    solution, *_ = np.linalg.lstsq(matrix, surrogate, rcond=None)

    intercept = _approximate_fraction(float(solution[0]))
    coeffs = tuple(_approximate_fraction(float(v)) for v in solution[1:])

    coeff_vec = np.array([float(intercept)] + [float(v) for v in coeffs], dtype=float)
    h = matrix @ coeff_vec

    mean_h = float(np.mean(h))
    if abs(mean_h) > 1e-9:
        h = h / mean_h
        coeff_vec = coeff_vec / mean_h

    # Now residual is centered variance of H around 1.
    residuals = h - 1.0
    residual_bits = _mdl_for_residuals(residuals)

    intercept = _approximate_fraction(float(coeff_vec[0]))
    coeffs = tuple(_approximate_fraction(float(v)) for v in coeff_vec[1:])

    coefficient_bits = _mdl_for_coefficients((intercept,) + coeffs)
    structure_bits = sum(feature.structure_bits for feature in terms) + math.log2(1.0 + len(terms))

    # Baseline: store the H time series as raw samples at bits_per_sample.
    baseline_bits = float(n) * float(bits_per_sample)

    mean_abs = float(np.mean(np.abs(h)))
    std = float(np.std(h))

    return InvariantCandidate(
        terms=tuple(terms),
        intercept=intercept,
        coefficients=coeffs,
        structure_bits=structure_bits,
        coefficient_bits=coefficient_bits,
        residual_bits=residual_bits,
        baseline_bits=baseline_bits,
        sample_count=n,
        mean_abs=mean_abs,
        std=std,
    )


def _fit_invariant_ensemble(
    bases: Sequence[Mapping[str, np.ndarray]],
    terms: Sequence[FeatureDefinition],
    *,
    bits_per_sample: float,
    min_global_std: float = 1e-3,
) -> InvariantCandidate:
    if not bases:
        raise ValueError("at least one trajectory basis is required")
    sizes = [int(next(iter(b.values())).size) for b in bases]
    if any(n < 64 for n in sizes):
        raise ValueError("each trajectory must have at least 64 samples")

    # Stack the design matrices across trajectories.
    matrices: List[np.ndarray] = []
    surrogates: List[np.ndarray] = []
    for basis in bases:
        n = int(next(iter(basis.values())).size)
        cols: List[np.ndarray] = [np.ones(n, dtype=float)]
        for feature in terms:
            cols.append(feature.value(basis))
        matrices.append(np.stack(cols, axis=1))
        surrogates.append(np.asarray(_surrogate_signal(basis), dtype=float))

    matrix = np.concatenate(matrices, axis=0)
    surrogate = np.concatenate(surrogates, axis=0)

    solution, *_ = np.linalg.lstsq(matrix, surrogate, rcond=None)
    coeff_vec = np.asarray(solution, dtype=float)

    # Compute H for each trajectory and score invariance by within-trajectory residual.
    h_segments: List[np.ndarray] = []
    residual_segments: List[np.ndarray] = []
    for mat in matrices:
        h = mat @ coeff_vec
        h_segments.append(h)
        residual_segments.append(h - float(np.mean(h)))
    h_all = np.concatenate(h_segments, axis=0)
    global_std = float(np.std(h_all))
    if not math.isfinite(global_std) or global_std < min_global_std:
        # Reject (near-)constant invariants across the ensemble.
        residual_bits = 1e9
        intercept = Fraction(0, 1)
        coeffs: Tuple[Fraction, ...] = tuple()
        structure_bits = sum(feature.structure_bits for feature in terms) + math.log2(1.0 + len(terms))
        coefficient_bits = 0.0
        baseline_bits = float(sum(sizes)) * float(bits_per_sample)
        return InvariantCandidate(
            terms=tuple(terms),
            intercept=intercept,
            coefficients=coeffs,
            structure_bits=structure_bits,
            coefficient_bits=coefficient_bits,
            residual_bits=residual_bits,
            baseline_bits=baseline_bits,
            sample_count=int(sum(sizes)),
            mean_abs=0.0,
            std=0.0,
        )

    # Scale-fix: normalize so global_std(H)=1.
    coeff_vec = coeff_vec / global_std

    means: List[float] = []
    residual_segments = []
    for mat in matrices:
        h = mat @ coeff_vec
        mu = float(np.mean(h))
        means.append(mu)
        residual_segments.append(h - mu)
    residuals = np.concatenate(residual_segments, axis=0)
    residual_bits = _mdl_for_residuals(residuals)

    intercept = _approximate_fraction(float(coeff_vec[0]))
    coeffs = tuple(_approximate_fraction(float(v)) for v in coeff_vec[1:])

    coefficient_bits = _mdl_for_coefficients((intercept,) + coeffs)
    structure_bits = sum(feature.structure_bits for feature in terms) + math.log2(1.0 + len(terms))
    baseline_bits = float(sum(sizes)) * float(bits_per_sample)

    # Report stability as within-trajectory deviation (after removing per-run mean).
    # This keeps `relative_std` aligned with the "conserved over time" intuition.
    mean_abs = float(np.mean([abs(v) for v in means]))
    std = float(np.std(residuals))

    return InvariantCandidate(
        terms=tuple(terms),
        intercept=intercept,
        coefficients=coeffs,
        structure_bits=structure_bits,
        coefficient_bits=coefficient_bits,
        residual_bits=residual_bits,
        baseline_bits=baseline_bits,
        sample_count=int(sum(sizes)),
        mean_abs=mean_abs,
        std=std,
    )


def greedy_invariant_search(
    dataset: DoublePendulumDataset,
    *,
    candidate_pool: Sequence[FeatureDefinition] | None = None,
    max_terms: int = 6,
    min_gain_bits: float = 0.1,
    bits_per_sample: float = 64.0,
) -> InvariantCandidate:
    if max_terms <= 0:
        raise ValueError("max_terms must be positive")
    basis = _basis_for_dataset(dataset)
    pool = list(candidate_pool or BASE_FEATURES)

    selected: List[FeatureDefinition] = []
    best = _fit_invariant(basis, selected, bits_per_sample=bits_per_sample)

    while pool and len(selected) < max_terms:
        improvements: List[Tuple[InvariantCandidate, FeatureDefinition]] = []
        for feature in pool:
            candidate = _fit_invariant(basis, selected + [feature], bits_per_sample=bits_per_sample)
            improvements.append((candidate, feature))
        improvements.sort(key=lambda item: (item[0].total_bits, item[0].residual_bits))
        candidate, feature = improvements[0]

        improves = candidate.total_bits + min_gain_bits < best.total_bits
        if improves:
            selected.append(feature)
            pool.remove(feature)
            best = candidate
        else:
            break

    return best


def greedy_invariant_search_ensemble(
    ensemble: DoublePendulumEnsemble,
    *,
    candidate_pool: Sequence[FeatureDefinition] | None = None,
    max_terms: int = 6,
    min_terms: int = 2,
    min_gain_bits: float = 0.1,
    bits_per_sample: float = 64.0,
) -> InvariantCandidate:
    if max_terms <= 0:
        raise ValueError("max_terms must be positive")
    if min_terms <= 0:
        raise ValueError("min_terms must be positive")
    if min_terms > max_terms:
        raise ValueError("min_terms must be <= max_terms")
    bases = [_basis_for_dataset(ds) for ds in ensemble.trajectories]
    pool = list(candidate_pool or BASE_FEATURES)

    # Disallow the degenerate empty model for the ensemble search.
    selected: List[FeatureDefinition] = []
    best: InvariantCandidate | None = None

    while pool and len(selected) < max_terms:
        improvements: List[Tuple[InvariantCandidate, FeatureDefinition]] = []
        for feature in pool:
            candidate = _fit_invariant_ensemble(bases, selected + [feature], bits_per_sample=bits_per_sample)
            improvements.append((candidate, feature))
        improvements.sort(key=lambda item: (item[0].total_bits, item[0].residual_bits))
        candidate, feature = improvements[0]

        must_accept = len(selected) < min_terms
        if best is None or must_accept or candidate.total_bits + min_gain_bits < best.total_bits:
            selected.append(feature)
            pool.remove(feature)
            best = candidate
        else:
            break

    if best is None:
        # Fall back to a single-term model.
        best = _fit_invariant_ensemble(bases, [BASE_FEATURES[0]], bits_per_sample=bits_per_sample)
    return best


def invariant_score_report(candidate: InvariantCandidate) -> Mapping[str, object]:
    return {
        "expression": candidate.expression,
        "total_bits": candidate.total_bits,
        "model_bits": candidate.model_bits,
        "residual_bits": candidate.residual_bits,
        "baseline_bits": candidate.baseline_bits,
        "compression_ratio": candidate.compression_ratio,
        "relative_std": (candidate.std / (candidate.mean_abs + 1e-12)) if candidate.mean_abs else 0.0,
        "sample_count": candidate.sample_count,
    }


__all__ = [
    "DoublePendulumParams",
    "DoublePendulumDataset",
    "DoublePendulumEnsemble",
    "simulate_double_pendulum",
    "FeatureDefinition",
    "InvariantCandidate",
    "BASE_FEATURES",
    "greedy_invariant_search",
    "greedy_invariant_search_ensemble",
    "invariant_score_report",
]
