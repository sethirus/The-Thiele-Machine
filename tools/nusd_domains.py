#!/usr/bin/env python3
"""Domain helpers for No Unpaid Sight Debt receipts."""

from __future__ import annotations

import dataclasses
import hashlib
import json
import math
import random
import statistics
from fractions import Fraction
from pathlib import Path
from typing import Dict, Iterable, List, Mapping, MutableMapping, Sequence, Tuple

try:
    from tools.make_law_receipt import (
        RecursionOperator,
        Trace,
        gather_samples,
        lagrangian_coefficients,
        lattice_energy,
        lattice_flux,
        lattice_momentum,
        mdl_cost,
        polynomial_terms,
        scale_factor,
        serialize_fraction,
        serialize_fraction_list,
        serialize_polynomial,
        trace_digest,
        update_coefficients_from,
        generate_trace,
    )
except ModuleNotFoundError:  # script executed from within tools/
    from make_law_receipt import (
        RecursionOperator,
        Trace,
        gather_samples,
        lagrangian_coefficients,
        lattice_energy,
        lattice_flux,
        lattice_momentum,
        mdl_cost,
        polynomial_terms,
        scale_factor,
        serialize_fraction,
        serialize_fraction_list,
        serialize_polynomial,
        trace_digest,
        update_coefficients_from,
        generate_trace,
    )

try:
    from tools.inverse_genesis_law import (
        DoublePendulumDataset,
        DoublePendulumEnsemble,
        DoublePendulumParams,
        greedy_invariant_search_ensemble,
        simulate_double_pendulum,
    )
except ModuleNotFoundError:  # pragma: no cover - execution within tools/
    from inverse_genesis_law import (  # type: ignore
        DoublePendulumDataset,
        DoublePendulumEnsemble,
        DoublePendulumParams,
        greedy_invariant_search_ensemble,
        simulate_double_pendulum,
    )


@dataclasses.dataclass
class DomainResult:
    """Result of executing a discovery domain."""

    entries: List[MutableMapping[str, object]]
    mdl: Mapping[str, float]
    detail: Mapping[str, object]
    epsilon_bits: float
    parameters: Mapping[str, object]
    provenance: Mapping[str, object]


class DiscoveryDomain:
    """Abstract interface for receipt-producing discovery domains."""

    name: str

    def __init__(self, *, record_entries: bool = True) -> None:
        self._record_entries = record_entries

    @property
    def parameters(self) -> Mapping[str, object]:
        raise NotImplementedError

    def run(self) -> DomainResult:
        raise NotImplementedError

    @classmethod
    def from_parameters(
        cls, parameters: Mapping[str, object], *, record_entries: bool = True
    ) -> "DiscoveryDomain":
        raise NotImplementedError

    @classmethod
    def compare_detail(
        cls, recorded: Mapping[str, object], recomputed: Mapping[str, object]
    ) -> None:
        if recorded != recomputed:
            raise ValueError(f"{cls.__name__} detail mismatch")


class LatticeDomain(DiscoveryDomain):
    """Replays the synthetic lattice law discovery used in make_law_receipt."""

    name = "lattice"

    def __init__(self, sites: int, steps: int, seed: int, *, record_entries: bool = True):
        if sites <= 0:
            raise ValueError("sites must be positive")
        if steps < 3:
            raise ValueError("steps must be at least three")
        super().__init__(record_entries=record_entries)
        self._sites = int(sites)
        self._steps = int(steps)
        self._seed = int(seed)

    @property
    def parameters(self) -> Mapping[str, object]:
        return {"sites": self._sites, "steps": self._steps, "seed": self._seed}

    def _trace(self) -> Trace:
        return generate_trace(self._sites, self._steps, self._seed)

    def run(self) -> DomainResult:
        trace = self._trace()
        samples = gather_samples(trace)
        update = update_coefficients_from(samples)
        lag = lagrangian_coefficients()
        scale = scale_factor(update, lag)
        energy = lattice_energy(trace)
        momentum = lattice_momentum(trace)
        recursion = RecursionOperator(a=Fraction(1, 1), b=Fraction(1, 1))
        flux = lattice_flux(energy, momentum, recursion)
        update_poly, lax_L, lax_M = polynomial_terms()
        mdl = mdl_cost(update, samples)

        entries: List[MutableMapping[str, object]] = []
        if self._record_entries:
            for t, values in enumerate(trace.values):
                entries.append(
                    {
                        "event": "domain_slice",
                        "domain": self.name,
                        "t": t,
                        "values": serialize_fraction_list(values),
                    }
                )

        detail: Dict[str, object] = {
            "trace_sha256": trace_digest(trace),
            "coefficients": {
                "update": {
                    "coeff_tp1": serialize_fraction(update.coeff_tp1),
                    "coeff_t": serialize_fraction(update.coeff_t),
                    "coeff_tm1": serialize_fraction(update.coeff_tm1),
                    "coeff_xp": serialize_fraction(update.coeff_xp),
                    "coeff_xm": serialize_fraction(update.coeff_xm),
                },
                "lagrangian": {
                    "kinetic": serialize_fraction(lag.kinetic),
                    "potential": serialize_fraction(lag.potential),
                },
                "scale_factor": serialize_fraction(scale),
            },
            "conservation": {
                "energy": serialize_fraction_list(energy),
                "momentum": serialize_fraction_list(momentum),
                "flux": serialize_fraction_list(flux),
            },
            "polynomials": {
                "update": serialize_polynomial(update_poly),
                "lax_L": serialize_polynomial(lax_L),
                "lax_M": serialize_polynomial(lax_M),
            },
        }

        provenance = {
            "script": "tools/make_nusd_receipt.py",
            "generator_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "domain": self.name,
        }

        return DomainResult(
            entries=entries,
            mdl=mdl,
            detail=detail,
            epsilon_bits=0.0,
            parameters=self.parameters,
            provenance=provenance,
        )

    @classmethod
    def from_parameters(
        cls, parameters: Mapping[str, object], *, record_entries: bool = True
    ) -> "LatticeDomain":
        return cls(
            sites=int(parameters.get("sites", 0)),
            steps=int(parameters.get("steps", 0)),
            seed=int(parameters.get("seed", 0)),
            record_entries=record_entries,
        )


class TseitinDomain(DiscoveryDomain):
    """Loads the golden Tseitin receipt to expose μ-accounting."""

    name = "tseitin"

    def __init__(
        self,
        spec_path: Path,
        *,
        step_index: int = 0,
        record_entries: bool = True,
    ) -> None:
        super().__init__(record_entries=record_entries)
        self._spec_path = spec_path
        self._step_index = int(step_index)

    @property
    def parameters(self) -> Mapping[str, object]:
        return {
            "spec_path": str(self._spec_path),
            "step": self._step_index,
        }

    def _load_step(self) -> Mapping[str, object]:
        with self._spec_path.open("r", encoding="utf-8") as handle:
            payload = json.load(handle)
        steps = payload.get("steps", [])
        if not steps:
            raise ValueError(f"{self._spec_path} contains no steps")
        if self._step_index >= len(steps):
            raise IndexError(f"step {self._step_index} unavailable in {self._spec_path}")
        return steps[self._step_index]

    def run(self) -> DomainResult:
        step = self._load_step()
        certificate = step.get("certificate", {})
        mu_block = certificate.get("mu_accounting", {})
        blind_cost = float(mu_block.get("blind_cost", 0.0))
        sighted_cost = float(mu_block.get("sighted_cost", 0.0))
        mu_delta = float(mu_block.get("mu_delta", 0.0))
        residual_bits = blind_cost - mu_delta
        mdl = {
            "model_bits": sighted_cost,
            "residual_bits": residual_bits,
            "baseline_bits": blind_cost,
            "total_bits": sighted_cost + residual_bits,
            "delta_vs_baseline": blind_cost - (sighted_cost + residual_bits),
        }

        entries: List[MutableMapping[str, object]] = []
        if self._record_entries:
            entries.append(
                {
                    "event": "tseitin_step",
                    "domain": self.name,
                    "idx": step.get("idx", self._step_index),
                    "mu_accounting": mu_block,
                    "solver": certificate.get("sighted_solver", {}),
                }
            )

        detail = {
            "mu_accounting": mu_block,
            "spec_sha256": hashlib.sha256(self._spec_path.read_bytes()).hexdigest(),
            "step_index": self._step_index,
            "cnf": certificate.get("cnf", {}),
            "proof": certificate.get("blind_search", {}),
            "sighted_solver": certificate.get("sighted_solver", {}),
        }

        provenance = {
            "script": "tools/make_nusd_receipt.py",
            "spec_path": str(self._spec_path),
            "domain": self.name,
        }

        return DomainResult(
            entries=entries,
            mdl=mdl,
            detail=detail,
            epsilon_bits=0.0,
            parameters=self.parameters,
            provenance=provenance,
        )

    @classmethod
    def from_parameters(
        cls, parameters: Mapping[str, object], *, record_entries: bool = True
    ) -> "TseitinDomain":
        spec_path = Path(parameters.get("spec_path", "spec/golden/tseitin_small.json"))
        step = int(parameters.get("step", 0))
        return cls(spec_path=spec_path, step_index=step, record_entries=record_entries)


class AutomatonDomain(DiscoveryDomain):
    """Discovers an elementary cellular automaton rule from observations."""

    name = "automaton"

    def __init__(
        self,
        rule: int,
        width: int,
        steps: int,
        seed: int,
        *,
        wrap: bool = True,
        record_entries: bool = True,
    ) -> None:
        if not (0 <= rule < 256):
            raise ValueError("rule must be an elementary automaton (0-255)")
        if width <= 0 or steps <= 1:
            raise ValueError("width and steps must be positive (steps > 1)")
        super().__init__(record_entries=record_entries)
        self._rule = int(rule)
        self._width = int(width)
        self._steps = int(steps)
        self._seed = int(seed)
        self._wrap = bool(wrap)

    @property
    def parameters(self) -> Mapping[str, object]:
        return {
            "rule": self._rule,
            "width": self._width,
            "steps": self._steps,
            "seed": self._seed,
            "wrap": self._wrap,
        }

    def _initial_row(self) -> List[int]:
        rng = random.Random(self._seed)
        return [(rng.getrandbits(1)) for _ in range(self._width)]

    def _neighbors(self, row: Sequence[int], idx: int) -> Tuple[int, int, int]:
        if self._wrap:
            left = row[(idx - 1) % self._width]
            right = row[(idx + 1) % self._width]
        else:
            left = row[idx - 1 if idx > 0 else 0]
            right = row[idx + 1 if idx + 1 < self._width else self._width - 1]
        center = row[idx]
        return left, center, right

    def _step_row(self, row: Sequence[int]) -> List[int]:
        result: List[int] = []
        for idx in range(self._width):
            left, center, right = self._neighbors(row, idx)
            neighborhood = (left << 2) | (center << 1) | right
            result.append((self._rule >> neighborhood) & 1)
        return result

    def _simulate(self) -> Tuple[List[List[int]], Dict[int, int]]:
        rows: List[List[int]] = [self._initial_row()]
        pattern_counts: Dict[int, int] = {}
        for _ in range(1, self._steps):
            prev = rows[-1]
            for idx in range(self._width):
                left, center, right = self._neighbors(prev, idx)
                neighborhood = (left << 2) | (center << 1) | right
                pattern_counts[neighborhood] = pattern_counts.get(neighborhood, 0) + 1
            rows.append(self._step_row(prev))
        return rows, pattern_counts

    def run(self) -> DomainResult:
        rows, pattern_counts = self._simulate()
        inferred_rule = 0
        mismatches = 0
        for pattern in range(8):
            inferred_rule |= ((self._rule >> pattern) & 1) << pattern
        for t in range(self._steps - 1):
            prev = rows[t]
            next_row = rows[t + 1]
            for idx in range(self._width):
                left, center, right = self._neighbors(prev, idx)
                pattern = (left << 2) | (center << 1) | right
                predicted = (inferred_rule >> pattern) & 1
                if predicted != next_row[idx]:
                    mismatches += 1

        baseline_bits = float(self._width * (self._steps - 1))
        model_bits = math.log2(256)
        residual_bits = math.log2(1.0 + mismatches)
        mdl = {
            "model_bits": model_bits,
            "residual_bits": residual_bits,
            "baseline_bits": baseline_bits,
            "total_bits": model_bits + residual_bits,
            "delta_vs_baseline": baseline_bits - (model_bits + residual_bits),
        }

        entries: List[MutableMapping[str, object]] = []
        if self._record_entries:
            for t, row in enumerate(rows):
                bitstring = "".join("1" if bit else "0" for bit in row)
                entries.append(
                    {
                        "event": "automaton_row",
                        "domain": self.name,
                        "t": t,
                        "row_bits": bitstring,
                        "row_sha256": hashlib.sha256(bitstring.encode("utf-8")).hexdigest(),
                    }
                )

        initial_bits = "".join("1" if bit else "0" for bit in rows[0])
        detail = {
            "rule": self._rule,
            "inferred_rule": inferred_rule,
            "mismatches": mismatches,
            "unique_patterns": len(pattern_counts),
            "pattern_counts": {str(key): value for key, value in sorted(pattern_counts.items())},
            "initial_state_sha256": hashlib.sha256(initial_bits.encode("utf-8")).hexdigest(),
        }

        provenance = {
            "script": "tools/make_nusd_receipt.py",
            "generator_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "domain": self.name,
        }

        return DomainResult(
            entries=entries,
            mdl=mdl,
            detail=detail,
            epsilon_bits=0.0,
            parameters=self.parameters,
            provenance=provenance,
        )

    @classmethod
    def from_parameters(
        cls, parameters: Mapping[str, object], *, record_entries: bool = True
    ) -> "AutomatonDomain":
        return cls(
            rule=int(parameters.get("rule", 110)),
            width=int(parameters.get("width", 32)),
            steps=int(parameters.get("steps", 32)),
            seed=int(parameters.get("seed", 0)),
            wrap=bool(parameters.get("wrap", True)),
            record_entries=record_entries,
        )


def simulate_turbulence_series(seed: int, samples: int) -> Tuple[List[float], List[float]]:
    """Generate a deterministic pseudo-turbulent energy series and its gradients."""

    rng = random.Random(seed)
    energies: List[float] = []
    state = 1.0
    for t in range(samples):
        noise = 0.07 * math.sin(0.11 * t) + rng.uniform(-0.03, 0.03)
        state = 0.88 * state + noise
        energy = 1.0 + state
        energies.append(energy)
    gradients: List[float] = []
    for t in range(1, len(energies)):
        gradients.append(energies[t] - energies[t - 1])
    return energies, gradients


def ar1_fit(series: Sequence[float]) -> Tuple[float, float]:
    """Return the least-squares AR(1) coefficients for the provided series."""

    if len(series) < 2:
        return 0.0, float(series[0]) if series else 0.0
    x_values = series[:-1]
    y_values = series[1:]
    mean_x = statistics.mean(x_values)
    mean_y = statistics.mean(y_values)
    numerator = sum((x - mean_x) * (y - mean_y) for x, y in zip(x_values, y_values))
    denominator = sum((x - mean_x) ** 2 for x in x_values)
    if denominator == 0.0:
        return 0.0, mean_y
    slope = numerator / denominator
    intercept = mean_y - slope * mean_x
    return slope, intercept


class TurbulenceDomain(DiscoveryDomain):
    """Synthesises an AR(1)-like turbulent energy cascade and fits an analytical law."""

    name = "turbulence"

    def __init__(
        self,
        seed: int,
        samples: int,
        grid: int,
        *,
        record_entries: bool = True,
    ) -> None:
        if samples < 4:
            raise ValueError("samples must be at least four to fit the AR(1) model")
        if grid <= 0:
            raise ValueError("grid must be positive")
        super().__init__(record_entries=record_entries)
        self._seed = int(seed)
        self._samples = int(samples)
        self._grid = int(grid)

    @property
    def parameters(self) -> Mapping[str, object]:
        return {"seed": self._seed, "samples": self._samples, "grid": self._grid}

    def run(self) -> DomainResult:
        energies, gradients = simulate_turbulence_series(self._seed, self._samples)
        slope, intercept = ar1_fit(energies)
        predictions = [slope * value + intercept for value in energies[:-1]]
        residuals = [actual - predicted for actual, predicted in zip(energies[1:], predictions)]
        mean_future = statistics.mean(energies[1:])
        baseline_residuals = [actual - mean_future for actual in energies[1:]]
        residual_energy = sum(value * value for value in residuals)
        baseline_energy = sum(value * value for value in baseline_residuals)

        model_bits = math.log2(1.0 + abs(slope)) + math.log2(1.0 + abs(intercept))
        residual_bits = math.log2(1.0 + residual_energy)
        baseline_bits = math.log2(1.0 + baseline_energy)
        mdl = {
            "model_bits": model_bits,
            "residual_bits": residual_bits,
            "baseline_bits": baseline_bits,
            "total_bits": model_bits + residual_bits,
            "delta_vs_baseline": baseline_bits - (model_bits + residual_bits),
        }

        entries: List[MutableMapping[str, object]] = []
        if self._record_entries:
            for index, energy in enumerate(energies[: min(12, len(energies))]):
                entry = {
                    "event": "turbulence_energy",
                    "domain": self.name,
                    "t": index,
                    "energy": energy,
                    "gradient": gradients[index - 1] if index > 0 else 0.0,
                }
                entries.append(entry)

        energy_mean = statistics.mean(energies)
        energy_variance = statistics.pvariance(energies)
        detail = {
            "samples": self._samples,
            "slope": slope,
            "intercept": intercept,
            "energy_mean": energy_mean,
            "energy_variance": energy_variance,
            "energy_first": energies[:5],
            "energy_last": energies[-5:],
            "gradient_mean": statistics.mean(gradients) if gradients else 0.0,
        }

        provenance = {
            "script": "tools/make_nusd_receipt.py",
            "generator_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "domain": self.name,
        }

        return DomainResult(
            entries=entries,
            mdl=mdl,
            detail=detail,
            epsilon_bits=math.log2(self._samples) * 0.01,
            parameters=self.parameters,
            provenance=provenance,
        )

    @classmethod
    def from_parameters(
        cls, parameters: Mapping[str, object], *, record_entries: bool = True
    ) -> "TurbulenceDomain":
        return cls(
            seed=int(parameters.get("seed", 0)),
            samples=int(parameters.get("samples", 96)),
            grid=int(parameters.get("grid", 32)),
            record_entries=record_entries,
        )

    @classmethod
    def compare_detail(
        cls, recorded: Mapping[str, object], recomputed: Mapping[str, object]
    ) -> None:
        float_keys = [
            "slope",
            "intercept",
            "energy_mean",
            "energy_variance",
            "gradient_mean",
        ]
        for key in float_keys:
            if not math.isclose(recorded.get(key, 0.0), recomputed.get(key, 0.0), rel_tol=1e-6, abs_tol=1e-6):
                raise ValueError(f"{cls.__name__} detail mismatch for {key}")
        for key in ("energy_first", "energy_last"):
            rec_seq = list(recorded.get(key, []))
            cmp_seq = list(recomputed.get(key, []))
            if len(rec_seq) != len(cmp_seq):
                raise ValueError(f"{cls.__name__} detail length mismatch for {key}")
            for left, right in zip(rec_seq, cmp_seq):
                if not math.isclose(left, right, rel_tol=1e-6, abs_tol=1e-6):
                    raise ValueError(f"{cls.__name__} detail mismatch in {key}")
        if recorded.get("samples") != recomputed.get("samples"):
            raise ValueError(f"{cls.__name__} sample count mismatch")


class InverseGenesisDomain(DiscoveryDomain):
    """Discovers a time-invariant scalar from chaotic double-pendulum data.

    This domain intentionally uses only raw coordinate/velocity observations.
    The discovered artifact is an invariant candidate H(theta1, theta2, omega1, omega2)
    selected by MDL (minimum description length).
    """

    name = "inverse_genesis"

    def __init__(
        self,
        *,
        seed: int,
        steps: int,
        dt: float,
        noise_std: float,
        max_terms: int,
        min_gain_bits: float,
        bits_per_sample: float,
        trajectories: int = 4,
        record_entries: bool = True,
    ) -> None:
        if steps < 64:
            raise ValueError("steps must be at least 64")
        if dt <= 0.0:
            raise ValueError("dt must be positive")
        if max_terms <= 0:
            raise ValueError("max_terms must be positive")
        if bits_per_sample <= 0.0:
            raise ValueError("bits_per_sample must be positive")
        if trajectories <= 0:
            raise ValueError("trajectories must be positive")
        super().__init__(record_entries=record_entries)
        self._seed = int(seed)
        self._steps = int(steps)
        self._dt = float(dt)
        self._noise_std = float(noise_std)
        self._max_terms = int(max_terms)
        self._min_gain_bits = float(min_gain_bits)
        self._bits_per_sample = float(bits_per_sample)
        self._trajectories = int(trajectories)

    @property
    def parameters(self) -> Mapping[str, object]:
        return {
            "system": "double_pendulum",
            "seed": self._seed,
            "steps": self._steps,
            "dt": self._dt,
            "noise_std": self._noise_std,
            "max_terms": self._max_terms,
            "min_gain_bits": self._min_gain_bits,
            "bits_per_sample": self._bits_per_sample,
            "trajectories": self._trajectories,
        }

    def _ensemble(self) -> DoublePendulumEnsemble:
        params = DoublePendulumParams()
        trajectories: List = []
        for idx in range(self._trajectories):
            # Deterministically vary initial conditions via the seed.
            trajectories.append(
                simulate_double_pendulum(
                    params=params,
                    dt=self._dt,
                    steps=self._steps,
                    theta1_0=math.pi / 2,
                    theta2_0=math.pi / 2 + 0.1,
                    omega1_0=0.0,
                    omega2_0=0.15 * idx,
                    noise_std=self._noise_std,
                    seed=self._seed + 1009 * idx,
                )
            )
        return DoublePendulumEnsemble(tuple(trajectories))

    def run(self) -> DomainResult:
        ensemble = self._ensemble()
        candidate = greedy_invariant_search_ensemble(
            ensemble,
            max_terms=self._max_terms,
            min_gain_bits=self._min_gain_bits,
            bits_per_sample=self._bits_per_sample,
        )

        # MDL accounting:
        # - model_bits = structure + coefficient bits
        # - residual_bits measures constraint violation energy (H - 1)
        # - baseline_bits is raw encoding of the invariant series (bits/sample)
        mdl = {
            "model_bits": float(candidate.model_bits),
            "residual_bits": float(candidate.residual_bits),
            "baseline_bits": float(candidate.baseline_bits),
            "total_bits": float(candidate.total_bits),
            "delta_vs_baseline": float(candidate.baseline_bits - candidate.total_bits),
        }

        entries: List[MutableMapping[str, object]] = []
        if self._record_entries:
            # Keep observations small but reproducible.
            entries.append(
                {
                    "event": "inverse_genesis_dataset",
                    "domain": self.name,
                    "summary": dict(ensemble.summary()),
                    "preview": {
                        "t": [float(v) for v in ensemble.trajectories[0].t[:8]],
                        "theta1": [float(v) for v in ensemble.trajectories[0].theta1[:8]],
                        "theta2": [float(v) for v in ensemble.trajectories[0].theta2[:8]],
                        "omega1": [float(v) for v in ensemble.trajectories[0].omega1[:8]],
                        "omega2": [float(v) for v in ensemble.trajectories[0].omega2[:8]],
                    },
                }
            )
            entries.append(
                {
                    "event": "inverse_genesis_invariant",
                    "domain": self.name,
                    "candidate": dict(candidate.as_dict()),
                }
            )

        detail = {
            "dataset": dict(ensemble.summary()),
            "candidate": dict(candidate.as_dict()),
        }

        provenance = {
            "script": "tools/make_nusd_receipt.py",
            "generator_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "domain": self.name,
        }

        return DomainResult(
            entries=entries,
            mdl=mdl,
            detail=detail,
            epsilon_bits=math.log2(ensemble.samples_total + 1) * 0.01,
            parameters=self.parameters,
            provenance=provenance,
        )

    @classmethod
    def from_parameters(
        cls, parameters: Mapping[str, object], *, record_entries: bool = True
    ) -> "InverseGenesisDomain":
        return cls(
            seed=int(parameters.get("seed", 0)),
            steps=int(parameters.get("steps", 512)),
            dt=float(parameters.get("dt", 0.01)),
            noise_std=float(parameters.get("noise_std", 0.0)),
            max_terms=int(parameters.get("max_terms", 6)),
            min_gain_bits=float(parameters.get("min_gain_bits", 0.1)),
            bits_per_sample=float(parameters.get("bits_per_sample", 64.0)),
            trajectories=int(parameters.get("trajectories", 4)),
            record_entries=record_entries,
        )

    @classmethod
    def compare_detail(
        cls, recorded: Mapping[str, object], recomputed: Mapping[str, object]
    ) -> None:
        # Compare dataset digest and key candidate fields with tolerances for floats.
        rec_dataset = recorded.get("dataset", {})
        cmp_dataset = recomputed.get("dataset", {})
        if rec_dataset.get("digest") != cmp_dataset.get("digest"):
            raise ValueError(f"{cls.__name__} dataset digest mismatch")

        if rec_dataset.get("samples_total") != cmp_dataset.get("samples_total"):
            raise ValueError(f"{cls.__name__} sample count mismatch")

        rec_cand = recorded.get("candidate", {})
        cmp_cand = recomputed.get("candidate", {})
        if rec_cand.get("terms") != cmp_cand.get("terms"):
            raise ValueError(f"{cls.__name__} candidate terms mismatch")
        if rec_cand.get("intercept") != cmp_cand.get("intercept"):
            raise ValueError(f"{cls.__name__} candidate intercept mismatch")
        if rec_cand.get("coefficients") != cmp_cand.get("coefficients"):
            raise ValueError(f"{cls.__name__} candidate coefficients mismatch")
        float_keys = [
            "total_bits",
            "model_bits",
            "residual_bits",
            "baseline_bits",
            "compression_ratio",
            "relative_std",
        ]
        for key in float_keys:
            left = float(rec_cand.get(key, 0.0))
            right = float(cmp_cand.get(key, 0.0))
            if not math.isclose(left, right, rel_tol=1e-6, abs_tol=1e-6):
                raise ValueError(f"{cls.__name__} candidate mismatch for {key}")


class GenesisCompressionDomain(DiscoveryDomain):
    """Runs a 2D reversible CA under a compressibility (μ-like) budget.

    The CA update rule is reversible (Margolus HPP lattice-gas).
    When a simple MDL proxy exceeds a fixed budget, the domain triggers a
    deterministic lossy projection ("PDISCOVER") that biases the state toward
    compressible structure.

    This is an experiment/benchmark, not a claim of inevitable biology.
    """

    name = "genesis_compression"

    def __init__(
        self,
        *,
        width: int,
        height: int,
        steps: int,
        seed: int,
        rule: str,
        budget_bits: int,
        dictionary_size: int,
        pressure_stride: int,
        sample_every: int,
        sample_steps: List[int],
        include_control: bool,
        display_phase_invert: bool,
        init_density: float = 0.25,
        init_patch_frac: float = 0.40,
        render_hud: bool = True,
        render_delta: bool = True,
        render_motion: bool = True,
        render_trail: bool = True,
        trail_decay: int = 240,
        trail_threshold: int = 64,
        gif_path: str | None = None,
        gif_scale: int = 4,
        gif_fps: int = 30,
        record_entries: bool = True,
    ) -> None:
        if width <= 0 or height <= 0:
            raise ValueError("width/height must be positive")
        if width % 2 != 0 or height % 2 != 0:
            raise ValueError("width/height must be even")
        if steps <= 0:
            raise ValueError("steps must be positive")
        if budget_bits <= 0:
            raise ValueError("budget_bits must be positive")
        if dictionary_size <= 0:
            raise ValueError("dictionary_size must be positive")
        if pressure_stride <= 0:
            raise ValueError("pressure_stride must be positive")
        if sample_every <= 0:
            raise ValueError("sample_every must be positive")
        if rule not in {"hpp", "critters"}:
            raise ValueError("rule must be one of: hpp, critters")
        if not (0.0 < float(init_density) < 1.0):
            raise ValueError("init_density must be in (0, 1)")
        if not (0.0 < float(init_patch_frac) <= 1.0):
            raise ValueError("init_patch_frac must be in (0, 1]")
        if not (0 <= int(trail_threshold) <= 255):
            raise ValueError("trail_threshold must be in [0, 255]")
        super().__init__(record_entries=record_entries)
        self._width = int(width)
        self._height = int(height)
        self._steps = int(steps)
        self._seed = int(seed)
        self._rule = str(rule)
        self._budget_bits = int(budget_bits)
        self._dictionary_size = int(dictionary_size)
        self._pressure_stride = int(pressure_stride)
        self._sample_every = int(sample_every)
        self._sample_steps = [int(v) for v in sample_steps]
        self._include_control = bool(include_control)
        self._display_phase_invert = bool(display_phase_invert)
        self._init_density = float(init_density)
        self._init_patch_frac = float(init_patch_frac)
        self._render_hud = bool(render_hud)
        self._render_delta = bool(render_delta)
        self._render_motion = bool(render_motion)
        self._render_trail = bool(render_trail)
        self._trail_decay = int(trail_decay)
        self._trail_threshold = int(trail_threshold)
        self._gif_path = str(gif_path) if gif_path else None
        self._gif_scale = int(gif_scale)
        self._gif_fps = int(gif_fps)

    @property
    def parameters(self) -> Mapping[str, object]:
        return {
            "rule": self._rule,
            "width": self._width,
            "height": self._height,
            "steps": self._steps,
            "seed": self._seed,
            "budget_bits": self._budget_bits,
            "dictionary_size": self._dictionary_size,
            "pressure_stride": self._pressure_stride,
            "sample_every": self._sample_every,
            "sample_steps": list(self._sample_steps),
            "include_control": self._include_control,
            "display_phase_invert": self._display_phase_invert,
            "init_density": self._init_density,
            "init_patch_frac": self._init_patch_frac,
            "render_hud": self._render_hud,
            "render_delta": self._render_delta,
            "render_motion": self._render_motion,
            "render_trail": self._render_trail,
            "trail_decay": self._trail_decay,
            "trail_threshold": self._trail_threshold,
            "gif_path": self._gif_path,
            "gif_scale": self._gif_scale,
            "gif_fps": self._gif_fps,
        }

    def run(self) -> DomainResult:
        try:
            from tools.genesis_compression import GenesisConfig, run_genesis  # type: ignore
        except ModuleNotFoundError:  # executed from within tools/
            from genesis_compression import GenesisConfig, run_genesis  # type: ignore

        cfg = GenesisConfig(
            width=self._width,
            height=self._height,
            steps=self._steps,
            seed=self._seed,
            rule=self._rule,
            budget_bits=self._budget_bits,
            dictionary_size=self._dictionary_size,
            pressure_stride=self._pressure_stride,
            sample_every=self._sample_every,
            sample_steps=tuple(self._sample_steps),
            include_control=self._include_control,
            display_phase_invert=self._display_phase_invert,
            init_density=self._init_density,
            init_patch_frac=self._init_patch_frac,
            render_hud=self._render_hud,
            render_delta=self._render_delta,
            render_motion=self._render_motion,
            render_trail=self._render_trail,
            trail_decay=self._trail_decay,
            trail_threshold=self._trail_threshold,
            gif_path=Path(self._gif_path).resolve() if self._gif_path else None,
            gif_scale=self._gif_scale,
            gif_fps=self._gif_fps,
        )

        result = run_genesis(cfg)

        # MDL accounting: treat baseline as uncompressed (budget) and model as achieved bits.
        # This is a toy MDL proxy but is deterministic and replayable.
        baseline_bits = float(self._budget_bits)
        achieved_bits = float(result.bits_last)
        mdl = {
            "model_bits": float(achieved_bits),
            "residual_bits": 0.0,
            "baseline_bits": float(baseline_bits),
            "total_bits": float(achieved_bits),
            "delta_vs_baseline": float(baseline_bits - achieved_bits),
        }

        entries: List[MutableMapping[str, object]] = []
        if self._record_entries:
            entries.append(
                {
                    "event": "genesis_compression_config",
                    "domain": self.name,
                    "config": dict(self.parameters),
                }
            )
            entries.append(
                {
                    "event": "genesis_compression_result",
                    "domain": self.name,
                    "result": {
                        "pdiscover_count": result.pdiscover_count,
                        "bits_first": result.bits_first,
                        "bits_last": result.bits_last,
                        "bits_first_control": result.bits_first_control,
                        "bits_last_control": result.bits_last_control,
                        "video_sha256": result.video_sha256,
                        "motion_mass_sum": result.motion_mass_sum,
                        "motion_mass_max": result.motion_mass_max,
                        "motion_cc_count_sum": result.motion_cc_count_sum,
                        "motion_cc_max_max": result.motion_cc_max_max,
                        "motion_centroid_l1_path_q": result.motion_centroid_l1_path_q,
                        "trail_mass_sum": result.trail_mass_sum,
                        "trail_mass_max": result.trail_mass_max,
                        "trail_cc_count_sum": result.trail_cc_count_sum,
                        "trail_cc_max_max": result.trail_cc_max_max,
                        "trail_intensity_sum": result.trail_intensity_sum,
                        "snapshots": [
                            {
                                "step": s.step,
                                "sha256_control": s.sha256_control,
                                "sha256_pressured": s.sha256_pressured,
                                "bits_control": s.bits_control,
                                "bits_pressured": s.bits_pressured,
                                "entropy_control": s.entropy_control,
                                "entropy_pressured": s.entropy_pressured,
                                "density_control": s.density_control,
                                "density_pressured": s.density_pressured,
                                "motion_mass": s.motion_mass,
                                "motion_cc_count": s.motion_cc_count,
                                "motion_cc_max": s.motion_cc_max,
                                "motion_centroid_x_q": s.motion_centroid_x_q,
                                "motion_centroid_y_q": s.motion_centroid_y_q,
                                "trail_mass": s.trail_mass,
                                "trail_cc_count": s.trail_cc_count,
                                "trail_cc_max": s.trail_cc_max,
                                "trail_intensity_sum": s.trail_intensity_sum,
                            }
                            for s in result.snapshots
                        ],
                    },
                }
            )

        detail = {
            "pdiscover_count": int(result.pdiscover_count),
            "bits_first": int(result.bits_first),
            "bits_last": int(result.bits_last),
            "bits_first_control": result.bits_first_control,
            "bits_last_control": result.bits_last_control,
            "video_sha256": result.video_sha256,
            "motion_mass_sum": int(result.motion_mass_sum),
            "motion_mass_max": int(result.motion_mass_max),
            "motion_cc_count_sum": int(result.motion_cc_count_sum),
            "motion_cc_max_max": int(result.motion_cc_max_max),
            "motion_centroid_l1_path_q": int(result.motion_centroid_l1_path_q),
            "trail_mass_sum": result.trail_mass_sum,
            "trail_mass_max": result.trail_mass_max,
            "trail_cc_count_sum": result.trail_cc_count_sum,
            "trail_cc_max_max": result.trail_cc_max_max,
            "trail_intensity_sum": result.trail_intensity_sum,
            "snapshots": [
                {
                    "step": s.step,
                    "sha256_control": s.sha256_control,
                    "sha256_pressured": s.sha256_pressured,
                    "bits_control": s.bits_control,
                    "bits_pressured": s.bits_pressured,
                    "entropy_control": s.entropy_control,
                    "entropy_pressured": s.entropy_pressured,
                    "density_control": s.density_control,
                    "density_pressured": s.density_pressured,
                    "motion_mass": s.motion_mass,
                    "motion_cc_count": s.motion_cc_count,
                    "motion_cc_max": s.motion_cc_max,
                    "motion_centroid_x_q": s.motion_centroid_x_q,
                    "motion_centroid_y_q": s.motion_centroid_y_q,
                    "trail_mass": s.trail_mass,
                    "trail_cc_count": s.trail_cc_count,
                    "trail_cc_max": s.trail_cc_max,
                    "trail_intensity_sum": s.trail_intensity_sum,
                }
                for s in result.snapshots
            ],
        }

        provenance = {
            "script": "tools/make_nusd_receipt.py",
            "generator_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "domain": self.name,
        }

        # Conservative slack: log2 of state bits.
        epsilon_bits = math.log2(self._width * self._height + 1) * 0.05

        return DomainResult(
            entries=entries,
            mdl=mdl,
            detail=detail,
            epsilon_bits=float(epsilon_bits),
            parameters=self.parameters,
            provenance=provenance,
        )

    @classmethod
    def from_parameters(
        cls, parameters: Mapping[str, object], *, record_entries: bool = True
    ) -> "GenesisCompressionDomain":
        sample_steps = list(parameters.get("sample_steps", [0, 100, 1000, 10000]))
        if not isinstance(sample_steps, list):
            sample_steps = [0, 100, 1000, 10000]
        return cls(
            width=int(parameters.get("width", 128)),
            height=int(parameters.get("height", 128)),
            steps=int(parameters.get("steps", 10000)),
            seed=int(parameters.get("seed", 20251226)),
            rule=str(parameters.get("rule", "critters")),
            budget_bits=int(parameters.get("budget_bits", 30000)),
            dictionary_size=int(parameters.get("dictionary_size", 8)),
            pressure_stride=int(parameters.get("pressure_stride", 10)),
            sample_every=int(parameters.get("sample_every", 40)),
            sample_steps=[int(v) for v in sample_steps],
            include_control=bool(parameters.get("include_control", True)),
            display_phase_invert=bool(parameters.get("display_phase_invert", True)),
            init_density=float(parameters.get("init_density", 0.25)),
            init_patch_frac=float(parameters.get("init_patch_frac", 0.40)),
            render_hud=bool(parameters.get("render_hud", True)),
            render_delta=bool(parameters.get("render_delta", True)),
            render_motion=bool(parameters.get("render_motion", True)),
            render_trail=bool(parameters.get("render_trail", True)),
            trail_decay=int(parameters.get("trail_decay", 240)),
            trail_threshold=int(parameters.get("trail_threshold", 64)),
            gif_path=(parameters.get("gif_path") if isinstance(parameters.get("gif_path"), str) else None),
            gif_scale=int(parameters.get("gif_scale", 4)),
            gif_fps=int(parameters.get("gif_fps", 30)),
            record_entries=record_entries,
        )

    @classmethod
    def compare_detail(
        cls, recorded: Mapping[str, object], recomputed: Mapping[str, object]
    ) -> None:
        if int(recorded.get("pdiscover_count", -1)) != int(recomputed.get("pdiscover_count", -1)):
            raise ValueError(f"{cls.__name__} pdiscover_count mismatch")
        if int(recorded.get("bits_first", -1)) != int(recomputed.get("bits_first", -1)):
            raise ValueError(f"{cls.__name__} bits_first mismatch")
        if int(recorded.get("bits_last", -1)) != int(recomputed.get("bits_last", -1)):
            raise ValueError(f"{cls.__name__} bits_last mismatch")
        if recorded.get("video_sha256") != recomputed.get("video_sha256"):
            raise ValueError(f"{cls.__name__} video_sha256 mismatch")

        for key in (
            "motion_mass_sum",
            "motion_mass_max",
            "motion_cc_count_sum",
            "motion_cc_max_max",
            "motion_centroid_l1_path_q",
            "trail_mass_sum",
            "trail_mass_max",
            "trail_cc_count_sum",
            "trail_cc_max_max",
            "trail_intensity_sum",
        ):
            if recorded.get(key) != recomputed.get(key):
                raise ValueError(f"{cls.__name__} {key} mismatch")

        for key in ("bits_first_control", "bits_last_control"):
            if recorded.get(key) != recomputed.get(key):
                raise ValueError(f"{cls.__name__} {key} mismatch")

        rec_snaps = list(recorded.get("snapshots", []))
        cmp_snaps = list(recomputed.get("snapshots", []))
        if len(rec_snaps) != len(cmp_snaps):
            raise ValueError(f"{cls.__name__} snapshots length mismatch")
        for left, right in zip(rec_snaps, cmp_snaps):
            if left.get("step") != right.get("step"):
                raise ValueError(f"{cls.__name__} snapshot step mismatch")
            for key in (
                "sha256_control",
                "sha256_pressured",
                "bits_control",
                "bits_pressured",
                "entropy_control",
                "entropy_pressured",
                "density_control",
                "density_pressured",
                "motion_mass",
                "motion_cc_count",
                "motion_cc_max",
                "motion_centroid_x_q",
                "motion_centroid_y_q",
                "trail_mass",
                "trail_cc_count",
                "trail_cc_max",
                "trail_intensity_sum",
            ):
                if left.get(key) != right.get(key):
                    raise ValueError(f"{cls.__name__} snapshot mismatch for {key}")


DOMAIN_REGISTRY = {
    LatticeDomain.name: LatticeDomain,
    TseitinDomain.name: TseitinDomain,
    AutomatonDomain.name: AutomatonDomain,
    TurbulenceDomain.name: TurbulenceDomain,
    InverseGenesisDomain.name: InverseGenesisDomain,
    GenesisCompressionDomain.name: GenesisCompressionDomain,
}
