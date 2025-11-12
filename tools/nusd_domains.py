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


DOMAIN_REGISTRY = {
    LatticeDomain.name: LatticeDomain,
    TseitinDomain.name: TseitinDomain,
    AutomatonDomain.name: AutomatonDomain,
    TurbulenceDomain.name: TurbulenceDomain,
}
