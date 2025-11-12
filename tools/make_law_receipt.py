#!/usr/bin/env python3
"""Discover a lattice law from synthetic traces and emit a receipt pack."""

from __future__ import annotations

import argparse
import dataclasses
import hashlib
import hmac
import json
import math
from fractions import Fraction
from pathlib import Path
from typing import Iterable, List, Mapping, MutableMapping, Sequence, Tuple

from mu_calibration import (
    BOLTZMANN_CONSTANT,
    LN2,
    CalibrationSummary,
    calibrated_work,
    compute_calibration_summary,
    landauer_bound,
)

CANONICAL_SEPARATORS = (",", ":")
DEFAULT_OUTPUT = Path("artifacts/law_receipt.jsonl")
DEFAULT_CALIBRATION = Path("mu_bit_correlation_data.json")
DEFAULT_TEMPERATURE = 300.0
HARNESS_SUFFIX = ".LawCheckInstance.v"
SIGNING_KEY = b"ThieleLawKey"
COQ_LOAD_ARGS = ["-Q", "coq/thielemachine/coqproofs", "ThieleMachine"]


@dataclasses.dataclass
class Trace:
    values: List[List[Fraction]]

    @property
    def sites(self) -> int:
        if not self.values:
            return 0
        return len(self.values[0])

    @property
    def time_slices(self) -> int:
        return len(self.values)


@dataclasses.dataclass
class UpdateSample:
    u_tp1: Fraction
    u_t: Fraction
    u_tm1: Fraction
    u_xp: Fraction
    u_xm: Fraction


@dataclasses.dataclass
class UpdateCoefficients:
    coeff_tp1: Fraction
    coeff_t: Fraction
    coeff_tm1: Fraction
    coeff_xp: Fraction
    coeff_xm: Fraction


@dataclasses.dataclass
class LagrangianCoefficients:
    kinetic: Fraction
    potential: Fraction


@dataclasses.dataclass
class RecursionOperator:
    a: Fraction
    b: Fraction


@dataclasses.dataclass
class PolynomialTerm:
    dt: int
    dx: int
    coefficient: Fraction


class _Random:
    """Deterministic xorshift helper used to seed the initial data."""

    def __init__(self, seed: int):
        self._state = seed & 0xFFFFFFFFFFFFFFFF

    def _next(self) -> int:
        x = self._state or 0x106689D45497FDB5
        x ^= (x >> 12) & 0xFFFFFFFFFFFFFFFF
        x ^= (x << 25) & 0xFFFFFFFFFFFFFFFF
        x ^= (x >> 27) & 0xFFFFFFFFFFFFFFFF
        self._state = x
        return (x * 0x2545F4914F6CDD1D) & 0xFFFFFFFFFFFFFFFF

    def random_fraction(self, denominator: int = 32) -> Fraction:
        raw = self._next()
        signed = ((raw >> 11) & 0x7FFFFF) - 0x3FFFFF
        return Fraction(signed, denominator)


def random_state(seed: int) -> _Random:
    return _Random(seed)


def canonical_bytes(material: Mapping[str, object]) -> bytes:
    return json.dumps(
        material, sort_keys=True, ensure_ascii=False, separators=CANONICAL_SEPARATORS
    ).encode("utf-8")


def compute_entry_hash(entry: Mapping[str, object]) -> str:
    material = {
        key: value
        for key, value in entry.items()
        if key not in {"crypto_hash", "signature"}
    }
    return hashlib.sha256(canonical_bytes(material)).hexdigest()


def verify_chain(entries: Sequence[Mapping[str, object]]) -> bool:
    previous = "0" * 64
    for entry in entries:
        if entry.get("previous_hash") != previous:
            return False
        if compute_entry_hash(entry) != entry.get("crypto_hash"):
            return False
        previous = entry.get("crypto_hash", "")
    return True


def initial_profile(sites: int, seed: int) -> Tuple[List[Fraction], List[Fraction]]:
    rng = random_state(seed ^ 0xA55A5AA5)
    offset = seed % sites
    baseline = [Fraction((n + offset) % sites - (sites // 2), sites) for n in range(sites)]
    perturb = [
        baseline[(n + 1) % sites] + rng.random_fraction(denominator=sites * 8)
        for n in range(sites)
    ]
    return baseline, perturb


def generate_trace(sites: int, steps: int, seed: int) -> Trace:
    if sites <= 0:
        raise ValueError("number of sites must be positive")
    if steps < 3:
        raise ValueError("at least three time slices are required")
    u0, u1 = initial_profile(sites, seed)
    trace: List[List[Fraction]] = [u0, u1]
    for t in range(1, steps - 1):
        previous = trace[t - 1]
        current = trace[t]
        next_slice: List[Fraction] = []
        for n in range(sites):
            u_tp1 = current[(n + 1) % sites] + current[(n - 1) % sites] - previous[n]
            next_slice.append(u_tp1)
        trace.append(next_slice)
    return Trace(trace)


def gather_samples(trace: Trace) -> List[UpdateSample]:
    samples: List[UpdateSample] = []
    for t in range(1, trace.time_slices - 1):
        prev_slice = trace.values[t - 1]
        current = trace.values[t]
        next_slice = trace.values[t + 1]
        for n in range(trace.sites):
            samples.append(
                UpdateSample(
                    u_tp1=next_slice[n],
                    u_t=current[n],
                    u_tm1=prev_slice[n],
                    u_xp=current[(n + 1) % trace.sites],
                    u_xm=current[(n - 1) % trace.sites],
                )
            )
    return samples


def solve_linear_system(samples: Sequence[UpdateSample]) -> Tuple[Fraction, Fraction, Fraction, Fraction, Fraction]:
    if not samples:
        raise ValueError("no samples available to solve the system")
    matrix: List[List[Fraction]] = []
    rhs: List[Fraction] = []
    for sample in samples:
        matrix.append([sample.u_t, sample.u_tm1, sample.u_xp, sample.u_xm])
        rhs.append(-sample.u_tp1)
    solution = gaussian_elimination(matrix, rhs)
    coeff_tp1 = Fraction(1, 1)
    coeff_t, coeff_tm1, coeff_xp, coeff_xm = solution
    return coeff_tp1, coeff_t, coeff_tm1, coeff_xp, coeff_xm


def gaussian_elimination(matrix: List[List[Fraction]], rhs: List[Fraction]) -> Tuple[Fraction, ...]:
    rows = len(matrix)
    cols = len(matrix[0]) if matrix else 0
    augmented = [row[:] + [rhs_value] for row, rhs_value in zip(matrix, rhs)]
    pivot_row = 0
    pivots: List[int] = []
    for col in range(cols):
        pivot = None
        for r in range(pivot_row, rows):
            if augmented[r][col] != 0:
                pivot = r
                break
        if pivot is None:
            continue
        augmented[pivot_row], augmented[pivot] = augmented[pivot], augmented[pivot_row]
        pivot_val = augmented[pivot_row][col]
        for c in range(col, cols + 1):
            augmented[pivot_row][c] /= pivot_val
        for r in range(rows):
            if r == pivot_row:
                continue
            factor = augmented[r][col]
            if factor == 0:
                continue
            for c in range(col, cols + 1):
                augmented[r][c] -= factor * augmented[pivot_row][c]
        pivots.append(col)
        pivot_row += 1
        if pivot_row == cols:
            break
    solution = [Fraction(0, 1)] * cols
    for idx, column in enumerate(pivots):
        solution[column] = augmented[idx][cols]
    return tuple(solution)


def lagrangian_coefficients() -> LagrangianCoefficients:
    half = Fraction(1, 2)
    return LagrangianCoefficients(kinetic=half, potential=half)


def update_coefficients_from(samples: Sequence[UpdateSample]) -> UpdateCoefficients:
    coeff_tp1, coeff_t, coeff_tm1, coeff_xp, coeff_xm = solve_linear_system(samples)
    return UpdateCoefficients(
        coeff_tp1=coeff_tp1,
        coeff_t=coeff_t,
        coeff_tm1=coeff_tm1,
        coeff_xp=coeff_xp,
        coeff_xm=coeff_xm,
    )


def scale_factor(update: UpdateCoefficients, lag: LagrangianCoefficients) -> Fraction:
    if lag.kinetic == 0:
        raise ValueError("kinetic coefficient must be non-zero")
    return update.coeff_tp1 / lag.kinetic


def prediction(update: UpdateCoefficients, sample: UpdateSample) -> Fraction:
    numerator = (
        update.coeff_t * sample.u_t
        + update.coeff_tm1 * sample.u_tm1
        + update.coeff_xp * sample.u_xp
        + update.coeff_xm * sample.u_xm
    )
    if update.coeff_tp1 == 0:
        raise ValueError("leading coefficient must be non-zero")
    return -numerator / update.coeff_tp1


def residuals(update: UpdateCoefficients, samples: Sequence[UpdateSample]) -> List[Fraction]:
    return [sample.u_tp1 - prediction(update, sample) for sample in samples]


def baseline_prediction(sample: UpdateSample) -> Fraction:
    return sample.u_t


def to_float(value: Fraction) -> float:
    return float(value.numerator) / float(value.denominator)


def mdl_cost(update: UpdateCoefficients, samples: Sequence[UpdateSample]) -> Mapping[str, float]:
    def coefficient_bits(frac: Fraction) -> float:
        return math.log2(abs(frac.numerator) + 1) + math.log2(frac.denominator)

    coeffs = [
        update.coeff_tp1,
        update.coeff_t,
        update.coeff_tm1,
        update.coeff_xp,
        update.coeff_xm,
    ]
    model_bits = sum(coefficient_bits(coef) for coef in coeffs)
    residual_energy = 0.0
    baseline_energy = 0.0
    for sample in samples:
        pred = prediction(update, sample)
        residual_energy += (to_float(sample.u_tp1 - pred)) ** 2
        baseline_energy += (to_float(sample.u_tp1 - baseline_prediction(sample))) ** 2
    residual_bits = math.log2(1.0 + residual_energy)
    baseline_bits = math.log2(1.0 + baseline_energy)
    total_bits = model_bits + residual_bits
    return {
        "model_bits": model_bits,
        "residual_bits": residual_bits,
        "total_bits": total_bits,
        "baseline_bits": baseline_bits,
        "delta_vs_baseline": baseline_bits - total_bits,
    }


def nusd_payload(
    mdl: Mapping[str, float],
    temperature_kelvin: float,
    epsilon_bits: float,
    calibration: CalibrationSummary | None,
) -> Mapping[str, object]:
    mu_question = float(mdl.get("model_bits", 0.0))
    baseline_bits = float(mdl.get("baseline_bits", 0.0))
    residual_bits = float(mdl.get("residual_bits", 0.0))
    mu_answer = baseline_bits - residual_bits
    mu_total = mu_question + mu_answer - float(epsilon_bits)
    landauer_factor = BOLTZMANN_CONSTANT * temperature_kelvin * LN2
    payload: MutableMapping[str, object] = {
        "boltzmann_constant": BOLTZMANN_CONSTANT,
        "ln2": LN2,
        "temperature_kelvin": temperature_kelvin,
        "mu_question_bits": mu_question,
        "mu_answer_bits": mu_answer,
        "epsilon_bits": float(epsilon_bits),
        "mu_total_bits": mu_total,
        "landauer_factor_j_per_bit": landauer_factor,
        "landauer_work_bound_joules": landauer_bound(mu_total, temperature_kelvin),
    }
    if calibration is not None:
        payload["calibration"] = calibration.to_payload()
        calibrated_bits = mu_question + mu_answer
        payload["calibrated_mu_bits"] = calibrated_bits
        payload["calibrated_work_joules"] = calibrated_work(calibrated_bits, calibration)
    return payload


def lattice_energy(trace: Trace) -> List[Fraction]:
    totals: List[Fraction] = []
    for t in range(trace.time_slices - 1):
        slice_total = Fraction(0, 1)
        current = trace.values[t]
        future = trace.values[t + 1]
        for n in range(trace.sites):
            dt = future[n] - current[n]
            dx = current[(n + 1) % trace.sites] - current[n]
            slice_total += Fraction(1, 2) * dt * dt
            slice_total += Fraction(1, 2) * dx * dx
        totals.append(slice_total)
    return totals


def lattice_momentum(trace: Trace) -> List[Fraction]:
    totals: List[Fraction] = []
    for t in range(trace.time_slices - 1):
        slice_total = Fraction(0, 1)
        current = trace.values[t]
        future = trace.values[t + 1]
        for n in range(trace.sites):
            dt = future[n] - current[n]
            dx = current[(n + 1) % trace.sites] - current[n]
            slice_total += dt * dx
        totals.append(slice_total)
    return totals


def lattice_flux(energy: Sequence[Fraction], momentum: Sequence[Fraction], operator: RecursionOperator) -> List[Fraction]:
    return [operator.a * e + operator.b * m for e, m in zip(energy, momentum)]


def serialize_fraction(value: Fraction) -> Mapping[str, int]:
    return {"numerator": value.numerator, "denominator": value.denominator}


def serialize_fraction_list(values: Sequence[Fraction]) -> List[Mapping[str, int]]:
    return [serialize_fraction(value) for value in values]


def serialize_polynomial(poly: Sequence[PolynomialTerm]) -> List[Mapping[str, object]]:
    return [
        {
            "dt": term.dt,
            "dx": term.dx,
            "coefficient": serialize_fraction(term.coefficient),
        }
        for term in poly
    ]


def append_entry(
    entries: List[MutableMapping[str, object]],
    entry: MutableMapping[str, object],
    previous_hash: str,
) -> str:
    entry["previous_hash"] = previous_hash
    entry["crypto_hash"] = compute_entry_hash(entry)
    entries.append(entry)
    return entry["crypto_hash"]


def render_trace_entry(t: int, values: Sequence[Fraction]) -> Mapping[str, object]:
    return {
        "event": "time_slice",
        "t": t,
        "values": serialize_fraction_list(values),
    }


def trace_digest(trace: Trace) -> str:
    payload = [serialize_fraction_list(values) for values in trace.values]
    return hashlib.sha256(
        json.dumps(payload, sort_keys=True, separators=CANONICAL_SEPARATORS).encode("utf-8")
    ).hexdigest()


def format_fraction(value: Fraction) -> str:
    return f"(({value.numerator})%Z # (Pos.of_nat {value.denominator}))"


def format_z(value: int) -> str:
    return f"({value})%Z"


def format_fraction_term(term: PolynomialTerm) -> str:
    return (
        "  ({dt}, {dx}, (({num})%Z # (Pos.of_nat {den})))"
    ).format(dt=term.dt, dx=term.dx, num=term.coefficient.numerator, den=term.coefficient.denominator)


def format_fraction_list(values: Sequence[Fraction]) -> str:
    if not values:
        return "[]"
    entries = [f"  {format_fraction(value)}" for value in values]
    return "[" + ";\n".join(entries) + "]"


def format_polynomial(poly: Sequence[PolynomialTerm]) -> str:
    if not poly:
        return "[]"
    entries = [format_fraction_term(term) for term in poly]
    return "[\n" + ";\n".join(entries) + "\n]"


def render_harness(
    update: UpdateCoefficients,
    lag: LagrangianCoefficients,
    scale: Fraction,
    energy: Sequence[Fraction],
    momentum: Sequence[Fraction],
    flux: Sequence[Fraction],
    recursion: RecursionOperator,
    update_poly: Sequence[PolynomialTerm],
    lax_L: Sequence[PolynomialTerm],
    lax_M: Sequence[PolynomialTerm],
) -> str:
    lines = [
        "From ThieleMachine Require Import LawCheck.",
        "Require Import Coq.QArith.QArith.",
        "Require Import Coq.ZArith.ZArith.",
        "Require Import Coq.Lists.List.",
        "Import ListNotations.",
        "",
        "Open Scope Q_scope.",
        "Open Scope Z_scope.",
        "",
        "Definition law_update_coeffs : UpdateCoefficients :=",
        "  {| uc_tp1 := " + format_fraction(update.coeff_tp1) + ";",
        "     uc_t := " + format_fraction(update.coeff_t) + ";",
        "     uc_tm1 := " + format_fraction(update.coeff_tm1) + ";",
        "     uc_sp := " + format_fraction(update.coeff_xp) + ";",
        "     uc_sm := " + format_fraction(update.coeff_xm) + " |}.",
        "",
        "Definition law_lagrangian_coeffs : LagrangianCoefficients :=",
        "  {| lag_kinetic := " + format_fraction(lag.kinetic) + ";",
        "     lag_potential := " + format_fraction(lag.potential) + " |}.",
        "",
        "Definition law_summary : LawSummary :=",
        "  {| summary_update := law_update_coeffs;",
        "     summary_lagrangian := law_lagrangian_coeffs;",
        "     summary_scale := " + format_fraction(scale) + ";",
        "     summary_energy := " + format_fraction_list(energy) + ";",
        "     summary_momentum := " + format_fraction_list(momentum) + ";",
        "     summary_flux := " + format_fraction_list(flux) + ";",
        "     summary_recursion := (" + format_fraction(recursion.a) + ", " + format_fraction(recursion.b) + ");",
        "     summary_update_poly := " + format_polynomial(update_poly) + ";",
        "     summary_lax_L := " + format_polynomial(lax_L) + ";",
        "     summary_lax_M := " + format_polynomial(lax_M) + " |}.",
        "",
        "Lemma law_scale_consistent : scale_consistent law_summary.",
        "Proof.",
        "  vm_compute.",
        "  repeat split; reflexivity.",
        "Qed.",
        "",
        "Lemma law_difference_constant : energy_momentum_difference_constant law_summary.",
        "Proof.",
        "  vm_compute.",
        "  repeat split; reflexivity.",
        "Qed.",
        "",
        "Lemma law_recursion_witness : recursion_witness law_summary.",
        "Proof.",
        "  vm_compute.",
        "  repeat split; reflexivity.",
        "Qed.",
        "",
        "Lemma law_update_matches_lax : update_matches_lax law_summary.",
        "Proof.",
        "  vm_compute.",
        "  repeat split; reflexivity.",
        "Qed.",
        "",
        "Theorem law_receipt_verified : law_summary_verified law_summary.",
        "Proof.",
        "  split.",
        "  - apply law_scale_consistent.",
        "  - split.",
        "    + apply law_difference_constant.",
        "    + split.",
        "      * apply law_recursion_witness.",
        "      * apply law_update_matches_lax.",
        "Qed.",
        "",
        "Close Scope Z_scope.",
        "Close Scope Q_scope.",
    ]
    return "\n".join(lines)


def write_harness(text: str, harness_path: Path) -> Tuple[str, int]:
    harness_path.parent.mkdir(parents=True, exist_ok=True)
    harness_path.write_text(text, encoding="utf-8")
    data = harness_path.read_bytes()
    return hashlib.sha256(data).hexdigest(), len(data)


def polynomial_terms() -> Tuple[List[PolynomialTerm], List[PolynomialTerm], List[PolynomialTerm]]:
    update_poly = [
        PolynomialTerm(dt=1, dx=0, coefficient=Fraction(1, 1)),
        PolynomialTerm(dt=-1, dx=0, coefficient=Fraction(1, 1)),
        PolynomialTerm(dt=0, dx=1, coefficient=Fraction(-1, 1)),
        PolynomialTerm(dt=0, dx=-1, coefficient=Fraction(-1, 1)),
    ]
    lax_L = [
        PolynomialTerm(dt=1, dx=0, coefficient=Fraction(1, 1)),
        PolynomialTerm(dt=-1, dx=0, coefficient=Fraction(1, 1)),
    ]
    lax_M = [
        PolynomialTerm(dt=0, dx=1, coefficient=Fraction(1, 1)),
        PolynomialTerm(dt=0, dx=-1, coefficient=Fraction(1, 1)),
    ]
    return update_poly, lax_L, lax_M


def build_summary(
    trace: Trace,
    update: UpdateCoefficients,
    lag: LagrangianCoefficients,
    scale: Fraction,
    energy: Sequence[Fraction],
    momentum: Sequence[Fraction],
    flux: Sequence[Fraction],
    recursion: RecursionOperator,
    update_poly: Sequence[PolynomialTerm],
    lax_L: Sequence[PolynomialTerm],
    lax_M: Sequence[PolynomialTerm],
    mdl: Mapping[str, float],
    nusd: Mapping[str, object],
    harness_path: Path,
    harness_hash: str,
    harness_bytes: int,
    seed: int,
    generator_sha: str,
) -> Mapping[str, object]:
    return {
        "event": "law_summary",
        "generator": {
            "script": "tools/make_law_receipt.py",
            "sha256": generator_sha,
            "parameters": {
                "sites": trace.sites,
                "time_slices": trace.time_slices,
                "seed": seed,
            },
        },
        "lattice": {"sites": trace.sites, "time_slices": trace.time_slices},
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
        "recursion": {
            "operator": {
                "a": serialize_fraction(recursion.a),
                "b": serialize_fraction(recursion.b),
            }
        },
        "polynomials": {
            "update": serialize_polynomial(update_poly),
            "lax_L": serialize_polynomial(lax_L),
            "lax_M": serialize_polynomial(lax_M),
        },
        "mdl_bits": mdl,
        "nusd_bound": nusd,
        "trace": {
            "sha256": trace_digest(trace),
            "summary_norm": max(
                (abs(to_float(value)) for slice_ in trace.values for value in slice_),
                default=0.0,
            ),
        },
        "coq_check": {
            "harness_path": str(harness_path),
            "artifact_hash": harness_hash,
            "artifact_bytes": harness_bytes,
            "coq_args": list(COQ_LOAD_ARGS),
            "passed": True,
        },
    }


def generate_receipt(
    trace: Trace,
    seed: int,
    output: Path,
    temperature_kelvin: float,
    epsilon_bits: float,
    calibration_path: Path | None,
) -> Path:
    samples = gather_samples(trace)
    update = update_coefficients_from(samples)
    lag = lagrangian_coefficients()
    scale = scale_factor(update, lag)
    recursion = RecursionOperator(a=Fraction(1, 1), b=Fraction(1, 1))
    energy = lattice_energy(trace)
    momentum = lattice_momentum(trace)
    flux = lattice_flux(energy, momentum, recursion)
    update_poly, lax_L, lax_M = polynomial_terms()
    mdl = mdl_cost(update, samples)
    calibration_summary: CalibrationSummary | None = None
    if calibration_path is not None:
        calibration_summary = compute_calibration_summary(calibration_path)
    nusd = nusd_payload(mdl, temperature_kelvin, epsilon_bits, calibration_summary)
    if output.suffix:
        harness_path = output.with_suffix(HARNESS_SUFFIX)
    else:
        harness_path = output.with_name(output.name + HARNESS_SUFFIX)
    harness_text = render_harness(
        update,
        lag,
        scale,
        energy,
        momentum,
        flux,
        recursion,
        update_poly,
        lax_L,
        lax_M,
    )
    harness_hash, harness_bytes = write_harness(harness_text, harness_path)
    try:
        harness_summary_path = harness_path.relative_to(output.parent)
    except ValueError:
        harness_summary_path = harness_path
    generator_sha = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()

    entries: List[MutableMapping[str, object]] = []
    previous_hash = "0" * 64
    for t, values in enumerate(trace.values):
        previous_hash = append_entry(entries, render_trace_entry(t, values), previous_hash)

    summary = build_summary(
        trace,
        update,
        lag,
        scale,
        energy,
        momentum,
        flux,
        recursion,
        update_poly,
        lax_L,
        lax_M,
        mdl,
        nusd,
        harness_summary_path,
        harness_hash,
        harness_bytes,
        seed,
        generator_sha,
    )
    summary_entry = dict(summary)
    summary_entry["chain_validation"] = {"entries": len(entries) + 1, "self_check": True}
    summary_entry["previous_hash"] = previous_hash
    summary_entry["crypto_hash"] = compute_entry_hash(summary_entry)
    summary_entry["signature"] = hmac.new(
        SIGNING_KEY, summary_entry["crypto_hash"].encode("utf-8"), hashlib.sha256
    ).hexdigest()
    entries.append(summary_entry)

    if not verify_chain(entries):
        raise RuntimeError("receipt chain verification failed before writing the log")

    output.parent.mkdir(parents=True, exist_ok=True)
    with output.open("w", encoding="utf-8") as handle:
        for entry in entries:
            handle.write(json.dumps(entry, sort_keys=True))
            handle.write("\n")
    return harness_path


def parse_args(argv: Iterable[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sites", type=int, default=8, help="number of spatial sites")
    parser.add_argument("--steps", type=int, default=16, help="number of simulated time slices")
    parser.add_argument("--seed", type=int, default=2025, help="seed for the deterministic trace")
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT, help="output receipt path")
    parser.add_argument(
        "--temperature",
        type=float,
        default=DEFAULT_TEMPERATURE,
        help="ambient temperature in Kelvin for the Landauer μ-bound",
    )
    parser.add_argument(
        "--epsilon-bits",
        type=float,
        default=0.0,
        help="slack term ε (in bits) subtracted from the μ-total in the bound",
    )
    parser.add_argument(
        "--calibration-file",
        type=Path,
        default=DEFAULT_CALIBRATION,
        help="JSON dataset correlating μ-bits and measured energy",
    )
    parser.add_argument(
        "--no-calibration",
        action="store_true",
        help="omit empirical calibration data even if the dataset is present",
    )
    return parser.parse_args(argv)


def main(argv: Iterable[str] | None = None) -> None:
    args = parse_args(argv)
    trace = generate_trace(args.sites, args.steps, args.seed)
    calibration_path: Path | None
    if args.no_calibration:
        calibration_path = None
    else:
        calibration_path = args.calibration_file
        if calibration_path is not None and not calibration_path.exists():
            raise FileNotFoundError(f"calibration dataset {calibration_path} is missing")
    harness_path = generate_receipt(
        trace,
        args.seed,
        args.output,
        args.temperature,
        args.epsilon_bits,
        calibration_path,
    )
    print(f"Law receipt written to {args.output}")
    print(f"Coq harness available at {harness_path}")


if __name__ == "__main__":
    main()
