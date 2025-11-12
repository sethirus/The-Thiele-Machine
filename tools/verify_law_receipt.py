#!/usr/bin/env python3
"""Verify an integrable law receipt and re-run the Coq harness."""

from __future__ import annotations

import argparse
import hashlib
import hmac
import json
import math
import subprocess
import sys
from fractions import Fraction
from pathlib import Path
from typing import Iterable, List, Mapping, Sequence

from make_law_receipt import (
    COQ_LOAD_ARGS,
    RecursionOperator,
    Trace,
    compute_entry_hash,
    gather_samples,
    lagrangian_coefficients,
    lattice_energy,
    lattice_flux,
    lattice_momentum,
    mdl_cost,
    polynomial_terms,
    scale_factor,
    SIGNING_KEY,
    trace_digest,
    update_coefficients_from,
    verify_chain,
)
from mu_calibration import (
    BOLTZMANN_CONSTANT,
    LN2,
    calibrated_work,
    compute_calibration_summary,
    landauer_bound,
)


def load_entries(path: Path) -> List[Mapping[str, object]]:
    entries: List[Mapping[str, object]] = []
    with path.open("r", encoding="utf-8") as handle:
        for line in handle:
            material = line.strip()
            if not material:
                continue
            entries.append(json.loads(material))
    if not entries:
        raise ValueError(f"receipt {path} is empty")
    return entries


def ensure(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def fraction_from(payload: Mapping[str, int]) -> Fraction:
    return Fraction(payload["numerator"], payload["denominator"])


def load_trace(entries: Sequence[Mapping[str, object]], sites: int) -> Trace:
    values: List[List[Fraction]] = []
    for index, entry in enumerate(entries):
        ensure(entry.get("event") == "time_slice", f"entry {index} is not a time_slice event")
        ensure(entry.get("t") == index, f"unexpected time index {entry.get('t')} at entry {index}")
        row = [fraction_from(value) for value in entry.get("values", [])]
        ensure(len(row) == sites, f"time slice {index} has {len(row)} values but expected {sites}")
        values.append(row)
    return Trace(values)


def compare_fraction_lists(expected: Sequence[Fraction], recorded: Sequence[Mapping[str, int]], label: str) -> None:
    ensure(len(expected) == len(recorded), f"{label} length mismatch")
    for index, (value, payload) in enumerate(zip(expected, recorded)):
        ensure(value == fraction_from(payload), f"{label} mismatch at index {index}")


def compare_polynomials(expected, recorded, label: str) -> None:
    ensure(len(expected) == len(recorded), f"{label} polynomial length mismatch")
    for index, (term, payload) in enumerate(zip(expected, recorded)):
        ensure(term.dt == payload.get("dt"), f"{label} dt mismatch at index {index}")
        ensure(term.dx == payload.get("dx"), f"{label} dx mismatch at index {index}")
        ensure(
            term.coefficient == fraction_from(payload.get("coefficient", {})),
            f"{label} coefficient mismatch at index {index}",
        )


def verify_summary(
    receipt_path: Path,
    entries: List[Mapping[str, object]],
    summary: Mapping[str, object],
    skip_coq: bool,
    coq_binary: str,
) -> None:
    ensure(summary.get("event") == "law_summary", "final entry is not a law summary")
    ensure(verify_chain(entries), "hash chain verification failed")
    ensure(
        compute_entry_hash(summary) == summary.get("crypto_hash"),
        "summary crypto_hash mismatch",
    )
    expected_signature = hmac.new(
        SIGNING_KEY, summary["crypto_hash"].encode("utf-8"), hashlib.sha256
    ).hexdigest()
    ensure(summary.get("signature") == expected_signature, "invalid HMAC signature")

    generator = summary.get("generator", {})
    ensure(generator, "missing generator metadata")
    ensure(
        generator.get("script") == "tools/make_law_receipt.py",
        "unexpected generator script",
    )
    generator_sha = generator.get("sha256")
    ensure(generator_sha, "missing generator sha256")
    ensure(
        hashlib.sha256(Path("tools/make_law_receipt.py").read_bytes()).hexdigest()
        == generator_sha,
        "generator sha256 mismatch",
    )
    parameters = generator.get("parameters", {})
    ensure(parameters, "missing generator parameters")
    sites = int(parameters.get("sites", 0))
    time_slices = int(parameters.get("time_slices", 0))
    ensure("seed" in parameters, "missing seed parameter")
    seed = int(parameters.get("seed", 0))
    ensure(sites > 0, "invalid number of sites in parameters")
    ensure(time_slices > 0, "invalid number of time slices in parameters")

    chain_validation = summary.get("chain_validation", {})
    ensure(chain_validation.get("self_check") is True, "chain self_check flag missing")
    ensure(chain_validation.get("entries") == len(entries), "chain length mismatch")

    time_entries = entries[:-1]
    ensure(len(time_entries) == time_slices, "time slice count mismatch")
    trace = load_trace(time_entries, sites)
    ensure(trace.time_slices == time_slices, "trace length mismatch")

    trace_info = summary.get("trace", {})
    ensure(trace_digest(trace) == trace_info.get("sha256"), "trace digest mismatch")

    samples = gather_samples(trace)
    update = update_coefficients_from(samples)

    coeff_payload = summary.get("coefficients", {})
    update_payload = coeff_payload.get("update", {})
    ensure(update.coeff_tp1 == fraction_from(update_payload.get("coeff_tp1", {})), "coeff_tp1 mismatch")
    ensure(update.coeff_t == fraction_from(update_payload.get("coeff_t", {})), "coeff_t mismatch")
    ensure(update.coeff_tm1 == fraction_from(update_payload.get("coeff_tm1", {})), "coeff_tm1 mismatch")
    ensure(update.coeff_xp == fraction_from(update_payload.get("coeff_xp", {})), "coeff_xp mismatch")
    ensure(update.coeff_xm == fraction_from(update_payload.get("coeff_xm", {})), "coeff_xm mismatch")

    lag_payload = coeff_payload.get("lagrangian", {})
    lag = lagrangian_coefficients()
    ensure(lag.kinetic == fraction_from(lag_payload.get("kinetic", {})), "lag kinetic mismatch")
    ensure(lag.potential == fraction_from(lag_payload.get("potential", {})), "lag potential mismatch")

    scale_payload = coeff_payload.get("scale_factor", {})
    recorded_scale = fraction_from(scale_payload)
    ensure(scale_factor(update, lag) == recorded_scale, "scale factor mismatch")

    energy = lattice_energy(trace)
    momentum = lattice_momentum(trace)
    recursion_payload = summary.get("recursion", {}).get("operator", {})
    recursion = RecursionOperator(
        a=fraction_from(recursion_payload.get("a", {})),
        b=fraction_from(recursion_payload.get("b", {})),
    )
    flux = lattice_flux(energy, momentum, recursion)

    conservation = summary.get("conservation", {})
    compare_fraction_lists(energy, conservation.get("energy", []), "energy totals")
    compare_fraction_lists(momentum, conservation.get("momentum", []), "momentum totals")
    compare_fraction_lists(flux, conservation.get("flux", []), "flux totals")

    update_poly, lax_L, lax_M = polynomial_terms()
    polynomials = summary.get("polynomials", {})
    compare_polynomials(update_poly, polynomials.get("update", []), "update polynomial")
    compare_polynomials(lax_L, polynomials.get("lax_L", []), "lax_L polynomial")
    compare_polynomials(lax_M, polynomials.get("lax_M", []), "lax_M polynomial")

    mdl = mdl_cost(update, samples)
    mdl_summary = summary.get("mdl_bits", {})
    for key, value in mdl.items():
        ensure(
            math.isclose(mdl_summary.get(key, 0.0), value, rel_tol=1e-9, abs_tol=1e-9),
            f"mdl mismatch for {key}",
        )

    nusd = summary.get("nusd_bound", {})
    ensure(nusd, "nusd bound block missing from summary")
    mu_question = mdl["model_bits"]
    mu_answer = mdl["baseline_bits"] - mdl["residual_bits"]
    ensure(
        math.isclose(nusd.get("mu_question_bits", 0.0), mu_question, rel_tol=1e-9, abs_tol=1e-9),
        "μ-question bits mismatch",
    )
    ensure(
        math.isclose(nusd.get("mu_answer_bits", 0.0), mu_answer, rel_tol=1e-9, abs_tol=1e-9),
        "μ-answer bits mismatch",
    )
    epsilon_bits = float(nusd.get("epsilon_bits", 0.0))
    mu_total = mu_question + mu_answer - epsilon_bits
    ensure(
        math.isclose(nusd.get("mu_total_bits", 0.0), mu_total, rel_tol=1e-9, abs_tol=1e-9),
        "μ-total bits mismatch",
    )
    temperature = float(nusd.get("temperature_kelvin", 0.0))
    ensure(temperature > 0.0, "non-positive temperature recorded in nusd bound")
    expected_factor = BOLTZMANN_CONSTANT * temperature * LN2
    ensure(
        math.isclose(
            nusd.get("landauer_factor_j_per_bit", 0.0),
            expected_factor,
            rel_tol=1e-9,
            abs_tol=1e-15,
        ),
        "Landauer factor mismatch",
    )
    expected_work = landauer_bound(mu_total, temperature)
    ensure(
        math.isclose(
            nusd.get("landauer_work_bound_joules", 0.0),
            expected_work,
            rel_tol=1e-9,
            abs_tol=1e-15,
        ),
        "Landauer work mismatch",
    )

    calibration_payload = nusd.get("calibration")
    if calibration_payload:
        source_str = calibration_payload.get("source_path", "")
        candidate = Path(source_str)
        if not candidate.is_absolute():
            receipt_dir = receipt_path.parent.resolve()
            possibilities = [receipt_dir / candidate, Path.cwd() / candidate]
            for option in possibilities:
                if option.exists():
                    candidate = option.resolve()
                    break
        ensure(candidate.exists(), f"calibration dataset {source_str} is missing")
        dataset_bytes = candidate.read_bytes()
        ensure(
            hashlib.sha256(dataset_bytes).hexdigest() == calibration_payload.get("sha256"),
            "calibration dataset sha256 mismatch",
        )
        summary_stats = compute_calibration_summary(candidate)
        ensure(
            calibration_payload.get("sample_count") == summary_stats.sample_count,
            "calibration sample count mismatch",
        )
        ensure(
            math.isclose(
                calibration_payload.get("mean_energy_per_mu_bit_joules", 0.0),
                summary_stats.mean_energy_per_mu_bit_joules,
                rel_tol=1e-9,
                abs_tol=1e-15,
            ),
            "calibration mean energy mismatch",
        )
        ensure(
            math.isclose(
                calibration_payload.get("std_energy_per_mu_bit_joules", 0.0),
                summary_stats.std_energy_per_mu_bit_joules,
                rel_tol=1e-9,
                abs_tol=1e-15,
            ),
            "calibration std energy mismatch",
        )
        ensure(
            math.isclose(
                calibration_payload.get("total_energy_joules", 0.0),
                summary_stats.total_energy_joules,
                rel_tol=1e-9,
                abs_tol=1e-15,
            ),
            "calibration total energy mismatch",
        )
        ensure(
            math.isclose(
                calibration_payload.get("total_mu_bits", 0.0),
                summary_stats.total_mu_bits,
                rel_tol=1e-9,
                abs_tol=1e-9,
            ),
            "calibration total μ mismatch",
        )
        calibrated_bits = mu_question + mu_answer
        ensure(
            math.isclose(
                nusd.get("calibrated_mu_bits", 0.0),
                calibrated_bits,
                rel_tol=1e-9,
                abs_tol=1e-9,
            ),
            "calibrated μ bits mismatch",
        )
        expected_calibrated = calibrated_work(calibrated_bits, summary_stats)
        ensure(
            math.isclose(
                nusd.get("calibrated_work_joules", 0.0),
                expected_calibrated,
                rel_tol=1e-9,
                abs_tol=1e-15,
            ),
            "calibrated work mismatch",
        )

    coq_check = summary.get("coq_check", {})
    harness_rel = coq_check.get("harness_path")
    ensure(harness_rel, "missing harness path in summary")
    harness_path = (receipt_path.parent / harness_rel).resolve()
    ensure(harness_path.exists(), f"Coq harness {harness_path} is missing")
    harness_hash = hashlib.sha256(harness_path.read_bytes()).hexdigest()
    ensure(harness_hash == coq_check.get("artifact_hash"), "harness hash mismatch")
    ensure(harness_path.stat().st_size == coq_check.get("artifact_bytes"), "harness size mismatch")
    ensure(coq_check.get("passed") is True, "coq harness status not recorded as passed")

    coq_args = list(coq_check.get("coq_args", []))
    ensure(coq_args == COQ_LOAD_ARGS, "stored coq args do not match generator defaults")

    if not skip_coq:
        command = [coq_binary, "-batch", *coq_args, "-l", str(harness_path)]
        completed = subprocess.run(command, capture_output=True, text=True)
        if completed.returncode != 0:
            sys.stderr.write(completed.stdout)
            sys.stderr.write(completed.stderr)
            raise RuntimeError("Coq harness execution failed")

    print("ALL CHECKS PASSED")


def parse_args(argv: Iterable[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("receipt", type=Path, help="path to the receipt JSONL file")
    parser.add_argument("--skip-coq", action="store_true", help="skip running the Coq harness")
    parser.add_argument("--coq-binary", default="coqtop", help="coq executable to invoke")
    return parser.parse_args(argv)


def main(argv: Iterable[str] | None = None) -> None:
    args = parse_args(argv)
    entries = load_entries(args.receipt)
    summary = entries[-1]
    verify_summary(args.receipt, entries, summary, args.skip_coq, args.coq_binary)


if __name__ == "__main__":
    main()
