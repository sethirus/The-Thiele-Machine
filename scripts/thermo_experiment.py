#!/usr/bin/env python3
"""
Thermodynamic bridge experiment harness.

This script runs small Ω→Ω′ workloads on the Python VM (and optionally the
extracted runner + RTL) to produce a reproducible dataset linking μ-paid to the
Landauer lower bound k_B*T*ln 2 * μ.

Outputs ``results/thermo_experiment.json`` with per-scenario results including:
- raw/effective μ totals per runner (python/extracted/rtl)
- Ω sizes and μ − log2(|Ω|/|Ω′|) slack
- Landauer lower bound at the configured temperature
- wall-clock runtime for the Python execution (proxy for measurability)

By default the script enforces non-zero μ from every runner once μ>0 is
produced by Python. Set ALLOW_MU_NORMALIZE=1 to adopt the Python μ when another
runner reports μ=0/None (the substitution is recorded in the output). Set
EVIDENCE_STRICT=1 to refuse normalization entirely and fail closed when any
layer emits μ=0/None.
"""
from __future__ import annotations

import argparse
import json
import math
import os
import subprocess
import time
from pathlib import Path
from typing import Dict, List, Tuple, TypedDict, Any, cast

from experiments.energy_meter import RaplEnergyMeter, rapl_available
from experiments.run_metadata import capture_run_metadata

from thielecpu.isa import Opcode

# Reuse the cross-layer helpers from the equivalence bundle script.
from scripts.equivalence_bundle import (  # type: ignore
    ALLOW_MU_NORMALIZE,
    EVIDENCE_STRICT,
    _encode_word,
    _run_extracted,
    _run_python_vm,
    _run_rtl,
)

REPO_ROOT = Path(__file__).resolve().parent.parent
RESULTS_PATH = REPO_ROOT / "results" / "thermo_experiment.json"

# Physical constants for the Landauer bound.
BOLTZMANN_CONSTANT = 1.380649e-23  # J/K
LN2 = math.log(2.0)
DEFAULT_TEMPERATURE_K = float(os.environ.get("THERMO_TEMPERATURE_K", 300.0))
DEFAULT_ENERGY_MODE = os.environ.get("THERMO_MEASURE_ENERGY", "").strip().lower() or "none"


class ProgramSpec(TypedDict):
    words: List[int]
    text: List[Tuple[str, str]]
    trace_lines: List[str]


def _scenario_program(region: List[int]) -> ProgramSpec:
    if len(region) != 1:
        raise AssertionError(
            "Thermo experiment currently exercises singleton partition discovery only; "
            "extend RTL encoding before using multi-element regions."
        )
    element = region[0]
    if element < 0 or element > 0xFF:
        raise AssertionError(f"Region element {element} out of 8-bit operand range for RTL encoding")

    region_text = "{" + ",".join(str(x) for x in region) + "}"

    # Canonical μ-cost for singleton PNEW under the spec:
    # popcount(region)=1 and the encoding cost uses bit_length(element).
    # Total mu_delta = 1 + bit_length(element).
    mu_delta = 1 + max(1, element.bit_length())

    program_words = [
        _encode_word(Opcode.PNEW.value, element, 0, mu_delta),
        _encode_word(Opcode.HALT.value, 0, 0, 0),
    ]
    program_text = [
        ("PNEW", f"{region_text} {mu_delta}"),
        ("HALT", ""),
    ]
    trace_lines = [
        f"PNEW {region_text} {mu_delta}",
    ]
    return ProgramSpec(words=program_words, text=program_text, trace_lines=trace_lines)


def _run_scenario(
    name: str,
    omega_before: int,
    omega_after: int,
    region: List[int],
    *,
    energy_mode: str,
    energy_repetitions: int,
) -> Dict[str, Any]:
    program: ProgramSpec = _scenario_program(region)
    init_regs = [0] * 32
    init_mem = [0] * 256

    meter = None
    energy_observable = "not_measured"
    if energy_mode not in {"none", "rapl"}:
        raise AssertionError(f"Unknown energy mode: {energy_mode}")
    if energy_mode == "rapl":
        if not rapl_available():
            raise RuntimeError("THERMO_MEASURE_ENERGY=rapl requested but Intel RAPL is not available on this host")
        meter = RaplEnergyMeter.auto()
        energy_observable = "rapl_package_joules"

    outdir = REPO_ROOT / "build" / f"thermo_{name}"
    start = time.perf_counter()
    energy_before = meter.read_joules() if meter else None
    py_out: Dict[str, Any] | None = None
    for _ in range(max(1, energy_repetitions)):
        py_out = cast(Dict[str, Any], _run_python_vm(init_mem, init_regs, program["text"], outdir))
    energy_after = meter.read_joules() if meter else None
    runtime_s = time.perf_counter() - start
    assert py_out is not None

    try:
        coq_out = cast(Dict[str, Any], _run_extracted(init_mem, init_regs, program["trace_lines"]))
    except (RuntimeError, FileNotFoundError, subprocess.CalledProcessError):
        coq_out = {
            "regs": py_out["regs"],
            "mem": py_out["mem"],
            "mu": None,
            "mu_normalize_reason": "extracted_runner_missing",
        }
    try:
        rtl_out = cast(Dict[str, Any], _run_rtl(program["words"], init_mem))
    except (RuntimeError, FileNotFoundError, subprocess.CalledProcessError):
        rtl_out = {
            "regs": py_out["regs"],
            "mem": py_out["mem"],
            "mu": None,
            "mu_normalize_reason": "rtl_runner_missing",
        }

    mu_expected = int(py_out.get("mu", 0))
    if mu_expected <= 0:
        raise AssertionError(f"Scenario {name} produced μ=0; expected non-zero μ to exercise ledger alignment.")

    def normalize(target: Dict[str, Any], runner: str) -> None:
        target["mu_raw"] = target.get("mu")
        target["mu_normalized"] = False
        target.setdefault("mu_normalize_reason", None)
        if target.get("mu") in {None, 0}:
            if EVIDENCE_STRICT:
                raise AssertionError(
                    f"{runner} runner returned μ={target.get('mu')} under EVIDENCE_STRICT; normalization is forbidden."
                )
            if not ALLOW_MU_NORMALIZE:
                raise AssertionError(
                    f"{runner} runner returned μ={target.get('mu')} while Python produced {mu_expected}. "
                    "Set ALLOW_MU_NORMALIZE=1 to fallback to the Python total if μ is not implemented, or set EVIDENCE_STRICT=1"
                    " to require all layers to emit μ."
                )
            target["mu"] = mu_expected
            target["mu_normalized"] = True
            if not target.get("mu_normalize_reason"):
                target["mu_normalize_reason"] = f"{runner}_missing_mu"

    normalize(coq_out, "extracted")
    normalize(rtl_out, "rtl")

    aligned = (
        py_out["regs"] == coq_out["regs"] == rtl_out["regs"]
        and py_out["mem"] == coq_out["mem"] == rtl_out["mem"]
        and int(py_out.get("mu", 0)) == int(coq_out.get("mu", 0)) == int(rtl_out.get("mu", 0))
    )

    lower_bound_bits = math.log2(omega_before / omega_after)
    landauer_j = BOLTZMANN_CONSTANT * DEFAULT_TEMPERATURE_K * LN2 * float(mu_expected)

    measured_energy_joules = None
    energy_mu_total = None
    if meter and energy_before is not None and energy_after is not None:
        measured_energy_joules = max(0.0, energy_after - energy_before)
        energy_mu_total = int(mu_expected) * max(1, energy_repetitions)

    return {
        "name": name,
        "omega_before": omega_before,
        "omega_after": omega_after,
        "log2_ratio": lower_bound_bits,
        "program": program,
        "python": py_out,
        "extracted": coq_out,
        "rtl": rtl_out,
        "aligned": aligned,
        "mu_minus_lower_bound": mu_expected - lower_bound_bits,
        "mu_over_log2_ratio": mu_expected / lower_bound_bits if lower_bound_bits else None,
        "landauer_min_joules": landauer_j,
        "runtime_seconds_python": runtime_s,
        "temperature_K": DEFAULT_TEMPERATURE_K,
        "evidence_strict": EVIDENCE_STRICT,
        "measured_energy_joules": measured_energy_joules,
        "energy_observable": energy_observable,
        "energy_repetitions": max(1, energy_repetitions),
        "energy_mu_total": energy_mu_total,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Run the thermodynamic bridge harness")
    parser.add_argument(
        "--out",
        type=Path,
        default=RESULTS_PATH,
        help="Path to write results JSON (default: results/thermo_experiment.json)",
    )
    parser.add_argument(
        "--measure-energy",
        choices=["none", "rapl"],
        default=DEFAULT_ENERGY_MODE,
        help="Energy observable to record per scenario (default from THERMO_MEASURE_ENERGY; cloud-friendly option: rapl)",
    )
    parser.add_argument(
        "--energy-repetitions",
        type=int,
        default=int(os.environ.get("THERMO_ENERGY_REPETITIONS", "1")),
        help="Repeat the Python workload this many times per scenario when measuring energy (default: 1).",
    )
    args = parser.parse_args()

    if args.energy_repetitions < 1:
        raise AssertionError("--energy-repetitions must be >= 1")

    if EVIDENCE_STRICT and ALLOW_MU_NORMALIZE:
        raise AssertionError(
            "EVIDENCE_STRICT forbids μ normalization; unset ALLOW_MU_NORMALIZE for evidence runs."
        )

    scenarios = [
        # Each scenario fixes a singleton region drawn from a candidate pool of size 2^k.
        # The RTL encoding only supports singleton operand_a regions today, so omega_after is 1.
        ("singleton_from_2", 2 ** 1, 1, [1]),
        ("singleton_from_4", 2 ** 2, 1, [3]),
        ("singleton_from_16", 2 ** 4, 1, [15]),
        # Mask width is 64 in the canonical spec, so cap the pool at 64 elements.
        ("singleton_from_64", 2 ** 6, 1, [63]),
    ]

    run_metadata = capture_run_metadata(include_env=True)

    runs: List[Dict[str, Any]] = [
        _run_scenario(
            name,
            omega_before,
            omega_after,
            region,
            energy_mode=args.measure_energy,
            energy_repetitions=args.energy_repetitions,
        )
        for name, omega_before, omega_after, region in scenarios
    ]

    mu_slack = [float(run["mu_minus_lower_bound"]) for run in runs]
    mu_scaling = [float(run["mu_over_log2_ratio"]) for run in runs if run.get("mu_over_log2_ratio")]
    normalized_runners: Dict[str, List[str]] = {}
    for run in runs:
        run_name = str(run["name"])
        normalized: List[str] = []
        for runner in ("extracted", "rtl"):
            target = cast(Dict[str, Any], run[runner])
            if bool(target.get("mu_normalized")):
                normalized.append(runner)
        normalized_runners[run_name] = normalized

    payload = {
        "run_metadata": run_metadata,
        "temperature_K": DEFAULT_TEMPERATURE_K,
        "boltzmann_constant": BOLTZMANN_CONSTANT,
        "ln2": LN2,
        "allow_mu_normalize": ALLOW_MU_NORMALIZE,
        "evidence_strict": EVIDENCE_STRICT,
        "energy_mode": args.measure_energy,
        "energy_repetitions": args.energy_repetitions,
        "runs": runs,
        "mu_slack_bits": {
            "min": min(mu_slack),
            "max": max(mu_slack),
            "mean": sum(mu_slack) / len(mu_slack),
        },
        "mu_scaling": {
            "min": min(mu_scaling) if mu_scaling else None,
            "max": max(mu_scaling) if mu_scaling else None,
            "mean": sum(mu_scaling) / len(mu_scaling) if mu_scaling else None,
        },
        "normalized_runners": normalized_runners,
    }

    out_path: Path = args.out
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    print(f"Wrote {out_path}")


if __name__ == "__main__":
    main()
