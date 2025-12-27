#!/usr/bin/env python3
"""Compare sighted and blind turbulence solvers and emit a head-to-head receipt."""

from __future__ import annotations

import argparse
import hashlib
import hmac
import json
import math
import statistics
from pathlib import Path
from typing import Iterable, List, MutableMapping

try:
    from tools.make_law_receipt import append_entry, compute_entry_hash, nusd_payload, verify_chain
except ModuleNotFoundError:  # pragma: no cover - executed inside tools/
    from make_law_receipt import append_entry, compute_entry_hash, nusd_payload, verify_chain  # type: ignore

try:
    from tools.nusd_domains import ar1_fit, simulate_turbulence_series
except ModuleNotFoundError:  # pragma: no cover - executed inside tools/
    from nusd_domains import ar1_fit, simulate_turbulence_series  # type: ignore

try:
    from tools.mu_calibration import CalibrationSummary, compute_calibration_summary
except ModuleNotFoundError:  # pragma: no cover
    from mu_calibration import (  # type: ignore
        CalibrationSummary,
        compute_calibration_summary,
    )

DEFAULT_OUTPUT = Path("artifacts/turbulence_head_to_head.jsonl")
DEFAULT_CALIBRATION = Path("mu_bit_correlation_data.json")
DEFAULT_TEMPERATURE = 300.0
SIGNING_KEY = b"ThieleHeadToHeadKey"
DEFAULT_EPSILON_FACTOR = 0.01
DEFAULT_BLIND_BITS_PER_SAMPLE = 16.0


def parse_args(argv: Iterable[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT, help="receipt output path")
    parser.add_argument("--seed", type=int, default=314159, help="dataset seed")
    parser.add_argument("--samples", type=int, default=96, help="number of samples to synthesise")
    parser.add_argument("--grid", type=int, default=32, help="grid resolution metadata for the dataset")
    parser.add_argument("--temperature", type=float, default=DEFAULT_TEMPERATURE, help="calibration temperature in kelvin")
    parser.add_argument(
        "--epsilon-bits",
        type=float,
        default=None,
        help="override the NUSD slack epsilon in bits (default derives from sample count)",
    )
    parser.add_argument(
        "--blind-bits-per-sample",
        type=float,
        default=DEFAULT_BLIND_BITS_PER_SAMPLE,
        help="encoding budget in bits per observation for the blind solver",
    )
    parser.add_argument(
        "--calibration-file",
        type=Path,
        default=DEFAULT_CALIBRATION,
        help="μ-bit calibration dataset (used when present)",
    )
    parser.add_argument("--no-calibration", action="store_true", help="skip calibration metadata in the summary")
    return parser.parse_args(argv)


def ensure_inputs(args: argparse.Namespace) -> None:
    if args.samples < 4:
        raise ValueError("samples must be at least four")
    if args.grid <= 0:
        raise ValueError("grid must be positive")
    if args.blind_bits_per_sample <= 0:
        raise ValueError("blind bits per sample must be positive")


def baseline_metrics(energies: List[float]) -> tuple[float, float, List[float]]:
    if len(energies) < 2:
        raise ValueError("need at least two energies to compute baseline residuals")
    mean_future = statistics.mean(energies[1:])
    baseline_residuals = [actual - mean_future for actual in energies[1:]]
    baseline_energy = sum(value * value for value in baseline_residuals)
    baseline_bits = math.log2(1.0 + baseline_energy)
    return baseline_bits, baseline_energy, baseline_residuals


def sighted_metrics(energies: List[float], baseline_bits: float) -> tuple[dict[str, float], dict[str, float]]:
    slope, intercept = ar1_fit(energies)
    predictions = [slope * value + intercept for value in energies[:-1]]
    residuals = [actual - predicted for actual, predicted in zip(energies[1:], predictions)]
    residual_energy = sum(value * value for value in residuals)
    residual_bits = math.log2(1.0 + residual_energy)
    model_bits = math.log2(1.0 + abs(slope)) + math.log2(1.0 + abs(intercept))
    total_bits = model_bits + residual_bits
    mdl = {
        "model_bits": model_bits,
        "residual_bits": residual_bits,
        "baseline_bits": baseline_bits,
        "total_bits": total_bits,
        "delta_vs_baseline": baseline_bits - total_bits,
    }
    detail = {
        "slope": slope,
        "intercept": intercept,
        "residual_energy": residual_energy,
        "residual_ratio": residual_energy / (math.pow(2.0, baseline_bits) - 1.0) if baseline_bits else 0.0,
    }
    return mdl, detail


def blind_metrics(
    energies: List[float],
    baseline_bits: float,
    bits_per_sample: float,
) -> tuple[dict[str, float], dict[str, float]]:
    samples = len(energies)
    model_bits = samples * bits_per_sample + math.log2(1.0 + bits_per_sample)
    residual_bits = baseline_bits
    total_bits = model_bits + residual_bits
    mdl = {
        "model_bits": model_bits,
        "residual_bits": residual_bits,
        "baseline_bits": baseline_bits,
        "total_bits": total_bits,
        "delta_vs_baseline": baseline_bits - total_bits,
    }
    detail = {
        "bits_per_sample": bits_per_sample,
        "samples": samples,
        "encoded_series_bits": samples * bits_per_sample,
    }
    return mdl, detail


def load_calibration(path: Path, skip: bool) -> tuple[CalibrationSummary | None, Path | None]:
    if skip:
        return None, None
    if not path.exists():
        raise FileNotFoundError(f"calibration dataset {path} is missing")
    return compute_calibration_summary(path), path


def dataset_digest(energies: List[float]) -> str:
    payload = json.dumps(energies, separators=(",", ":"), ensure_ascii=False)
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


def append_dataset_entries(
    entries: List[MutableMapping[str, object]],
    seed: int,
    samples: int,
    grid: int,
    energies: List[float],
    gradients: List[float],
) -> None:
    previous_hash = "0" * 64 if not entries else entries[-1]["crypto_hash"]
    digest_entry: MutableMapping[str, object] = {
        "event": "dataset_digest",
        "seed": seed,
        "samples": samples,
        "grid": grid,
        "series_sha256": dataset_digest(energies),
    }
    previous_hash = append_entry(entries, digest_entry, previous_hash)
    for index, energy in enumerate(energies[: min(16, len(energies))]):
        sample_entry: MutableMapping[str, object] = {
            "event": "dataset_sample",
            "index": index,
            "energy": energy,
            "gradient": gradients[index - 1] if index > 0 else 0.0,
        }
        previous_hash = append_entry(entries, sample_entry, previous_hash)


def append_solver_entry(
    entries: List[MutableMapping[str, object]],
    solver: str,
    mdl: dict[str, float],
    detail: dict[str, float],
) -> None:
    previous_hash = "0" * 64 if not entries else entries[-1]["crypto_hash"]
    entry: MutableMapping[str, object] = {
        "event": "solver_result",
        "solver": solver,
        "mdl_bits": mdl,
        "detail": detail,
    }
    append_entry(entries, entry, previous_hash)


def main(argv: Iterable[str] | None = None) -> None:
    args = parse_args(argv)
    ensure_inputs(args)
    energies, gradients = simulate_turbulence_series(args.seed, args.samples)
    baseline_bits, baseline_energy, _ = baseline_metrics(energies)
    epsilon_bits = args.epsilon_bits if args.epsilon_bits is not None else math.log2(args.samples) * DEFAULT_EPSILON_FACTOR

    sighted_mdl, sighted_detail = sighted_metrics(energies, baseline_bits)
    blind_mdl, blind_detail = blind_metrics(energies, baseline_bits, args.blind_bits_per_sample)

    calibration_summary, calibration_path = load_calibration(args.calibration_file, args.no_calibration)

    entries: List[MutableMapping[str, object]] = []
    append_dataset_entries(entries, args.seed, args.samples, args.grid, energies, gradients)
    append_solver_entry(entries, "sighted", sighted_mdl, sighted_detail)
    append_solver_entry(entries, "blind", blind_mdl, blind_detail)

    sighted_nusd = nusd_payload(sighted_mdl, args.temperature, epsilon_bits, calibration_summary)
    blind_nusd = nusd_payload(blind_mdl, args.temperature, epsilon_bits, calibration_summary)

    generator_sha = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()

    summary: MutableMapping[str, object] = {
        "event": "turbulence_head_to_head_summary",
        "generator": {
            "script": "tools/make_turbulence_head_to_head.py",
            "sha256": generator_sha,
            "parameters": {
                "seed": args.seed,
                "samples": args.samples,
                "grid": args.grid,
                "temperature": args.temperature,
                "epsilon_bits": epsilon_bits,
                "blind_bits_per_sample": args.blind_bits_per_sample,
            },
        },
        "dataset": {
            "series_sha256": dataset_digest(energies),
            "samples": args.samples,
            "grid": args.grid,
            "seed": args.seed,
            "energy_mean": statistics.mean(energies),
            "energy_variance": statistics.pvariance(energies),
            "baseline_energy": baseline_energy,
            "baseline_bits": baseline_bits,
        },
        "solvers": {
            "sighted": {
                "mdl_bits": sighted_mdl,
                "nusd_bound": sighted_nusd,
                "detail": sighted_detail,
            },
            "blind": {
                "mdl_bits": blind_mdl,
                "nusd_bound": blind_nusd,
                "detail": blind_detail,
            },
        },
        "temperature_kelvin": args.temperature,
        "epsilon_bits": epsilon_bits,
        "calibration_dataset": str(calibration_path) if calibration_path else None,
        "mu_gap_bits": blind_nusd["mu_total_bits"] - sighted_nusd["mu_total_bits"],
        "chain_validation": {"entries": len(entries) + 1, "self_check": True},
    }

    previous_hash = entries[-1]["crypto_hash"] if entries else "0" * 64
    append_entry(entries, summary, previous_hash)

    summary_entry = entries[-1]
    summary_entry["signature_algorithm"] = "HMAC-SHA256"
    summary_entry["crypto_hash"] = compute_entry_hash(summary_entry)
    summary_entry["signature"] = hmac.new(
        SIGNING_KEY, summary_entry["crypto_hash"].encode("utf-8"), hashlib.sha256
    ).hexdigest()

    if not verify_chain(entries):
        raise RuntimeError("hash chain verification failed before writing receipt")

    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w", encoding="utf-8") as handle:
        for entry in entries:
            handle.write(json.dumps(entry, sort_keys=True))
            handle.write("\n")

    print(f"Turbulence head-to-head receipt written to {args.output}")


if __name__ == "__main__":
    main()
