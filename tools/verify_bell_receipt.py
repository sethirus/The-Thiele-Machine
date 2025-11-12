#!/usr/bin/env python3
"""Verify a Bell receipt pack and re-run the Coq harness."""

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

from make_bell_receipt import (
    ModeTotals,
    SIGNING_KEY,
    compute_entry_hash,
    mdl_for_correlators,
    verify_chain,
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


def totals_from_entries(entries: List[Mapping[str, object]]) -> tuple[ModeTotals, ModeTotals]:
    bell_totals = ModeTotals.fresh()
    classical_totals = ModeTotals.fresh()
    for entry in entries:
        settings = entry.get("settings", {})
        key = f"{settings.get('a')}{settings.get('b')}"
        ensure(key in bell_totals.settings, f"unknown setting key {key}")
        outcomes = entry.get("outcomes", {})
        for mode, totals in (("bell", bell_totals), ("lhv", classical_totals)):
            product = outcomes.get(mode, {}).get("product")
            ensure(product in (-1, 1), f"invalid product {product} for {mode}")
            totals.record(key, int(product))
    return bell_totals, classical_totals


def fraction_from(summary_field: Mapping[str, int]) -> Fraction:
    return Fraction(summary_field["numerator"], summary_field["denominator"])


def verify_summary(
    receipt_path: Path,
    entries: List[Mapping[str, object]],
    summary: Mapping[str, object],
) -> tuple[Fraction, Fraction, Fraction, Fraction, Fraction, Path, Sequence[str]]:
    ensure(summary.get("event") == "bell_summary", "final entry is not a bell summary")
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
    script_path = Path(generator.get("script", ""))
    ensure(script_path.as_posix() == "tools/make_bell_receipt.py", "unexpected generator script")
    generator_sha = generator.get("sha256")
    ensure(generator_sha, "missing generator sha256")
    ensure(
        hashlib.sha256(Path("tools/make_bell_receipt.py").read_bytes()).hexdigest()
        == generator_sha,
        "generator sha256 mismatch",
    )
    parameters = generator.get("parameters", {})
    ensure(parameters, "missing generator parameters")
    epsilon_params = parameters.get("epsilon_fraction", {})
    ensure(
        {"numerator", "denominator"} <= epsilon_params.keys(),
        "epsilon fraction parameters missing",
    )
    epsilon_fraction = Fraction(epsilon_params["numerator"], epsilon_params["denominator"])
    num_trials = int(parameters.get("N", 0))
    ensure(num_trials > 0, "invalid number of trials in generator parameters")
    ensure("seed" in parameters, "missing seed parameter")
    ensure(
        math.isclose(parameters.get("epsilon_float", 0.0), float(epsilon_fraction), rel_tol=1e-12, abs_tol=1e-12),
        "epsilon_float mismatch",
    )

    chain_validation = summary.get("chain_validation", {})
    ensure(
        chain_validation.get("entries") == len(entries),
        "chain_validation entries mismatch",
    )
    ensure(chain_validation.get("self_check") is True, "chain self_check flag not set")

    trial_entries = entries[:-1]
    ensure(len(trial_entries) == num_trials, "trial count mismatch with generator parameters")

    bell_totals, classical_totals = totals_from_entries(trial_entries)

    counts = summary.get("counts", {})
    ensure(counts.get("total_trials") == num_trials, "total_trials mismatch")
    for label, totals in (("bell", bell_totals), ("lhv", classical_totals)):
        recorded = counts.get(label, {})
        for setting, stats in totals.settings.items():
            entry_counts = recorded.get(setting, {})
            ensure(entry_counts.get("trials") == stats.trials, f"{label} trials mismatch for {setting}")
            ensure(entry_counts.get("sum_xy") == stats.sum_xy, f"{label} sum mismatch for {setting}")

    bell_corr = bell_totals.correlators()
    classical_corr = classical_totals.correlators()
    correlators = summary.get("E", {})
    for label, observed in (("bell", bell_corr), ("lhv", classical_corr)):
        summary_corr = correlators.get(label, {})
        for setting, value in observed.items():
            ensure(
                math.isclose(summary_corr.get(setting, 0.0), float(value), rel_tol=1e-9, abs_tol=1e-9),
                f"{label} correlator mismatch for {setting}",
            )

    s_bell = bell_corr["00"] + bell_corr["01"] + bell_corr["10"] - bell_corr["11"]
    s_classical = (
        classical_corr["00"]
        + classical_corr["01"]
        + classical_corr["10"]
        - classical_corr["11"]
    )
    epsilon_float = summary.get("epsilon")
    ensure(
        math.isclose(float(epsilon_fraction), float(epsilon_float), rel_tol=1e-12, abs_tol=1e-12),
        "epsilon mismatch",
    )

    violation_margin = s_bell - Fraction(2, 1) - epsilon_fraction
    classical_gap = Fraction(2, 1) + epsilon_fraction - s_classical
    summary_violation = fraction_from(summary["violation_margin"])
    summary_gap = fraction_from(summary["classical_gap"])
    ensure(summary_violation == violation_margin, "violation margin mismatch")
    ensure(summary_gap == classical_gap, "classical gap mismatch")

    s_summary = summary.get("S", {})
    ensure(
        math.isclose(s_summary.get("bell", 0.0), float(s_bell), rel_tol=1e-9, abs_tol=1e-9),
        "S_bell mismatch",
    )
    ensure(
        math.isclose(s_summary.get("lhv", 0.0), float(s_classical), rel_tol=1e-9, abs_tol=1e-9),
        "S_lhv mismatch",
    )

    sigma = math.sqrt(bell_totals.sigma_terms())
    ensure(
        math.isclose(s_summary.get("sigma", 0.0), sigma, rel_tol=1e-9, abs_tol=1e-9),
        "sigma mismatch",
    )
    margin_sigma = float(violation_margin) / sigma if sigma > 0 else float("inf")
    ensure(
        math.isclose(s_summary.get("margin_sigma", 0.0), margin_sigma, rel_tol=1e-7, abs_tol=1e-7),
        "sigma margin mismatch",
    )

    mdl_section = summary.get("mdl_bits", {})
    mdl_bell = mdl_for_correlators(bell_totals)
    mdl_classical = mdl_for_correlators(classical_totals)
    ensure(
        math.isclose(mdl_section.get("delta_vs_classical", 0.0), mdl_classical["total"] - mdl_bell["total"], rel_tol=1e-9, abs_tol=1e-6),
        "MDL delta mismatch",
    )
    for label, expected in (("bell", mdl_bell), ("lhv", mdl_classical)):
        recorded = mdl_section.get(label, {})
        for key in ("model", "residual", "total"):
            ensure(
                math.isclose(recorded.get(key, 0.0), expected[key], rel_tol=1e-9, abs_tol=1e-6),
                f"MDL mismatch for {label}.{key}",
            )

    harness_info = summary.get("coq_check", {})
    ensure(harness_info, "missing Coq harness metadata")
    harness_path_str = harness_info.get("harness_path")
    ensure(harness_path_str, "missing harness path")
    harness_path = Path(harness_path_str)
    if not harness_path.is_absolute():
        harness_path = receipt_path.parent / harness_path
    ensure(harness_path.exists(), f"Coq harness missing at {harness_path}")
    harness_bytes = harness_path.read_bytes()
    ensure(len(harness_bytes) == harness_info.get("artifact_bytes"), "harness byte count mismatch")
    ensure(
        hashlib.sha256(harness_bytes).hexdigest() == harness_info.get("artifact_hash"),
        "harness sha256 mismatch",
    )
    ensure(harness_info.get("passed") is True, "Coq check flag not set")
    coq_args = harness_info.get("coq_args")
    ensure(isinstance(coq_args, list) and all(isinstance(arg, str) for arg in coq_args), "missing Coq arguments")

    return (
        s_bell,
        s_classical,
        epsilon_fraction,
        violation_margin,
        classical_gap,
        harness_path,
        list(coq_args),
    )


def run_coq(harness_path: Path, coqtop: str, coq_args: Sequence[str]) -> None:
    result = subprocess.run(
        [coqtop, *coq_args, "-batch", "-l", str(harness_path)],
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    if result.returncode != 0:
        sys.stderr.write(result.stdout)
        sys.stderr.write(result.stderr)
        raise RuntimeError("Coq harness execution failed")


def parse_args(argv: Iterable[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("receipt", type=Path, help="path to the bell receipt jsonl")
    parser.add_argument("--coqtop", default="coqtop", help="coqtop binary to invoke")
    parser.add_argument(
        "--skip-coq",
        action="store_true",
        help="skip running the Coq harness (useful when the binary is unavailable)",
    )
    return parser.parse_args(argv)


def main(argv: Iterable[str] | None = None) -> None:
    args = parse_args(argv)
    receipt_path = args.receipt
    entries = load_entries(receipt_path)
    summary = entries[-1]
    try:
        (
            s_bell,
            s_classical,
            epsilon_fraction,
            violation_margin,
            classical_gap,
            harness_path,
            coq_args,
        ) = verify_summary(receipt_path, entries, summary)
        if args.skip_coq:
            print("Skipping Coq harness execution (--skip-coq).")
        else:
            run_coq(harness_path, args.coqtop, coq_args)
    except FileNotFoundError as exc:
        raise SystemExit(
            f"verification failed: could not execute '{args.coqtop}': {exc}. "
            "Install Coq or re-run with --skip-coq."
        )
    except Exception as exc:  # pragma: no cover - explicit failure path
        raise SystemExit(f"verification failed: {exc}")

    bell_totals, _ = totals_from_entries(entries[:-1])
    sigma = math.sqrt(bell_totals.sigma_terms())
    margin_sigma = float(violation_margin) / sigma if sigma > 0 else float("inf")

    print(f"S_bell = {float(s_bell):.6f}")
    print(f"S_lhv = {float(s_classical):.6f}")
    print(f"epsilon = {float(epsilon_fraction):.6f}")
    print(f"violation margin = {float(violation_margin):.6f}")
    print(f"classical gap = {float(classical_gap):.6f}")
    print(f"sigma = {sigma:.6f} -> margin {margin_sigma:.2f}σ")
    print("\033[32mALL VERIFIED\033[0m")


if __name__ == "__main__":
    main()
