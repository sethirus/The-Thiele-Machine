#!/usr/bin/env python3
"""Verify a multi-domain No Unpaid Sight Debt receipt."""

from __future__ import annotations

import argparse
import hashlib
import hmac
import json
import math
from pathlib import Path
from typing import Iterable, List, Mapping

try:
    from tools.make_law_receipt import compute_entry_hash, nusd_payload, verify_chain
except ModuleNotFoundError:  # script executed from within tools/
    from make_law_receipt import compute_entry_hash, nusd_payload, verify_chain
from mu_calibration import CalibrationSummary, compute_calibration_summary
from nusd_domains import DOMAIN_REGISTRY, DiscoveryDomain

SIGNING_KEY = b"ThieleNUSDKey"


def parse_args(argv: Iterable[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("receipt", type=Path, help="path to the receipt JSONL")
    parser.add_argument(
        "--calibration-file",
        type=Path,
        default=None,
        help="override the calibration dataset referenced in the receipt",
    )
    parser.add_argument(
        "--skip-calibration",
        action="store_true",
        help="do not recompute calibration-derived quantities",
    )
    return parser.parse_args(argv)


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


def calibration_from(
    summary_dataset: str | None,
    override: Path | None,
    skip: bool,
) -> CalibrationSummary | None:
    if skip:
        return None
    candidate: Path | None = None
    if override is not None:
        candidate = override
    elif summary_dataset:
        candidate = Path(summary_dataset)
    if candidate is None:
        return None
    if not candidate.exists():
        raise FileNotFoundError(f"calibration dataset {candidate} is missing")
    return compute_calibration_summary(candidate)


def compare_mdl(expected: Mapping[str, float], recorded: Mapping[str, object]) -> None:
    for key, value in expected.items():
        ensure(key in recorded, f"missing mdl field {key}")
        ensure(
            math.isclose(float(recorded.get(key, 0.0)), float(value), rel_tol=1e-6, abs_tol=1e-6),
            f"mdl mismatch for {key}",
        )


def compare_nusd(
    mdl: Mapping[str, float],
    summary: Mapping[str, object],
    temperature: float,
    epsilon_bits: float,
    calibration: CalibrationSummary | None,
) -> None:
    recomputed = nusd_payload(mdl, temperature, epsilon_bits, calibration)
    for key, value in recomputed.items():
        recorded = summary.get(key)
        if isinstance(value, (int, float)):
            ensure(recorded is not None, f"missing nusd field {key}")
            ensure(
                math.isclose(float(recorded), float(value), rel_tol=1e-6, abs_tol=1e-6),
                f"nusd mismatch for {key}",
            )
        else:
            ensure(recorded == value, f"nusd mismatch for {key}")


def main(argv: Iterable[str] | None = None) -> None:
    args = parse_args(argv)
    entries = load_entries(args.receipt)
    summary = entries[-1]
    ensure(summary.get("event") == "nusd_summary", "final entry is not a nusd summary")
    ensure(verify_chain(entries), "hash chain verification failed")
    ensure(
        compute_entry_hash(summary) == summary.get("crypto_hash"),
        "summary crypto hash mismatch",
    )
    expected_signature = hmac.new(
        SIGNING_KEY, summary["crypto_hash"].encode("utf-8"), hashlib.sha256
    ).hexdigest()
    ensure(summary.get("signature") == expected_signature, "invalid HMAC signature")

    generator = summary.get("generator", {})
    ensure(generator.get("script") == "tools/make_nusd_receipt.py", "unexpected generator script")
    generator_sha = generator.get("sha256")
    ensure(generator_sha, "missing generator sha256")
    ensure(
        hashlib.sha256(Path("tools/make_nusd_receipt.py").read_bytes()).hexdigest()
        == generator_sha,
        "generator sha mismatch",
    )

    parameters = generator.get("parameters", {})
    ensure(parameters, "missing generator parameters")
    domain_block = summary.get("domain", {})
    domain_name = domain_block.get("name")
    ensure(domain_name in DOMAIN_REGISTRY, "unrecognised domain name")

    domain_cls = DOMAIN_REGISTRY[domain_name]
    domain: DiscoveryDomain = domain_cls.from_parameters(parameters, record_entries=False)
    replay = domain.run()

    recorded_mdl = summary.get("mdl_bits", {})
    compare_mdl(replay.mdl, recorded_mdl)

    domain_detail = domain_block.get("detail", {})
    recomputed_detail = replay.detail
    domain_cls.compare_detail(domain_detail, recomputed_detail)

    epsilon_bits = float(summary.get("epsilon_bits", 0.0))
    temperature = float(summary.get("temperature_kelvin", 0.0))
    calibration_dataset = summary.get("calibration_dataset")
    calibration_summary = calibration_from(calibration_dataset, args.calibration_file, args.skip_calibration)
    compare_nusd(replay.mdl, summary.get("nusd_bound", {}), temperature, epsilon_bits, calibration_summary)

    chain_validation = summary.get("chain_validation", {})
    ensure(chain_validation.get("self_check") is True, "chain self_check flag missing")
    ensure(chain_validation.get("entries") == len(entries), "chain length mismatch")

    print("Receipt verification succeeded")


if __name__ == "__main__":  # pragma: no cover - defensive guard
    main()
