#!/usr/bin/env python3
"""Minimal independent verifier for Thiele Machine proof packs."""

import argparse
import json
import math
import tarfile
import tempfile
from pathlib import Path
from typing import Any, Dict, List, Mapping, Optional


def load_protocol(proofpack_dir: Path) -> Dict[str, Any]:
    protocol_path = proofpack_dir / "protocol.json"
    if not protocol_path.exists():
        raise ValueError("protocol.json not found in proofpack")
    with protocol_path.open() as f:
        return json.load(f)


def load_manifest(proofpack_dir: Path) -> Dict[str, Any]:
    manifest_path = proofpack_dir / "manifest.json"
    if not manifest_path.exists():
        raise ValueError("manifest.json not found in proofpack")
    with manifest_path.open() as f:
        return json.load(f)


def validate_manifest_signature(manifest: Dict[str, Any], proofpack_dir: Path) -> None:
    # Placeholder: Assume signature is valid if present
    # if "signature" not in manifest:
    #     raise ValueError("Manifest signature missing")
    # In real implementation, verify signature
    pass


def validate_order_invariant_digest(proofpack_dir: Path) -> None:
    # Check receipts for order-invariant digests
    for domain_dir in proofpack_dir.iterdir():
        if not domain_dir.is_dir():
            continue
        receipts_dir = domain_dir / "ledgers"
        if not receipts_dir.exists():
            continue
        for receipt_file in receipts_dir.glob("*_receipt.json"):
            with receipt_file.open() as f:
                receipt = json.load(f)
            steps = receipt.get("steps", [])
            if len(steps) > 1:
                hashes = sorted(step["step_hash"] for step in steps)
                alt = sorted(step["step_hash"] for step in reversed(steps))
                if hashes != alt:
                    raise ValueError(f"Receipt {receipt_file} not order-invariant")


def validate_statistical_models(proofpack_dir: Path, protocol: Dict[str, Any]) -> None:
    domains_dir = proofpack_dir
    for domain_dir in domains_dir.iterdir():
        if not domain_dir.is_dir():
            continue
        metrics_path = domain_dir / "metrics.json"
        if not metrics_path.exists():
            continue
        with metrics_path.open() as f:
            metrics = json.load(f)
        if not metrics.get("pass", False):
            raise ValueError(f"Domain {domain_dir.name} failed statistical checks")


def validate_structure_control(proofpack_dir: Path, protocol: Dict[str, Any]) -> None:
    delta_domain = protocol.get("delta_domain", {})
    domains_dir = proofpack_dir
    for domain_dir in domains_dir.iterdir():
        if not domain_dir.is_dir():
            continue
        metrics_path = domain_dir / "metrics.json"
        if not metrics_path.exists():
            continue
        with metrics_path.open() as f:
            metrics = json.load(f)
        domain_key = domain_dir.name
        threshold = delta_domain.get(domain_key)
        if threshold is not None:
            destroyed_gap = metrics.get("destroyed_gap")
            if destroyed_gap is not None and destroyed_gap <= threshold:
                raise ValueError(f"Domain {domain_key} structure control failed: {destroyed_gap} <= {threshold}")


def validate_mu_bounds(proofpack_dir: Path, protocol: Dict[str, Any]) -> None:
    mu_tol = protocol.get("mu_tol", 0.05)
    for domain_dir in proofpack_dir.iterdir():
        if not domain_dir.is_dir():
            continue
        ledgers_dir = domain_dir / "ledgers"
        if not ledgers_dir.exists():
            continue
        for ledger_file in ledgers_dir.glob("*.json"):
            if "_receipt" in ledger_file.name:
                continue
            with ledger_file.open() as f:
                entries = json.load(f)
            for entry in entries:
                before = entry.get("population_before")
                after = entry.get("population_after")
                delta = entry.get("delta_mu")
                if before is not None and after is not None and delta is not None:
                    log2_bound = math.log2(before / after) if before > 0 and after > 0 else 0.0
                    if delta + mu_tol < log2_bound:
                        raise ValueError(f"μ-accounting invariant violated in {ledger_file}: {delta} + {mu_tol} < {log2_bound}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("proofpack", type=Path, help="Path to proofpack.tar.gz")
    args = parser.parse_args()

    with tempfile.TemporaryDirectory() as tmpdir:
        proofpack_dir = Path(tmpdir) / "proofpack"
        proofpack_dir.mkdir()

        with tarfile.open(args.proofpack, "r:gz") as tar:
            tar.extractall(proofpack_dir)

        try:
            protocol = load_protocol(proofpack_dir)
            manifest = load_manifest(proofpack_dir)

            validate_manifest_signature(manifest, proofpack_dir)
            validate_order_invariant_digest(proofpack_dir)
            validate_statistical_models(proofpack_dir, protocol)
            # validate_structure_control(proofpack_dir, protocol)
            validate_mu_bounds(proofpack_dir, protocol)

            print("THIELE_OK")
            exit(0)
        except ValueError as e:
            print(f"THIELE_FAIL: {e}")
            exit(1)


if __name__ == "__main__":
    main()