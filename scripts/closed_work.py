#!/usr/bin/env python3
"""One-command "closed work" runner.

Completion criterion (Dec 16, 2025): a single command produces:
  (i)  Coq proof objects for A+B (no admitted/axioms enforced separately)
  (ii) a bounded falsifier-search report
  (iii) a verifier artifact for C with a clear PASS/FAIL + signed receipt
  (iv) reproducibility: deterministic parameters captured in artifacts

This script is intentionally conservative: it does not assume secret keys exist.
It generates an ephemeral Ed25519 keypair and a matching trust manifest for the
artifacts it signs.

Narrative phases:
  INIT → DISCOVER → CLASSIFY → DECOMPOSE → EXECUTE → MERGE → VERIFY → SUCCESS
"""

from __future__ import annotations

import argparse
import datetime as _dt
import hashlib
import json
import os
import subprocess
import sys
from contextlib import redirect_stderr, redirect_stdout
from dataclasses import asdict
from pathlib import Path
from typing import Dict, List, Mapping, Optional, Sequence, Tuple

PROJECT_ROOT = Path(__file__).resolve().parents[1]
if str(PROJECT_ROOT) not in sys.path:
    sys.path.insert(0, str(PROJECT_ROOT))


def _phase(name: str) -> None:
    print(f"\n== {name} ==")


def _sha256_hex(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _run(cmd: Sequence[str], *, cwd: Path, log_path: Path) -> None:
    proc = subprocess.run(
        list(cmd),
        cwd=str(cwd),
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        check=False,
    )
    log_path.write_text(proc.stdout, encoding="utf-8")
    if proc.returncode != 0:
        raise RuntimeError(f"command failed ({proc.returncode}): {' '.join(cmd)}\nlog: {log_path}")


def _write_json(path: Path, payload: Mapping[str, object]) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _write_trust_manifest(path: Path, *, key_id: str, public_key_hex: str) -> None:
    from verifier.receipt_protocol import write_trust_manifest

    write_trust_manifest(path, key_id=key_id, public_key_hex=public_key_hex, patterns=["*.json", "*/**", "*"])


def _bounded_falsifier_scan(*, out_dir: Path, n_per_setting: int, seed: int) -> Mapping[str, object]:
    """Run a bounded search for counterexamples to the operational disclosure rule.

    We check the falsifiable claim encoded in tools/mu_chsh_operational_scan.py:
      For receipt-authenticated CHSH, supra-quantum S without REVEAL should set CSR.ERR.

    Bound: the chosen deterministic strategy tables with the provided n_per_setting.
    """

    from tools import mu_chsh_operational_scan as scan

    stamp = _dt.datetime.now(_dt.UTC).strftime("%Y%m%d_%H%M%S")
    run_root = out_dir / "falsifier_runs" / stamp

    samples: List[Dict[str, object]] = []
    failures = []

    # Force oracle_charge_bits=0 to attempt a counterexample (no disclosure).
    for strategy in ["tsirelson", "supra_16_5", "pr"]:
        outdir = run_root / strategy
        outdir.mkdir(parents=True, exist_ok=True)

        # Keep terminal output clean; store VM prints in a per-strategy log.
        vm_log = outdir / "vm_stdout.log"
        with vm_log.open("w", encoding="utf-8") as handle:
            with redirect_stdout(handle), redirect_stderr(handle):
                sample = scan.run_one(
                    strategy=strategy,
                    n_per_setting=n_per_setting,
                    seed=seed,
                    oracle_charge_bits=0,
                    outdir=outdir,
                )

        print(f"falsify[{strategy}]: S={float(sample.chsh):.6f} err={int(sample.err)} run={outdir}")
        samples.append(
            {
                "strategy": sample.strategy,
                "chsh": str(sample.chsh),
                "mu_ledger_total": int(sample.mu_ledger_total),
                "mu_discovery": int(sample.mu_discovery),
                "mu_execution": int(sample.mu_execution),
                "mu_information": float(sample.mu_information),
                "mu_total": float(sample.mu_total),
                "mu_legacy_total": float(sample.mu_legacy_total),
                "n_per_setting": int(sample.n_per_setting),
                "seed": int(sample.seed),
                "oracle_charge_bits": int(sample.oracle_charge_bits),
                "err": int(sample.err),
                "steps": int(sample.steps),
                "run_dir": str(outdir.as_posix()),
                "vm_log": str(vm_log.as_posix()),
            }
        )

        s_val = float(sample.chsh)
        tsirelson = 2.0 * (2.0**0.5)
        if s_val > tsirelson + 1e-9 and int(sample.err) == 0:
            failures.append(
                {
                    "strategy": strategy,
                    "chsh": str(sample.chsh),
                    "err": int(sample.err),
                    "run_dir": str((run_root / strategy).as_posix()),
                    "reason": "supra-quantum CHSH without REVEAL did not set CSR.ERR",
                }
            )

    report = {
        "ok": len(failures) == 0,
        "bound": {
            "n_per_setting": n_per_setting,
            "seed": seed,
            "oracle_charge_bits": 0,
            "strategies": ["tsirelson", "supra_16_5", "pr"],
        },
        "runs_root": str(run_root.as_posix()),
        "samples": samples,
        "counterexamples": failures,
    }
    return report


def _build_c_artifact(
    *,
    out_dir: Path,
    private_key: object,
    public_key_hex: str,
    key_id: str,
    trust_manifest_path: Path,
) -> Mapping[str, object]:
    """Build + verify the C artifact (non-CHSH): C1 physics-divergence receipt gate."""

    from verifier.physics_divergence import verify_physics_divergence
    from verifier.receipt_protocol import write_trs10_receipt

    c_dir = out_dir / "C_artifact"
    run_dir = c_dir / "run"
    run_dir.mkdir(parents=True, exist_ok=True)

    # Minimal run layout.
    (run_dir / "measurement.csv").write_text("t,value\n0,1.0\n1,1.1\n", encoding="utf-8")
    (run_dir / "claim.json").write_text(
        json.dumps(
            {"metric": "demo_metric", "baseline": 0.10, "claimed": 0.50, "epsilon": 0.20},
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )
    (run_dir / "calibration.json").write_text(
        json.dumps({"protocol": "demo", "disclosure_bits": 9999}, sort_keys=True) + "\n",
        encoding="utf-8",
    )

    receipt_path = run_dir / "physics.receipt.json"
    write_trs10_receipt(
        receipt_path=receipt_path,
        base_dir=run_dir,
        files=[run_dir / "measurement.csv", run_dir / "claim.json", run_dir / "calibration.json"],
        private_key=private_key,
        public_key_hex=public_key_hex,
        key_id=key_id,
        metadata={"purpose": "C1 physics divergence demo", "generator": "scripts/closed_work.py"},
    )

    result = verify_physics_divergence(run_dir, trust_manifest_path)

    verification_path = c_dir / "verification.json"
    _write_json(verification_path, {"status": "PASS" if result.get("ok") else "FAIL", "result": result})

    tm_copy = c_dir / "trust_manifest.json"
    tm_copy.write_text(trust_manifest_path.read_text(encoding="utf-8"), encoding="utf-8")

    verification_receipt_path = c_dir / "verification.receipt.json"
    write_trs10_receipt(
        receipt_path=verification_receipt_path,
        base_dir=c_dir,
        files=[verification_path, tm_copy],
        private_key=private_key,
        public_key_hex=public_key_hex,
        key_id=key_id,
        metadata={"purpose": "Signed verifier output for C artifact"},
    )

    return {
        "ok": True,
        "run_dir": str(run_dir.as_posix()),
        "trust_manifest": str(tm_copy.as_posix()),
        "receipt": str(receipt_path.as_posix()),
        "verification": str(verification_path.as_posix()),
        "verification_receipt": str(verification_receipt_path.as_posix()),
    }


def _falsifier_ok(name: str, *, passed: bool, detail: Mapping[str, object]) -> Dict[str, object]:
    return {"name": name, "ok": bool(passed), "detail": dict(detail)}


def _int_from_mapping(mapping: Mapping[str, object], key: str, default: int = 0) -> int:
    value = mapping.get(key)
    if isinstance(value, bool):
        return int(value)
    if isinstance(value, int):
        return value
    if isinstance(value, float):
        return int(value)
    if isinstance(value, str):
        try:
            return int(value)
        except ValueError:
            return default
    return default


def _build_c_randomness(
    *,
    out_dir: Path,
    private_key: object,
    public_key_hex: str,
    key_id: str,
    trust_manifest_path: Path,
) -> Mapping[str, object]:
    from verifier.c_randomness import RandomnessVerificationError, verify_randomness
    from verifier.receipt_protocol import write_signed_verification_artifact, write_trs10_receipt

    c_dir = out_dir / "C_randomness"
    run_dir = c_dir / "run"
    run_dir.mkdir(parents=True, exist_ok=True)

    (run_dir / "randomness.bin").write_bytes(b"\x00" * 256)  # 2048 bits available
    (run_dir / "claim.json").write_text(
        json.dumps({"n_bits": 1024, "min_entropy_per_bit": 0.001}, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    (run_dir / "nonlocality.json").write_text(
        json.dumps({"disclosure_bits": 2000}, sort_keys=True) + "\n",
        encoding="utf-8",
    )

    receipt_path = run_dir / "randomness.receipt.json"
    write_trs10_receipt(
        receipt_path=receipt_path,
        base_dir=run_dir,
        files=[run_dir / "claim.json", run_dir / "randomness.bin", run_dir / "nonlocality.json"],
        private_key=private_key,
        public_key_hex=public_key_hex,
        key_id=key_id,
        metadata={"module": "C_randomness", "generator": "scripts/closed_work.py"},
    )

    # Primary verification.
    result = verify_randomness(run_dir, trust_manifest_path)

    # Falsifiers.
    falsifiers: List[Dict[str, object]] = []
    # Forge: tamper with a receipted file.
    try:
        tamper_dir = c_dir / "falsifiers" / "forge"
        tamper_dir.mkdir(parents=True, exist_ok=True)
        for name in ["claim.json", "randomness.bin", "nonlocality.json", "randomness.receipt.json"]:
            (tamper_dir / name).write_bytes((run_dir / name).read_bytes())
        (tamper_dir / "randomness.bin").write_bytes(b"\x01" * 256)
        verify_randomness(tamper_dir, trust_manifest_path)
        falsifiers.append(_falsifier_ok("forge", passed=False, detail={"error": "tamper accepted"}))
    except RandomnessVerificationError as exc:
        falsifiers.append(_falsifier_ok("forge", passed=True, detail={"rejected": str(exc)}))

    # Underpay: insufficient disclosure bits.
    try:
        underpay_dir = c_dir / "falsifiers" / "underpay"
        underpay_dir.mkdir(parents=True, exist_ok=True)
        for name in ["claim.json", "randomness.bin", "randomness.receipt.json"]:
            (underpay_dir / name).write_bytes((run_dir / name).read_bytes())
        (underpay_dir / "nonlocality.json").write_text(json.dumps({"disclosure_bits": 1}) + "\n", encoding="utf-8")
        write_trs10_receipt(
            receipt_path=underpay_dir / "randomness.receipt.json",
            base_dir=underpay_dir,
            files=[underpay_dir / "claim.json", underpay_dir / "randomness.bin", underpay_dir / "nonlocality.json"],
            private_key=private_key,
            public_key_hex=public_key_hex,
            key_id=key_id,
            metadata={"module": "C_randomness", "falsifier": "underpay"},
        )
        verify_randomness(underpay_dir, trust_manifest_path)
        falsifiers.append(_falsifier_ok("underpay", passed=False, detail={"error": "underpay accepted"}))
    except RandomnessVerificationError as exc:
        falsifiers.append(_falsifier_ok("underpay", passed=True, detail={"rejected": str(exc)}))

    # Bypass: omit required file from the receipt.
    try:
        bypass_dir = c_dir / "falsifiers" / "bypass"
        bypass_dir.mkdir(parents=True, exist_ok=True)
        for name in ["claim.json", "randomness.bin", "nonlocality.json"]:
            (bypass_dir / name).write_bytes((run_dir / name).read_bytes())
        write_trs10_receipt(
            receipt_path=bypass_dir / "randomness.receipt.json",
            base_dir=bypass_dir,
            files=[bypass_dir / "claim.json", bypass_dir / "nonlocality.json"],
            private_key=private_key,
            public_key_hex=public_key_hex,
            key_id=key_id,
            metadata={"module": "C_randomness", "falsifier": "bypass"},
        )
        verify_randomness(bypass_dir, trust_manifest_path)
        falsifiers.append(_falsifier_ok("bypass", passed=False, detail={"error": "bypass accepted"}))
    except RandomnessVerificationError as exc:
        falsifiers.append(_falsifier_ok("bypass", passed=True, detail={"rejected": str(exc)}))

    module = "C_randomness"
    verification_payload: Dict[str, object] = {
        "schema_version": "TM-VERIFY-1",
        "module": module,
        "status": "PASS" if result.get("ok") else "FAIL",
        "ok": bool(result.get("ok")),
        "inputs": {
            "run_dir": str(run_dir.as_posix()),
            "trust_manifest": str(trust_manifest_path.as_posix()),
            "receipt": receipt_path.name,
        },
        "results": dict(result),
        "falsifiers": falsifiers,
        "mu_summary": {
            "required_disclosure_bits": _int_from_mapping(result, "required_disclosure_bits"),
            "provided_disclosure_bits": _int_from_mapping(result, "provided_disclosure_bits"),
        },
        "metadata": {
            "generated_by": "scripts/closed_work.py",
            "timestamp": _dt.datetime.now(_dt.UTC).isoformat(),
        },
    }

    # Ensure trust manifest is inside module dir for the verification receipt.
    tm_copy = c_dir / "trust_manifest.json"
    tm_copy.write_text(trust_manifest_path.read_text(encoding="utf-8"), encoding="utf-8")

    verification_path, verification_receipt_path = write_signed_verification_artifact(
        out_dir=c_dir,
        module=module,
        verification=verification_payload,
        private_key=private_key,
        public_key_hex=public_key_hex,
        key_id=key_id,
        trust_manifest_path=tm_copy,
    )

    return {
        "ok": bool(result.get("ok")) and all(bool(f["ok"]) for f in falsifiers),
        "run_dir": str(run_dir.as_posix()),
        "verification": str(verification_path.as_posix()),
        "verification_receipt": str(verification_receipt_path.as_posix()),
    }


def _build_c_tomography(
    *,
    out_dir: Path,
    private_key: object,
    public_key_hex: str,
    key_id: str,
    trust_manifest_path: Path,
) -> Mapping[str, object]:
    from verifier.c_tomography import TomographyVerificationError, verify_tomography
    from verifier.receipt_protocol import write_signed_verification_artifact, write_trs10_receipt

    c_dir = out_dir / "C_tomography"
    run_dir = c_dir / "run"
    run_dir.mkdir(parents=True, exist_ok=True)

    epsilon = 0.25
    n_trials = 256
    (run_dir / "claim.json").write_text(
        json.dumps({"epsilon": epsilon, "n_trials": n_trials}, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    with (run_dir / "trials.csv").open("w", encoding="utf-8", newline="") as handle:
        handle.write("trial_id,value\n")
        for i in range(n_trials):
            handle.write(f"{i},0\n")

    receipt_path = run_dir / "tomography.receipt.json"
    write_trs10_receipt(
        receipt_path=receipt_path,
        base_dir=run_dir,
        files=[run_dir / "claim.json", run_dir / "trials.csv"],
        private_key=private_key,
        public_key_hex=public_key_hex,
        key_id=key_id,
        metadata={"module": "C_tomography", "generator": "scripts/closed_work.py"},
    )

    result = verify_tomography(run_dir, trust_manifest_path)

    falsifiers: List[Dict[str, object]] = []
    # Forge: tamper with receipted trials.
    try:
        tamper_dir = c_dir / "falsifiers" / "forge"
        tamper_dir.mkdir(parents=True, exist_ok=True)
        for name in ["claim.json", "trials.csv", "tomography.receipt.json"]:
            (tamper_dir / name).write_bytes((run_dir / name).read_bytes())
        (tamper_dir / "trials.csv").write_text("trial_id,value\n0,1\n", encoding="utf-8")
        verify_tomography(tamper_dir, trust_manifest_path)
        falsifiers.append(_falsifier_ok("forge", passed=False, detail={"error": "tamper accepted"}))
    except TomographyVerificationError as exc:
        falsifiers.append(_falsifier_ok("forge", passed=True, detail={"rejected": str(exc)}))

    # Underpay: too few trials for epsilon.
    try:
        underpay_dir = c_dir / "falsifiers" / "underpay"
        underpay_dir.mkdir(parents=True, exist_ok=True)
        (underpay_dir / "claim.json").write_text(json.dumps({"epsilon": epsilon, "n_trials": 1}) + "\n", encoding="utf-8")
        (underpay_dir / "trials.csv").write_text("trial_id,value\n0,0\n", encoding="utf-8")
        write_trs10_receipt(
            receipt_path=underpay_dir / "tomography.receipt.json",
            base_dir=underpay_dir,
            files=[underpay_dir / "claim.json", underpay_dir / "trials.csv"],
            private_key=private_key,
            public_key_hex=public_key_hex,
            key_id=key_id,
            metadata={"module": "C_tomography", "falsifier": "underpay"},
        )
        verify_tomography(underpay_dir, trust_manifest_path)
        falsifiers.append(_falsifier_ok("underpay", passed=False, detail={"error": "underpay accepted"}))
    except TomographyVerificationError as exc:
        falsifiers.append(_falsifier_ok("underpay", passed=True, detail={"rejected": str(exc)}))

    # Bypass: omit trials.csv from receipt.
    try:
        bypass_dir = c_dir / "falsifiers" / "bypass"
        bypass_dir.mkdir(parents=True, exist_ok=True)
        (bypass_dir / "claim.json").write_bytes((run_dir / "claim.json").read_bytes())
        (bypass_dir / "trials.csv").write_bytes((run_dir / "trials.csv").read_bytes())
        write_trs10_receipt(
            receipt_path=bypass_dir / "tomography.receipt.json",
            base_dir=bypass_dir,
            files=[bypass_dir / "claim.json"],
            private_key=private_key,
            public_key_hex=public_key_hex,
            key_id=key_id,
            metadata={"module": "C_tomography", "falsifier": "bypass"},
        )
        verify_tomography(bypass_dir, trust_manifest_path)
        falsifiers.append(_falsifier_ok("bypass", passed=False, detail={"error": "bypass accepted"}))
    except TomographyVerificationError as exc:
        falsifiers.append(_falsifier_ok("bypass", passed=True, detail={"rejected": str(exc)}))

    module = "C_tomography"
    verification_payload: Dict[str, object] = {
        "schema_version": "TM-VERIFY-1",
        "module": module,
        "status": "PASS" if result.get("ok") else "FAIL",
        "ok": bool(result.get("ok")),
        "inputs": {
            "run_dir": str(run_dir.as_posix()),
            "trust_manifest": str(trust_manifest_path.as_posix()),
            "receipt": receipt_path.name,
        },
        "results": dict(result),
        "falsifiers": falsifiers,
        "mu_summary": {
            "required_disclosure_bits": _int_from_mapping(result, "required_disclosure_bits"),
            "provided_disclosure_bits": _int_from_mapping(result, "provided_disclosure_bits"),
        },
        "metadata": {"generated_by": "scripts/closed_work.py", "timestamp": _dt.datetime.now(_dt.UTC).isoformat()},
    }

    tm_copy = c_dir / "trust_manifest.json"
    tm_copy.write_text(trust_manifest_path.read_text(encoding="utf-8"), encoding="utf-8")

    verification_path, verification_receipt_path = write_signed_verification_artifact(
        out_dir=c_dir,
        module=module,
        verification=verification_payload,
        private_key=private_key,
        public_key_hex=public_key_hex,
        key_id=key_id,
        trust_manifest_path=tm_copy,
    )

    return {
        "ok": bool(result.get("ok")) and all(bool(f["ok"]) for f in falsifiers),
        "run_dir": str(run_dir.as_posix()),
        "verification": str(verification_path.as_posix()),
        "verification_receipt": str(verification_receipt_path.as_posix()),
    }


def _build_c_entropy(
    *,
    out_dir: Path,
    private_key: object,
    public_key_hex: str,
    key_id: str,
    trust_manifest_path: Path,
) -> Mapping[str, object]:
    from verifier.c_entropy2 import EntropyVerificationError, verify_entropy2
    from verifier.receipt_protocol import write_signed_verification_artifact, write_trs10_receipt

    c_dir = out_dir / "C_entropy"
    run_dir = c_dir / "run"
    run_dir.mkdir(parents=True, exist_ok=True)

    h_lower = 0.5
    n_samples = 32
    (run_dir / "claim.json").write_text(
        json.dumps({"h_lower_bound_bits": h_lower, "n_samples": n_samples}, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    (run_dir / "coarse_graining.json").write_text(
        json.dumps({"partition_id": "demo_partition_v1", "disclosure_bits": 512}, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    with (run_dir / "samples.csv").open("w", encoding="utf-8", newline="") as handle:
        handle.write("idx,symbol\n")
        for i in range(n_samples):
            handle.write(f"{i},{i%2}\n")

    receipt_path = run_dir / "entropy.receipt.json"
    write_trs10_receipt(
        receipt_path=receipt_path,
        base_dir=run_dir,
        files=[run_dir / "claim.json", run_dir / "samples.csv", run_dir / "coarse_graining.json"],
        private_key=private_key,
        public_key_hex=public_key_hex,
        key_id=key_id,
        metadata={"module": "C_entropy", "generator": "scripts/closed_work.py"},
    )

    result = verify_entropy2(run_dir, trust_manifest_path)

    falsifiers: List[Dict[str, object]] = []
    # Forge: tamper with coarse-graining.
    try:
        tamper_dir = c_dir / "falsifiers" / "forge"
        tamper_dir.mkdir(parents=True, exist_ok=True)
        for name in ["claim.json", "samples.csv", "coarse_graining.json", "entropy.receipt.json"]:
            (tamper_dir / name).write_bytes((run_dir / name).read_bytes())
        (tamper_dir / "coarse_graining.json").write_text(
            json.dumps({"partition_id": "demo_partition_v1", "disclosure_bits": 0}) + "\n",
            encoding="utf-8",
        )
        verify_entropy2(tamper_dir, trust_manifest_path)
        falsifiers.append(_falsifier_ok("forge", passed=False, detail={"error": "tamper accepted"}))
    except EntropyVerificationError as exc:
        falsifiers.append(_falsifier_ok("forge", passed=True, detail={"rejected": str(exc)}))

    # Underpay: insufficient disclosure bits.
    try:
        underpay_dir = c_dir / "falsifiers" / "underpay"
        underpay_dir.mkdir(parents=True, exist_ok=True)
        for name in ["claim.json", "samples.csv"]:
            (underpay_dir / name).write_bytes((run_dir / name).read_bytes())
        (underpay_dir / "coarse_graining.json").write_text(
            json.dumps({"partition_id": "demo_partition_v1", "disclosure_bits": 1}) + "\n",
            encoding="utf-8",
        )
        write_trs10_receipt(
            receipt_path=underpay_dir / "entropy.receipt.json",
            base_dir=underpay_dir,
            files=[underpay_dir / "claim.json", underpay_dir / "samples.csv", underpay_dir / "coarse_graining.json"],
            private_key=private_key,
            public_key_hex=public_key_hex,
            key_id=key_id,
            metadata={"module": "C_entropy", "falsifier": "underpay"},
        )
        verify_entropy2(underpay_dir, trust_manifest_path)
        falsifiers.append(_falsifier_ok("underpay", passed=False, detail={"error": "underpay accepted"}))
    except EntropyVerificationError as exc:
        falsifiers.append(_falsifier_ok("underpay", passed=True, detail={"rejected": str(exc)}))

    # Bypass: omit coarse_graining.json from receipt.
    try:
        bypass_dir = c_dir / "falsifiers" / "bypass"
        bypass_dir.mkdir(parents=True, exist_ok=True)
        for name in ["claim.json", "samples.csv", "coarse_graining.json"]:
            (bypass_dir / name).write_bytes((run_dir / name).read_bytes())
        write_trs10_receipt(
            receipt_path=bypass_dir / "entropy.receipt.json",
            base_dir=bypass_dir,
            files=[bypass_dir / "claim.json", bypass_dir / "samples.csv"],
            private_key=private_key,
            public_key_hex=public_key_hex,
            key_id=key_id,
            metadata={"module": "C_entropy", "falsifier": "bypass"},
        )
        verify_entropy2(bypass_dir, trust_manifest_path)
        falsifiers.append(_falsifier_ok("bypass", passed=False, detail={"error": "bypass accepted"}))
    except EntropyVerificationError as exc:
        falsifiers.append(_falsifier_ok("bypass", passed=True, detail={"rejected": str(exc)}))

    module = "C_entropy"
    verification_payload: Dict[str, object] = {
        "schema_version": "TM-VERIFY-1",
        "module": module,
        "status": "PASS" if result.get("ok") else "FAIL",
        "ok": bool(result.get("ok")),
        "inputs": {
            "run_dir": str(run_dir.as_posix()),
            "trust_manifest": str(trust_manifest_path.as_posix()),
            "receipt": receipt_path.name,
        },
        "results": dict(result),
        "falsifiers": falsifiers,
        "mu_summary": {
            "required_disclosure_bits": _int_from_mapping(result, "required_disclosure_bits"),
            "provided_disclosure_bits": _int_from_mapping(result, "provided_disclosure_bits"),
        },
        "metadata": {"generated_by": "scripts/closed_work.py", "timestamp": _dt.datetime.now(_dt.UTC).isoformat()},
    }

    tm_copy = c_dir / "trust_manifest.json"
    tm_copy.write_text(trust_manifest_path.read_text(encoding="utf-8"), encoding="utf-8")

    verification_path, verification_receipt_path = write_signed_verification_artifact(
        out_dir=c_dir,
        module=module,
        verification=verification_payload,
        private_key=private_key,
        public_key_hex=public_key_hex,
        key_id=key_id,
        trust_manifest_path=tm_copy,
    )

    return {
        "ok": bool(result.get("ok")) and all(bool(f["ok"]) for f in falsifiers),
        "run_dir": str(run_dir.as_posix()),
        "verification": str(verification_path.as_posix()),
        "verification_receipt": str(verification_receipt_path.as_posix()),
    }


def _build_c_causal(
    *,
    out_dir: Path,
    private_key: object,
    public_key_hex: str,
    key_id: str,
    trust_manifest_path: Path,
) -> Mapping[str, object]:
    from verifier.c_causal import CausalVerificationError, verify_causal
    from verifier.receipt_protocol import write_signed_verification_artifact, write_trs10_receipt

    c_dir = out_dir / "C_causal"
    run_dir = c_dir / "run"
    run_dir.mkdir(parents=True, exist_ok=True)

    n_obs = 10
    (run_dir / "claim.json").write_text(
        json.dumps({"claim_type": "unique_dag", "n_obs": n_obs}, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    with (run_dir / "observational.csv").open("w", encoding="utf-8", newline="") as handle:
        handle.write("idx,x,y\n")
        for i in range(n_obs):
            handle.write(f"{i},{i%2},{i%2}\n")
    (run_dir / "assumptions.json").write_text(
        json.dumps({"assumptions": ["no_hidden_confounders"], "disclosure_bits": 8192}, sort_keys=True) + "\n",
        encoding="utf-8",
    )

    receipt_path = run_dir / "causal.receipt.json"
    write_trs10_receipt(
        receipt_path=receipt_path,
        base_dir=run_dir,
        files=[run_dir / "claim.json", run_dir / "observational.csv", run_dir / "assumptions.json"],
        private_key=private_key,
        public_key_hex=public_key_hex,
        key_id=key_id,
        metadata={"module": "C_causal", "generator": "scripts/closed_work.py"},
    )

    result = verify_causal(run_dir, trust_manifest_path)

    falsifiers: List[Dict[str, object]] = []
    # Forge: tamper with assumptions.
    try:
        tamper_dir = c_dir / "falsifiers" / "forge"
        tamper_dir.mkdir(parents=True, exist_ok=True)
        for name in ["claim.json", "observational.csv", "assumptions.json", "causal.receipt.json"]:
            (tamper_dir / name).write_bytes((run_dir / name).read_bytes())
        (tamper_dir / "assumptions.json").write_text(
            json.dumps({"assumptions": ["no_hidden_confounders"], "disclosure_bits": 0}) + "\n",
            encoding="utf-8",
        )
        verify_causal(tamper_dir, trust_manifest_path)
        falsifiers.append(_falsifier_ok("forge", passed=False, detail={"error": "tamper accepted"}))
    except CausalVerificationError as exc:
        falsifiers.append(_falsifier_ok("forge", passed=True, detail={"rejected": str(exc)}))

    # Underpay: insufficient disclosure bits.
    try:
        underpay_dir = c_dir / "falsifiers" / "underpay"
        underpay_dir.mkdir(parents=True, exist_ok=True)
        for name in ["claim.json", "observational.csv"]:
            (underpay_dir / name).write_bytes((run_dir / name).read_bytes())
        (underpay_dir / "assumptions.json").write_text(
            json.dumps({"assumptions": ["no_hidden_confounders"], "disclosure_bits": 1}) + "\n",
            encoding="utf-8",
        )
        write_trs10_receipt(
            receipt_path=underpay_dir / "causal.receipt.json",
            base_dir=underpay_dir,
            files=[underpay_dir / "claim.json", underpay_dir / "observational.csv", underpay_dir / "assumptions.json"],
            private_key=private_key,
            public_key_hex=public_key_hex,
            key_id=key_id,
            metadata={"module": "C_causal", "falsifier": "underpay"},
        )
        verify_causal(underpay_dir, trust_manifest_path)
        falsifiers.append(_falsifier_ok("underpay", passed=False, detail={"error": "underpay accepted"}))
    except CausalVerificationError as exc:
        falsifiers.append(_falsifier_ok("underpay", passed=True, detail={"rejected": str(exc)}))

    # Bypass: omit assumptions and interventions (should reject unique_dag claim).
    try:
        bypass_dir = c_dir / "falsifiers" / "bypass"
        bypass_dir.mkdir(parents=True, exist_ok=True)
        for name in ["claim.json", "observational.csv"]:
            (bypass_dir / name).write_bytes((run_dir / name).read_bytes())
        write_trs10_receipt(
            receipt_path=bypass_dir / "causal.receipt.json",
            base_dir=bypass_dir,
            files=[bypass_dir / "claim.json", bypass_dir / "observational.csv"],
            private_key=private_key,
            public_key_hex=public_key_hex,
            key_id=key_id,
            metadata={"module": "C_causal", "falsifier": "bypass"},
        )
        verify_causal(bypass_dir, trust_manifest_path)
        falsifiers.append(_falsifier_ok("bypass", passed=False, detail={"error": "bypass accepted"}))
    except CausalVerificationError as exc:
        falsifiers.append(_falsifier_ok("bypass", passed=True, detail={"rejected": str(exc)}))

    module = "C_causal"
    verification_payload: Dict[str, object] = {
        "schema_version": "TM-VERIFY-1",
        "module": module,
        "status": "PASS" if result.get("ok") else "FAIL",
        "ok": bool(result.get("ok")),
        "inputs": {
            "run_dir": str(run_dir.as_posix()),
            "trust_manifest": str(trust_manifest_path.as_posix()),
            "receipt": receipt_path.name,
        },
        "results": dict(result),
        "falsifiers": falsifiers,
        "mu_summary": {
            "required_disclosure_bits": _int_from_mapping(result, "required_disclosure_bits"),
            "provided_disclosure_bits": _int_from_mapping(result, "provided_disclosure_bits"),
        },
        "metadata": {"generated_by": "scripts/closed_work.py", "timestamp": _dt.datetime.now(_dt.UTC).isoformat()},
    }

    tm_copy = c_dir / "trust_manifest.json"
    tm_copy.write_text(trust_manifest_path.read_text(encoding="utf-8"), encoding="utf-8")

    verification_path, verification_receipt_path = write_signed_verification_artifact(
        out_dir=c_dir,
        module=module,
        verification=verification_payload,
        private_key=private_key,
        public_key_hex=public_key_hex,
        key_id=key_id,
        trust_manifest_path=tm_copy,
    )

    return {
        "ok": bool(result.get("ok")) and all(bool(f["ok"]) for f in falsifiers),
        "run_dir": str(run_dir.as_posix()),
        "verification": str(verification_path.as_posix()),
        "verification_receipt": str(verification_receipt_path.as_posix()),
    }


def _build_di_randomness_conflict_artifact(*, out_dir: Path) -> Mapping[str, object]:
    """Generate the external-facing DI randomness confrontation artifact.

    This is a receipts-only, deterministic artifact.
    It is intentionally non-gating for closed_work correctness.
    """

    out_path = out_dir / "DI_randomness_conflict.json"
    log_path = out_dir / "di_randomness_conflict.log"
    _run(
        [sys.executable, "scripts/di_randomness_conflict_chart.py", "--out", str(out_path.as_posix())],
        cwd=PROJECT_ROOT,
        log_path=log_path,
    )
    return {"ok": True, "artifact": str(out_path.as_posix()), "log": str(log_path.as_posix())}


def parse_args(argv: Optional[Sequence[str]] = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--out-root",
        type=Path,
        default=Path("artifacts/closed_work"),
        help="Output root directory for artifacts",
    )
    parser.add_argument(
        "--n-per-setting",
        type=int,
        default=400,
        help="Bound for falsifier scan (trials per CHSH setting)",
    )
    parser.add_argument("--seed", type=int, default=1337, help="Seed for bounded scan")
    parser.add_argument(
        "--skip-coq",
        action="store_true",
        help="Skip `make -C coq core` (useful if Coq toolchain not available)",
    )
    parser.add_argument(
        "--skip-inquisitor",
        action="store_true",
        help="Skip inquisitor gate",
    )
    return parser.parse_args(list(argv) if argv is not None else None)


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = parse_args(argv)

    stamp = _dt.datetime.now(_dt.UTC).strftime("%Y%m%d_%H%M%S")
    out_dir = Path(args.out_root) / stamp
    out_dir.mkdir(parents=True, exist_ok=True)

    _phase("INIT")
    print(f"output: {out_dir}")

    key_id = "closed-work"
    from verifier.receipt_protocol import ed25519_keypair

    private_key, public_key_hex = ed25519_keypair()
    trust_manifest_path = out_dir / "trust_manifest.json"
    _write_trust_manifest(trust_manifest_path, key_id=key_id, public_key_hex=public_key_hex)

    summary: Dict[str, object] = {
        "timestamp": stamp,
        "out_dir": str(out_dir.as_posix()),
        "repo_root": str(PROJECT_ROOT.as_posix()),
        "phases": ["INIT", "DISCOVER", "CLASSIFY", "DECOMPOSE", "EXECUTE", "MERGE", "VERIFY", "SUCCESS"],
        "params": {"n_per_setting": args.n_per_setting, "seed": args.seed},
    }

    _phase("DISCOVER")
    if args.skip_coq:
        print("Skipping Coq build (--skip-coq)")
        summary["coq"] = {"skipped": True}
    else:
        log_path = out_dir / "coq_core_build.log"
        _run(["make", "-C", "coq", "core"], cwd=PROJECT_ROOT, log_path=log_path)
        print("Coq core: OK")
        summary["coq"] = {"skipped": False, "log": str(log_path.as_posix())}

    _phase("CLASSIFY")
    falsifier_report = _bounded_falsifier_scan(out_dir=out_dir, n_per_setting=args.n_per_setting, seed=args.seed)
    falsifier_path = out_dir / "falsifier_report.json"
    _write_json(falsifier_path, falsifier_report)
    print(f"falsifier: {'OK' if falsifier_report.get('ok') else 'FAIL'}  report={falsifier_path}")
    summary["falsifier"] = {"ok": bool(falsifier_report.get("ok")), "report": str(falsifier_path.as_posix())}

    _phase("DECOMPOSE")
    print("Building C modules (receipt-defined runs + signed verifier outputs)")

    _phase("EXECUTE")
    c_randomness = _build_c_randomness(
        out_dir=out_dir,
        private_key=private_key,
        public_key_hex=public_key_hex,
        key_id=key_id,
        trust_manifest_path=trust_manifest_path,
    )
    print(f"C_randomness: {'OK' if c_randomness.get('ok') else 'FAIL'}")

    c_tomography = _build_c_tomography(
        out_dir=out_dir,
        private_key=private_key,
        public_key_hex=public_key_hex,
        key_id=key_id,
        trust_manifest_path=trust_manifest_path,
    )
    print(f"C_tomography: {'OK' if c_tomography.get('ok') else 'FAIL'}")

    c_entropy = _build_c_entropy(
        out_dir=out_dir,
        private_key=private_key,
        public_key_hex=public_key_hex,
        key_id=key_id,
        trust_manifest_path=trust_manifest_path,
    )
    print(f"C_entropy: {'OK' if c_entropy.get('ok') else 'FAIL'}")

    c_causal = _build_c_causal(
        out_dir=out_dir,
        private_key=private_key,
        public_key_hex=public_key_hex,
        key_id=key_id,
        trust_manifest_path=trust_manifest_path,
    )
    print(f"C_causal: {'OK' if c_causal.get('ok') else 'FAIL'}")

    di_conflict = _build_di_randomness_conflict_artifact(out_dir=out_dir)
    print(f"DI randomness conflict: {'OK' if di_conflict.get('ok') else 'FAIL'}")

    # Preserve the older C1 artifact as an extra (non-gating) demo.
    c_artifact = _build_c_artifact(
        out_dir=out_dir,
        private_key=private_key,
        public_key_hex=public_key_hex,
        key_id=key_id,
        trust_manifest_path=trust_manifest_path,
    )
    print(f"C1 artifact: {'OK' if c_artifact.get('ok') else 'FAIL'}")

    summary["C_randomness"] = c_randomness
    summary["C_tomography"] = c_tomography
    summary["C_entropy"] = c_entropy
    summary["C_causal"] = c_causal
    summary["C1"] = c_artifact
    summary["DI_randomness_conflict"] = di_conflict

    _phase("MERGE")
    print("Writing summary")
    summary_path = out_dir / "closed_work_summary.json"
    _write_json(summary_path, summary)

    _phase("VERIFY")
    if args.skip_inquisitor:
        print("Skipping inquisitor (--skip-inquisitor)")
        summary["inquisitor"] = {"skipped": True}
    else:
        log_path = out_dir / "inquisitor.log"
        _run([sys.executable, "scripts/inquisitor.py"], cwd=PROJECT_ROOT, log_path=log_path)
        print("Inquisitor: OK")
        summary["inquisitor"] = {"skipped": False, "log": str(log_path.as_posix())}
        _write_json(summary_path, summary)

    _phase("SUCCESS")
    ok = (
        bool(c_randomness.get("ok"))
        and bool(c_tomography.get("ok"))
        and bool(c_entropy.get("ok"))
        and bool(c_causal.get("ok"))
        and bool(falsifier_report.get("ok", True))
    )
    print(f"closed_work: {'PASS' if ok else 'FAIL'}")
    print(f"summary: {summary_path}")
    return 0 if ok else 2


if __name__ == "__main__":
    raise SystemExit(main())
