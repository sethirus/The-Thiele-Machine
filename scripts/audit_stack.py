#!/usr/bin/env python3
"""Run a reproducible stack audit and emit a signed JSON summary.

Audit gates:
1. Coq build
2. Canonical source pipeline tests
3. Bitlock chain hash gate
4. Cross-layer lockstep gates (with stable timeout)
5. Example program batch run
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List

try:
    from cryptography.hazmat.primitives import serialization
    from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
except Exception:  # pragma: no cover
    Ed25519PrivateKey = None  # type: ignore[assignment]
    serialization = None  # type: ignore[assignment]


ROOT = Path(__file__).resolve().parents[1]
OUT_DIR = ROOT / "artifacts" / "proof_gate"

import sys as _sys
_sys.path.insert(0, str(Path(__file__).resolve().parent))
from _signing_key import resolve_signing_key_path


def utc_now() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def canonical_json_bytes(obj: Dict[str, Any]) -> bytes:
    return json.dumps(obj, sort_keys=True, separators=(",", ":")).encode("utf-8")


def run_step(name: str, command: List[str], timeout: int, extra_env: Dict[str, str] | None = None) -> Dict[str, Any]:
    env = dict(os.environ)
    if extra_env:
        env.update(extra_env)

    result = subprocess.run(
        command,
        cwd=str(ROOT),
        capture_output=True,
        text=True,
        timeout=timeout,
        env=env,
    )

    stdout = result.stdout
    stderr = result.stderr
    combined = ""
    if stdout:
        combined += stdout
    if stderr:
        if combined:
            combined += "\n"
        combined += stderr

    log_path = OUT_DIR / f"stack_audit_{name}.log"
    log_path.write_text(combined, encoding="utf-8")

    return {
        "name": name,
        "command": " ".join(command),
        "exit_code": result.returncode,
        "ok": result.returncode == 0,
        "timeout_sec": timeout,
        "log": str(log_path.relative_to(ROOT)),
        "stdout_sha256": sha256_text(stdout),
        "stderr_sha256": sha256_text(stderr),
    }


def load_or_create_key(path: Path):
    if Ed25519PrivateKey is None or serialization is None:
        return None

    if path.exists() and path.stat().st_size > 0:
        return serialization.load_pem_private_key(path.read_bytes(), password=None)

    path.parent.mkdir(parents=True, exist_ok=True)
    key = Ed25519PrivateKey.generate()
    path.write_bytes(
        key.private_bytes(
            encoding=serialization.Encoding.PEM,
            format=serialization.PrivateFormat.PKCS8,
            encryption_algorithm=serialization.NoEncryption(),
        )
    )
    pub_path = path.with_suffix(".pub.pem")
    pub_path.write_bytes(
        key.public_key().public_bytes(
            encoding=serialization.Encoding.PEM,
            format=serialization.PublicFormat.SubjectPublicKeyInfo,
        )
    )
    return key


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output",
        default="artifacts/proof_gate/stack_audit_summary.json",
        help="Output JSON path",
    )
    parser.add_argument(
        "--signing-key-file",
        default=None,
        help=(
            "Ed25519 private key path for an authenticated signature. "
            "Defaults to $THIELE_BITLOCK_SIGNING_KEY, else the non-secret "
            "committed reproducibility fixture (integrity-only; warns). "
            "Created if the chosen path is missing."
        ),
    )
    parser.add_argument(
        "--bitlock-timeout",
        type=int,
        default=240,
        help="Per-test timeout for heavy lockstep tests",
    )
    args = parser.parse_args()

    OUT_DIR.mkdir(parents=True, exist_ok=True)

    steps = [
        (
            "coq_build",
            ["make", "-C", "coq", "-j2"],
            900,
            None,
        ),
        (
            "canonical_pipeline",
            ["python3", "-m", "pytest", "-q", "tests/test_canonical_source_pipeline.py"],
            240,
            None,
        ),
        (
            "bitlock_chain_hash_gate",
            [
                "python3",
                "-m",
                "pytest",
                "-q",
                "tests/test_bitlock_proof_vm_cpu.py::test_proof_to_vm_to_cpu_source_chain_hashes_exist",
            ],
            240,
            None,
        ),
        (
            "bitlock_lockstep",
            [
                "python3",
                "-m",
                "pytest",
                "-q",
                "tests/test_bitlock_proof_vm_cpu.py::test_bit_for_bit_state_isomorphism_across_ocaml_python_rtl",
                f"--per-test-timeout={args.bitlock_timeout}",
            ],
            900,
            {"THIELE_RTL_SIM": "iverilog"},
        ),
        (
            "bitlock_prefix_lockstep",
            [
                "python3",
                "-m",
                "pytest",
                "-q",
                "tests/test_bitlock_proof_vm_cpu.py::test_prefix_by_prefix_digest_isomorphism_every_step",
                f"--per-test-timeout={args.bitlock_timeout}",
            ],
            900,
            {"THIELE_RTL_SIM": "iverilog"},
        ),
        (
            "examples_batch",
            ["python3", "examples/run_all.py"],
            600,
            None,
        ),
    ]

    executed: List[Dict[str, Any]] = []
    started = utc_now()

    for name, cmd, timeout, env in steps:
        try:
            step_result = run_step(name, cmd, timeout, env)
        except subprocess.TimeoutExpired:
            log_path = OUT_DIR / f"stack_audit_{name}.log"
            log_path.write_text(f"TIMEOUT after {timeout}s\n", encoding="utf-8")
            step_result = {
                "name": name,
                "command": " ".join(cmd),
                "exit_code": 124,
                "ok": False,
                "timeout_sec": timeout,
                "log": str(log_path.relative_to(ROOT)),
                "stdout_sha256": sha256_text(""),
                "stderr_sha256": sha256_text("timeout"),
            }
        executed.append(step_result)

    summary_unsigned: Dict[str, Any] = {
        "schema": "thiele.stack-audit.v1",
        "started_at": started,
        "finished_at": utc_now(),
        "repo_root": str(ROOT),
        "steps": executed,
        "all_passed": all(s["ok"] for s in executed),
    }

    unsigned_bytes = canonical_json_bytes(summary_unsigned)
    summary: Dict[str, Any] = dict(summary_unsigned)
    summary["aggregate_digest"] = hashlib.sha256(unsigned_bytes).hexdigest()

    key = load_or_create_key(resolve_signing_key_path(args.signing_key_file))
    if key is not None:
        sig = key.sign(unsigned_bytes)
        pub_hex = key.public_key().public_bytes(
            encoding=serialization.Encoding.Raw,
            format=serialization.PublicFormat.Raw,
        ).hex()
        summary["signature"] = {
            "algorithm": "ed25519",
            "public_key_hex": pub_hex,
            "signature_hex": sig.hex(),
            "signed_over": "canonical_json(summary_without_signature_and_aggregate_digest)",
        }
    else:
        summary["signature"] = {
            "algorithm": "none",
            "reason": "cryptography package unavailable",
        }

    out_path = ROOT / args.output
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    print(f"Wrote {out_path}")
    print(f"all_passed={summary['all_passed']}")
    print(f"aggregate_digest={summary['aggregate_digest']}")

    return 0 if summary["all_passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
