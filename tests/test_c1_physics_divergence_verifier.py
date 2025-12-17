"""C1 falsifier harness: receipt-defined physics/bench verification.

This is intentionally minimal and repo-internal:
- we verify a signed TRS-1.0 manifest over run artifacts
- we reject improvements that lack explicit calibration/disclosure

External protocol mapping (true physics) is tracked separately as C1.4.
"""

from __future__ import annotations

import json
import hashlib
from pathlib import Path
from typing import Dict, Tuple

import pytest
from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey

from verifier.physics_divergence import (
    PhysicsDivergenceVerificationError,
    compute_trs10_global_digest,
    verify_physics_divergence,
)


@pytest.fixture
def ed25519_keypair() -> Tuple[Ed25519PrivateKey, str]:
    private_key = Ed25519PrivateKey.generate()
    public_hex = private_key.public_key().public_bytes(
        encoding=serialization.Encoding.Raw,
        format=serialization.PublicFormat.Raw,
    ).hex()
    return private_key, public_hex


def _sha256_hex(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _write_trust_manifest(path: Path, key_id: str, public_key: str) -> Path:
    manifest = {
        "trusted_keys": {
            key_id: {
                "public_key": public_key,
                "patterns": ["*"],
            }
        }
    }
    path.write_text(json.dumps(manifest), encoding="utf-8")
    return path


def _create_run_dir(
    tmp_path: Path,
    *,
    baseline: float,
    claimed: float,
    epsilon: float,
    include_calibration: bool,
    disclosure_bits: int | None,
    key_id: str,
    private_key: Ed25519PrivateKey,
    public_key: str,
) -> Tuple[Path, Path]:
    run_dir = tmp_path / "run"
    run_dir.mkdir(parents=True, exist_ok=True)

    measurement_path = run_dir / "measurement.csv"
    measurement_path.write_text("t,value\n0,1.0\n1,1.1\n", encoding="utf-8")

    claim_path = run_dir / "claim.json"
    claim_path.write_text(
        json.dumps(
            {
                "metric": "demo_metric",
                "baseline": baseline,
                "claimed": claimed,
                "epsilon": epsilon,
            },
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )

    calibration_path = run_dir / "calibration.json"
    if include_calibration:
        calibration_path.write_text(
            json.dumps(
                {
                    "disclosure_bits": disclosure_bits,
                    "protocol": "demo",
                },
                sort_keys=True,
            )
            + "\n",
            encoding="utf-8",
        )

    files = [
        {
            "path": measurement_path.name,
            "sha256": _sha256_hex(measurement_path.read_bytes()),
        },
        {
            "path": claim_path.name,
            "sha256": _sha256_hex(claim_path.read_bytes()),
        },
    ]

    if include_calibration:
        files.append(
            {
                "path": calibration_path.name,
                "sha256": _sha256_hex(calibration_path.read_bytes()),
            }
        )

    global_digest = compute_trs10_global_digest(files)
    signature = private_key.sign(global_digest.encode("utf-8")).hex()

    receipt = {
        "version": "TRS-1.0",
        "files": files,
        "global_digest": global_digest,
        "sig_scheme": "ed25519",
        "signature": signature,
        "public_key": public_key,
        "key_id": key_id,
    }

    receipt_path = run_dir / "physics.receipt.json"
    receipt_path.write_text(json.dumps(receipt, sort_keys=True) + "\n", encoding="utf-8")

    trust_manifest_path = tmp_path / "trust_manifest.json"
    _write_trust_manifest(trust_manifest_path, key_id=key_id, public_key=public_key)

    return run_dir, trust_manifest_path


def test_c1_rejects_improvement_without_calibration(ed25519_keypair: Tuple[Ed25519PrivateKey, str], tmp_path: Path) -> None:
    private_key, public_key = ed25519_keypair
    run_dir, trust_manifest_path = _create_run_dir(
        tmp_path,
        baseline=0.10,
        claimed=0.50,
        epsilon=0.05,
        include_calibration=False,
        disclosure_bits=None,
        key_id="alpha",
        private_key=private_key,
        public_key=public_key,
    )

    with pytest.raises(PhysicsDivergenceVerificationError, match="requires calibration"):
        verify_physics_divergence(run_dir, trust_manifest_path)


def test_c1_rejects_insufficient_disclosure_bits(ed25519_keypair: Tuple[Ed25519PrivateKey, str], tmp_path: Path) -> None:
    private_key, public_key = ed25519_keypair
    run_dir, trust_manifest_path = _create_run_dir(
        tmp_path,
        baseline=0.10,
        claimed=0.50,
        epsilon=0.20,
        include_calibration=True,
        disclosure_bits=1,
        key_id="alpha",
        private_key=private_key,
        public_key=public_key,
    )

    with pytest.raises(PhysicsDivergenceVerificationError, match="Insufficient disclosure_bits"):
        verify_physics_divergence(run_dir, trust_manifest_path)


def test_c1_accepts_certified_improvement(ed25519_keypair: Tuple[Ed25519PrivateKey, str], tmp_path: Path) -> None:
    private_key, public_key = ed25519_keypair
    run_dir, trust_manifest_path = _create_run_dir(
        tmp_path,
        baseline=0.10,
        claimed=0.50,
        epsilon=0.20,
        include_calibration=True,
        disclosure_bits=9999,
        key_id="alpha",
        private_key=private_key,
        public_key=public_key,
    )

    result = verify_physics_divergence(run_dir, trust_manifest_path)
    assert result["ok"] is True
    assert result["improved"] is True


def test_c1_accepts_non_improvement_without_calibration(ed25519_keypair: Tuple[Ed25519PrivateKey, str], tmp_path: Path) -> None:
    private_key, public_key = ed25519_keypair
    run_dir, trust_manifest_path = _create_run_dir(
        tmp_path,
        baseline=0.10,
        claimed=0.12,
        epsilon=0.05,
        include_calibration=False,
        disclosure_bits=None,
        key_id="alpha",
        private_key=private_key,
        public_key=public_key,
    )

    result = verify_physics_divergence(run_dir, trust_manifest_path)
    assert result["ok"] is True
    assert result["improved"] is False
