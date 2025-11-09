"""CLI tests for trust manifest behaviour in verifier tools."""

from __future__ import annotations

import hashlib
import os
import json
import subprocess
import sys
from pathlib import Path
from typing import Tuple

import pytest
from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey

PROJECT_ROOT = Path(__file__).resolve().parents[2]
REPLAY_CLI = PROJECT_ROOT / "verifier" / "replay.py"
TRS10_CLI = PROJECT_ROOT / "tools" / "verify_trs10.py"

from verifier.replay_helpers import compute_receipt_digest, compute_state_hash, sha256_hex
from tools.verify_trs10 import compute_global_digest


@pytest.fixture
def ed25519_keypair() -> Tuple[Ed25519PrivateKey, str]:
    private_key = Ed25519PrivateKey.generate()
    public_hex = private_key.public_key().public_bytes(
        encoding=serialization.Encoding.Raw,
        format=serialization.PublicFormat.Raw,
    ).hex()
    return private_key, public_hex


def write_trust_manifest(path: Path, key_id: str, public_key: str) -> Path:
    manifest = {
        "trusted_keys": {
            key_id: {
                "public_key": public_key,
                "patterns": ["*.json"],
            }
        }
    }
    path.write_text(json.dumps(manifest), encoding="utf-8")
    return path


def create_trs10_receipt(tmp_path: Path, key_id: str, private_key: Ed25519PrivateKey, public_key: str) -> Path:
    artifact_path = tmp_path / "artifact.txt"
    artifact_path.write_text("test artifact", encoding="utf-8")
    file_entry = {
        "path": artifact_path.name,
        "sha256": hashlib.sha256(artifact_path.read_bytes()).hexdigest(),
    }
    files = [file_entry]
    global_digest = compute_global_digest(files)
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
    receipt_path = tmp_path / "artifact.receipt.json"
    receipt_path.write_text(json.dumps(receipt), encoding="utf-8")
    return receipt_path


def create_trs0_receipt(tmp_path: Path, key_id: str, private_key: Ed25519PrivateKey, public_key: str) -> Path:
    virtual_fs = {}
    exec_flags = {}
    steps = []

    current_state = compute_state_hash(virtual_fs, exec_flags)
    content = b"hello"
    emit_step = {
        "step": 0,
        "opcode": "EMIT_BYTES",
        "args": {
            "path": "hello.txt",
            "offset": 0,
            "bytes_hex": content.hex(),
        },
        "pre_state_sha256": current_state,
    }
    virtual_fs["hello.txt"] = content
    next_state = compute_state_hash(virtual_fs, exec_flags)
    emit_step["post_state_sha256"] = next_state
    steps.append(emit_step)

    sha_step = {
        "step": 1,
        "opcode": "ASSERT_SHA256",
        "args": {
            "path": "hello.txt",
            "sha256": sha256_hex(content),
        },
        "pre_state_sha256": next_state,
        "post_state_sha256": next_state,
    }
    steps.append(sha_step)

    global_digest = compute_receipt_digest(steps)
    signature = private_key.sign(global_digest.encode("utf-8")).hex()
    receipt = {
        "version": "TRS-0",
        "steps": steps,
        "global_digest": global_digest,
        "sig_scheme": "ed25519",
        "signature": signature,
        "public_key": public_key,
        "key_id": key_id,
    }
    receipt_path = tmp_path / "hello.receipt.json"
    receipt_path.write_text(json.dumps(receipt), encoding="utf-8")
    return receipt_path


def run_cli(command: list[str], cwd: Path = PROJECT_ROOT) -> subprocess.CompletedProcess:
    env = os.environ.copy()
    existing = env.get("PYTHONPATH")
    if existing:
        env["PYTHONPATH"] = f"{PROJECT_ROOT}:{existing}"
    else:
        env["PYTHONPATH"] = str(PROJECT_ROOT)

    return subprocess.run(
        command,
        cwd=cwd,
        capture_output=True,
        text=True,
        check=False,
        env=env,
    )


class TestVerifyTRS10:
    def test_manifest_allows_signed_receipt(self, tmp_path: Path, ed25519_keypair) -> None:
        private_key, public_key = ed25519_keypair
        receipt_path = create_trs10_receipt(tmp_path, "alpha", private_key, public_key)
        manifest_path = write_trust_manifest(tmp_path / "trust_manifest.json", "alpha", public_key)

        result = run_cli([sys.executable, str(TRS10_CLI), str(receipt_path), "--trust-manifest", str(manifest_path)])

        assert result.returncode == 0, result.stderr

    def test_manifest_rejects_mismatched_public_key(self, tmp_path: Path, ed25519_keypair) -> None:
        private_key, public_key = ed25519_keypair
        receipt_path = create_trs10_receipt(tmp_path, "alpha", private_key, public_key)
        manifest_path = write_trust_manifest(tmp_path / "trust_manifest.json", "alpha", "00" * 32)

        result = run_cli([sys.executable, str(TRS10_CLI), str(receipt_path), "--trust-manifest", str(manifest_path)])

        assert result.returncode == 1
        assert "does not match manifest" in result.stderr

    def test_trusted_pubkey_overrides_manifest(self, tmp_path: Path, ed25519_keypair) -> None:
        private_key, public_key = ed25519_keypair
        receipt_path = create_trs10_receipt(tmp_path, "alpha", private_key, public_key)

        result = run_cli(
            [
                sys.executable,
                str(TRS10_CLI),
                str(receipt_path),
                "--trusted-pubkey",
                public_key,
            ]
        )

        assert result.returncode == 0, result.stderr

    def test_signed_receipt_without_trust_fails(self, tmp_path: Path, ed25519_keypair) -> None:
        private_key, public_key = ed25519_keypair
        receipt_path = create_trs10_receipt(tmp_path, "alpha", private_key, public_key)

        result = run_cli([sys.executable, str(TRS10_CLI), str(receipt_path)], cwd=tmp_path)

        assert result.returncode == 1
        assert "no trust manifest or trusted public key" in result.stderr

    def test_allow_unsigned_overrides_missing_trust(self, tmp_path: Path, ed25519_keypair) -> None:
        private_key, public_key = ed25519_keypair
        receipt_path = create_trs10_receipt(tmp_path, "alpha", private_key, public_key)

        result = run_cli([sys.executable, str(TRS10_CLI), str(receipt_path), "--allow-unsigned"], cwd=tmp_path)

        assert result.returncode == 0
        assert "Warning: no trust anchor" in result.stderr


class TestReplayCLI:
    def test_manifest_allows_replay(self, tmp_path: Path, ed25519_keypair) -> None:
        private_key, public_key = ed25519_keypair
        receipt_path = create_trs0_receipt(tmp_path, "alpha", private_key, public_key)
        manifest_path = write_trust_manifest(tmp_path / "trust_manifest.json", "alpha", public_key)

        result = run_cli(
            [
                sys.executable,
                str(REPLAY_CLI),
                str(receipt_path),
                "--trust-manifest",
                str(manifest_path),
                "--dry-run",
            ]
        )

        assert result.returncode == 0, result.stderr

    def test_manifest_rejects_mismatched_public_key(self, tmp_path: Path, ed25519_keypair) -> None:
        private_key, public_key = ed25519_keypair
        receipt_path = create_trs0_receipt(tmp_path, "alpha", private_key, public_key)
        manifest_path = write_trust_manifest(tmp_path / "trust_manifest.json", "alpha", "00" * 32)

        result = run_cli(
            [
                sys.executable,
                str(REPLAY_CLI),
                str(receipt_path),
                "--trust-manifest",
                str(manifest_path),
                "--dry-run",
            ]
        )

        assert result.returncode == 1
        assert "does not match manifest" in result.stderr

    def test_trusted_pubkey_overrides_manifest(self, tmp_path: Path, ed25519_keypair) -> None:
        private_key, public_key = ed25519_keypair
        receipt_path = create_trs0_receipt(tmp_path, "alpha", private_key, public_key)

        result = run_cli(
            [
                sys.executable,
                str(REPLAY_CLI),
                str(receipt_path),
                "--trusted-pubkey",
                public_key,
                "--dry-run",
            ],
            cwd=tmp_path,
        )

        assert result.returncode == 0, result.stderr

    def test_signed_receipt_without_trust_fails(self, tmp_path: Path, ed25519_keypair) -> None:
        private_key, public_key = ed25519_keypair
        receipt_path = create_trs0_receipt(tmp_path, "alpha", private_key, public_key)

        result = run_cli([sys.executable, str(REPLAY_CLI), str(receipt_path), "--dry-run"], cwd=tmp_path)

        assert result.returncode == 1
        assert "no trust manifest or trusted public key" in result.stderr

    def test_allow_unsigned_overrides_missing_trust(self, tmp_path: Path, ed25519_keypair) -> None:
        private_key, public_key = ed25519_keypair
        receipt_path = create_trs0_receipt(tmp_path, "alpha", private_key, public_key)

        result = run_cli(
            [
                sys.executable,
                str(REPLAY_CLI),
                str(receipt_path),
                "--allow-unsigned",
                "--dry-run",
            ],
            cwd=tmp_path,
        )

        assert result.returncode == 0
        assert "Warning: no trust anchor" in result.stderr
