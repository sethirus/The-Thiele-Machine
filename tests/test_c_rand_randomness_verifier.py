"""C-RAND falsifier harness: receipt-defined certified randomness gate."""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from verifier.c_randomness import RandomnessVerificationError, verify_randomness
from verifier.receipt_protocol import ed25519_keypair, write_trs10_receipt, write_trust_manifest


def _make_run_dir(tmp_path: Path, *, disclosure_bits: int = 2000) -> tuple[Path, Path]:
    sk, pk_hex = ed25519_keypair()
    trust = tmp_path / "trust_manifest.json"
    write_trust_manifest(trust, key_id="k", public_key_hex=pk_hex)

    run_dir = tmp_path / "run"
    run_dir.mkdir(parents=True, exist_ok=True)

    (run_dir / "randomness.bin").write_bytes(b"\x00" * 256)
    (run_dir / "claim.json").write_text(
        json.dumps({"n_bits": 1024, "min_entropy_per_bit": 0.001}, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    (run_dir / "nonlocality.json").write_text(
        json.dumps({"disclosure_bits": disclosure_bits}, sort_keys=True) + "\n",
        encoding="utf-8",
    )

    write_trs10_receipt(
        receipt_path=run_dir / "randomness.receipt.json",
        base_dir=run_dir,
        files=[run_dir / "claim.json", run_dir / "randomness.bin", run_dir / "nonlocality.json"],
        private_key=sk,
        public_key_hex=pk_hex,
        key_id="k",
    )

    return run_dir, trust


def test_c_rand_forge_rejected(tmp_path: Path) -> None:
    run_dir, trust = _make_run_dir(tmp_path)

    # Tamper with a receipted file after signing.
    (run_dir / "randomness.bin").write_bytes(b"\x01" * 256)

    with pytest.raises(RandomnessVerificationError, match="Hash mismatch"):
        verify_randomness(run_dir, trust)


def test_c_rand_underpay_rejected(tmp_path: Path) -> None:
    run_dir, trust = _make_run_dir(tmp_path, disclosure_bits=1)

    with pytest.raises(RandomnessVerificationError, match="Insufficient disclosure_bits"):
        verify_randomness(run_dir, trust)


def test_c_rand_bypass_rejected(tmp_path: Path) -> None:
    sk, pk_hex = ed25519_keypair()
    trust = tmp_path / "trust_manifest.json"
    write_trust_manifest(trust, key_id="k", public_key_hex=pk_hex)

    run_dir = tmp_path / "run"
    run_dir.mkdir(parents=True, exist_ok=True)

    (run_dir / "randomness.bin").write_bytes(b"\x00" * 256)
    (run_dir / "claim.json").write_text(
        json.dumps({"n_bits": 1024, "min_entropy_per_bit": 0.001}, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    (run_dir / "nonlocality.json").write_text(
        json.dumps({"disclosure_bits": 2000}, sort_keys=True) + "\n",
        encoding="utf-8",
    )

    # Receipt omits randomness.bin (attempt to route around the receipt channel).
    write_trs10_receipt(
        receipt_path=run_dir / "randomness.receipt.json",
        base_dir=run_dir,
        files=[run_dir / "claim.json", run_dir / "nonlocality.json"],
        private_key=sk,
        public_key_hex=pk_hex,
        key_id="k",
    )

    with pytest.raises(RandomnessVerificationError, match="Receipt missing required"):
        verify_randomness(run_dir, trust)
