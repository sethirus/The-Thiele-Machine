"""C-ENTROPY falsifier harness: coarse-graining must be declared and paid."""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from verifier.c_entropy2 import EntropyVerificationError, verify_entropy2
from verifier.receipt_protocol import ed25519_keypair, write_trs10_receipt, write_trust_manifest


def _write_samples(path: Path, n: int) -> None:
    with path.open("w", encoding="utf-8", newline="") as handle:
        handle.write("idx,symbol\n")
        for i in range(n):
            handle.write(f"{i},{i%2}\n")


def test_c_entropy_forge_rejected(tmp_path: Path) -> None:
    sk, pk_hex = ed25519_keypair()
    trust = tmp_path / "trust_manifest.json"
    write_trust_manifest(trust, key_id="k", public_key_hex=pk_hex)

    run_dir = tmp_path / "run"
    run_dir.mkdir(parents=True, exist_ok=True)

    (run_dir / "claim.json").write_text(json.dumps({"h_lower_bound_bits": 0.5, "n_samples": 32}) + "\n", encoding="utf-8")
    _write_samples(run_dir / "samples.csv", 32)
    (run_dir / "coarse_graining.json").write_text(
        json.dumps({"partition_id": "p", "disclosure_bits": 512}) + "\n",
        encoding="utf-8",
    )

    write_trs10_receipt(
        receipt_path=run_dir / "entropy.receipt.json",
        base_dir=run_dir,
        files=[run_dir / "claim.json", run_dir / "samples.csv", run_dir / "coarse_graining.json"],
        private_key=sk,
        public_key_hex=pk_hex,
        key_id="k",
    )

    # Tamper coarse-graining after signing.
    (run_dir / "coarse_graining.json").write_text(json.dumps({"partition_id": "p", "disclosure_bits": 0}) + "\n", encoding="utf-8")

    with pytest.raises(EntropyVerificationError, match="Hash mismatch"):
        verify_entropy2(run_dir, trust)


def test_c_entropy_underpay_rejected(tmp_path: Path) -> None:
    sk, pk_hex = ed25519_keypair()
    trust = tmp_path / "trust_manifest.json"
    write_trust_manifest(trust, key_id="k", public_key_hex=pk_hex)

    run_dir = tmp_path / "run"
    run_dir.mkdir(parents=True, exist_ok=True)

    (run_dir / "claim.json").write_text(json.dumps({"h_lower_bound_bits": 0.5, "n_samples": 32}) + "\n", encoding="utf-8")
    _write_samples(run_dir / "samples.csv", 32)
    (run_dir / "coarse_graining.json").write_text(
        json.dumps({"partition_id": "p", "disclosure_bits": 1}) + "\n",
        encoding="utf-8",
    )

    write_trs10_receipt(
        receipt_path=run_dir / "entropy.receipt.json",
        base_dir=run_dir,
        files=[run_dir / "claim.json", run_dir / "samples.csv", run_dir / "coarse_graining.json"],
        private_key=sk,
        public_key_hex=pk_hex,
        key_id="k",
    )

    with pytest.raises(EntropyVerificationError, match="Insufficient disclosure_bits"):
        verify_entropy2(run_dir, trust)


def test_c_entropy_bypass_rejected(tmp_path: Path) -> None:
    sk, pk_hex = ed25519_keypair()
    trust = tmp_path / "trust_manifest.json"
    write_trust_manifest(trust, key_id="k", public_key_hex=pk_hex)

    run_dir = tmp_path / "run"
    run_dir.mkdir(parents=True, exist_ok=True)

    (run_dir / "claim.json").write_text(json.dumps({"h_lower_bound_bits": 0.0, "n_samples": 32}) + "\n", encoding="utf-8")
    _write_samples(run_dir / "samples.csv", 32)
    (run_dir / "coarse_graining.json").write_text(
        json.dumps({"partition_id": "p", "disclosure_bits": 0}) + "\n",
        encoding="utf-8",
    )

    # Receipt omits coarse_graining.json.
    write_trs10_receipt(
        receipt_path=run_dir / "entropy.receipt.json",
        base_dir=run_dir,
        files=[run_dir / "claim.json", run_dir / "samples.csv"],
        private_key=sk,
        public_key_hex=pk_hex,
        key_id="k",
    )

    with pytest.raises(EntropyVerificationError, match="Receipt missing required"):
        verify_entropy2(run_dir, trust)
