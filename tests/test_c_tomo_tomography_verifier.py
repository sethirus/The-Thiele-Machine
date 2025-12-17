"""C-TOMO falsifier harness: receipt-defined tomography/estimation gate."""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from verifier.c_tomography import TomographyVerificationError, verify_tomography
from verifier.receipt_protocol import ed25519_keypair, write_trs10_receipt, write_trust_manifest


def _write_trials(path: Path, n: int) -> None:
    with path.open("w", encoding="utf-8", newline="") as handle:
        handle.write("trial_id,value\n")
        for i in range(n):
            handle.write(f"{i},0\n")


def test_c_tomo_forge_rejected(tmp_path: Path) -> None:
    sk, pk_hex = ed25519_keypair()
    trust = tmp_path / "trust_manifest.json"
    write_trust_manifest(trust, key_id="k", public_key_hex=pk_hex)

    run_dir = tmp_path / "run"
    run_dir.mkdir(parents=True, exist_ok=True)

    epsilon = 0.25
    n_trials = 256

    (run_dir / "claim.json").write_text(json.dumps({"epsilon": epsilon, "n_trials": n_trials}) + "\n", encoding="utf-8")
    _write_trials(run_dir / "trials.csv", n_trials)

    write_trs10_receipt(
        receipt_path=run_dir / "tomography.receipt.json",
        base_dir=run_dir,
        files=[run_dir / "claim.json", run_dir / "trials.csv"],
        private_key=sk,
        public_key_hex=pk_hex,
        key_id="k",
    )

    # Tamper with trials after signing.
    _write_trials(run_dir / "trials.csv", 1)

    with pytest.raises(TomographyVerificationError, match="Hash mismatch"):
        verify_tomography(run_dir, trust)


def test_c_tomo_underpay_rejected(tmp_path: Path) -> None:
    sk, pk_hex = ed25519_keypair()
    trust = tmp_path / "trust_manifest.json"
    write_trust_manifest(trust, key_id="k", public_key_hex=pk_hex)

    run_dir = tmp_path / "run"
    run_dir.mkdir(parents=True, exist_ok=True)

    epsilon = 0.25
    n_trials = 1

    (run_dir / "claim.json").write_text(json.dumps({"epsilon": epsilon, "n_trials": n_trials}) + "\n", encoding="utf-8")
    _write_trials(run_dir / "trials.csv", n_trials)

    write_trs10_receipt(
        receipt_path=run_dir / "tomography.receipt.json",
        base_dir=run_dir,
        files=[run_dir / "claim.json", run_dir / "trials.csv"],
        private_key=sk,
        public_key_hex=pk_hex,
        key_id="k",
    )

    with pytest.raises(TomographyVerificationError, match="Underpaid"):
        verify_tomography(run_dir, trust)


def test_c_tomo_bypass_rejected(tmp_path: Path) -> None:
    sk, pk_hex = ed25519_keypair()
    trust = tmp_path / "trust_manifest.json"
    write_trust_manifest(trust, key_id="k", public_key_hex=pk_hex)

    run_dir = tmp_path / "run"
    run_dir.mkdir(parents=True, exist_ok=True)

    epsilon = 0.25
    n_trials = 256

    (run_dir / "claim.json").write_text(json.dumps({"epsilon": epsilon, "n_trials": n_trials}) + "\n", encoding="utf-8")
    _write_trials(run_dir / "trials.csv", n_trials)

    # Receipt omits trials.csv.
    write_trs10_receipt(
        receipt_path=run_dir / "tomography.receipt.json",
        base_dir=run_dir,
        files=[run_dir / "claim.json"],
        private_key=sk,
        public_key_hex=pk_hex,
        key_id="k",
    )

    with pytest.raises(TomographyVerificationError, match="Receipt missing required"):
        verify_tomography(run_dir, trust)
