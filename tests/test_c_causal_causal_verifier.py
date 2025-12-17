"""C-CAUSAL falsifier harness: stronger causal claims need assumptions or interventions."""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from verifier.c_causal import CausalVerificationError, verify_causal
from verifier.receipt_protocol import ed25519_keypair, write_trs10_receipt, write_trust_manifest


def _write_obs(path: Path, n: int) -> None:
    with path.open("w", encoding="utf-8", newline="") as handle:
        handle.write("idx,x,y\n")
        for i in range(n):
            handle.write(f"{i},{i%2},{i%2}\n")


def test_c_causal_forge_rejected(tmp_path: Path) -> None:
    sk, pk_hex = ed25519_keypair()
    trust = tmp_path / "trust_manifest.json"
    write_trust_manifest(trust, key_id="k", public_key_hex=pk_hex)

    run_dir = tmp_path / "run"
    run_dir.mkdir(parents=True, exist_ok=True)

    (run_dir / "claim.json").write_text(json.dumps({"claim_type": "unique_dag", "n_obs": 10}) + "\n", encoding="utf-8")
    _write_obs(run_dir / "observational.csv", 10)
    (run_dir / "assumptions.json").write_text(
        json.dumps({"assumptions": ["no_hidden_confounders"], "disclosure_bits": 8192}) + "\n",
        encoding="utf-8",
    )

    write_trs10_receipt(
        receipt_path=run_dir / "causal.receipt.json",
        base_dir=run_dir,
        files=[run_dir / "claim.json", run_dir / "observational.csv", run_dir / "assumptions.json"],
        private_key=sk,
        public_key_hex=pk_hex,
        key_id="k",
    )

    # Tamper assumptions after signing.
    (run_dir / "assumptions.json").write_text(
        json.dumps({"assumptions": ["no_hidden_confounders"], "disclosure_bits": 0}) + "\n",
        encoding="utf-8",
    )

    with pytest.raises(CausalVerificationError, match="Hash mismatch"):
        verify_causal(run_dir, trust)


def test_c_causal_underpay_rejected(tmp_path: Path) -> None:
    sk, pk_hex = ed25519_keypair()
    trust = tmp_path / "trust_manifest.json"
    write_trust_manifest(trust, key_id="k", public_key_hex=pk_hex)

    run_dir = tmp_path / "run"
    run_dir.mkdir(parents=True, exist_ok=True)

    (run_dir / "claim.json").write_text(json.dumps({"claim_type": "unique_dag", "n_obs": 10}) + "\n", encoding="utf-8")
    _write_obs(run_dir / "observational.csv", 10)
    (run_dir / "assumptions.json").write_text(
        json.dumps({"assumptions": ["no_hidden_confounders"], "disclosure_bits": 1}) + "\n",
        encoding="utf-8",
    )

    write_trs10_receipt(
        receipt_path=run_dir / "causal.receipt.json",
        base_dir=run_dir,
        files=[run_dir / "claim.json", run_dir / "observational.csv", run_dir / "assumptions.json"],
        private_key=sk,
        public_key_hex=pk_hex,
        key_id="k",
    )

    with pytest.raises(CausalVerificationError, match="Insufficient disclosure_bits"):
        verify_causal(run_dir, trust)


def test_c_causal_bypass_rejected(tmp_path: Path) -> None:
    sk, pk_hex = ed25519_keypair()
    trust = tmp_path / "trust_manifest.json"
    write_trust_manifest(trust, key_id="k", public_key_hex=pk_hex)

    run_dir = tmp_path / "run"
    run_dir.mkdir(parents=True, exist_ok=True)

    (run_dir / "claim.json").write_text(json.dumps({"claim_type": "unique_dag", "n_obs": 10}) + "\n", encoding="utf-8")
    _write_obs(run_dir / "observational.csv", 10)

    # Receipt omits assumptions and interventions.
    write_trs10_receipt(
        receipt_path=run_dir / "causal.receipt.json",
        base_dir=run_dir,
        files=[run_dir / "claim.json", run_dir / "observational.csv"],
        private_key=sk,
        public_key_hex=pk_hex,
        key_id="k",
    )

    with pytest.raises(CausalVerificationError, match="Receipt missing required"):
        verify_causal(run_dir, trust)
