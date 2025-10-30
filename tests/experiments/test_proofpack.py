from __future__ import annotations

import json
from pathlib import Path

import pytest
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey

from experiments import proofpack
from tools.receipts import ReceiptValidator


def _write_temp_files(tmp_path: Path) -> list[Path]:
    files = []
    files.append(tmp_path / "protocol.json")
    files[-1].write_text("{}\n", encoding="utf-8")
    files.append(tmp_path / "verifier" / "proofpack_verifier.json")
    files[-1].parent.mkdir(parents=True, exist_ok=True)
    files[-1].write_text(json.dumps({"status": True}) + "\n", encoding="utf-8")
    return files


def test_manifest_and_receipt_round_trip(tmp_path: Path) -> None:
    attachments = _write_temp_files(tmp_path)
    entries = proofpack.collect_manifest_entries(tmp_path, attachments)
    manifest_path = proofpack.write_manifest(
        tmp_path,
        entries,
        run_tag="unit-test",
        metadata={"phase": "archive"},
    )

    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    assert manifest["run_tag"] == "unit-test"
    assert manifest["metadata"]["phase"] == "archive"
    assert len(manifest["entries"]) == len(entries)

    signer = proofpack.ReceiptSigner(private_key=Ed25519PrivateKey.generate())
    receipt_path = tmp_path / "receipt.json"
    proofpack.write_receipt(
        entries,
        signer,
        manifest_digest=manifest["manifest_digest_sha256"],
        run_tag="unit-test",
        out_path=receipt_path,
    )

    validator = ReceiptValidator(require_signature=True)
    receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
    total_mu = validator.validate(receipt)
    assert total_mu == pytest.approx(0.0, abs=1e-12)


def test_summary_payload_from_verifier(tmp_path: Path) -> None:
    aggregated = {
        "status": True,
        "epsilon": 0.05,
        "delta": 0.05,
        "phases": {
            "landauer": {
                "status": True,
                "runs": [
                    {"run_dir": "landauer/run0", "status": True},
                    {"run_dir": "landauer/run1", "status": False, "error": "mu_mismatch"},
                ],
            },
            "entropy": {"status": True, "runs": []},
        },
    }

    payload = proofpack.build_summary_payload(aggregated)
    assert payload["status"] is True
    assert payload["parameters"]["epsilon"] == 0.05
    assert payload["phases"]["landauer"]["run_count"] == 2
    assert payload["phases"]["landauer"]["failing_runs"] == [
        {"run_dir": "landauer/run1", "error": "mu_mismatch"}
    ]

    summary_path = tmp_path / "summary.json"
    proofpack.write_summary(payload, summary_path)
    stored = json.loads(summary_path.read_text(encoding="utf-8"))
    assert stored == payload


def test_protocol_document_notes(tmp_path: Path) -> None:
    protocol_path = tmp_path / "protocol.json"
    proofpack.write_protocol_document(
        {"epsilon": 0.05, "delta": 0.05},
        protocol_path,
        notes=["deterministic seeds", "no hidden state"],
    )
    data = json.loads(protocol_path.read_text(encoding="utf-8"))
    assert data["thresholds"]["epsilon"] == 0.05
    assert "deterministic seeds" in data["notes"]


def test_human_summary_round_trip(tmp_path: Path) -> None:
    aggregated = {
        "status": True,
        "parameters": {"epsilon": 0.05, "delta": 0.05},
        "phases": {
            "landauer": {
                "status": True,
                "runs": [
                    {
                        "protocol": "sighted",
                        "status": True,
                        "trial_count": 3,
                        "verifier_json": "verifier/landauer_0.json",
                        "highlights": {"max_bits_gap": 0.01, "tolerance_pass_rate": 1.0},
                    }
                ],
                "highlights": {"max_bits_gap": 0.01},
            },
            "cwd": {
                "status": True,
                "protocol_runs": {"sighted": "cwd/sighted"},
                "highlights": {"min_penalty_margin_bits": 0.12},
            },
        },
        "public_data": {
            "status": True,
            "datasets": [
                {
                    "dataset": "osf/sample",
                    "dataset_dir": "public_data/osf/sample",
                    "status": True,
                    "verifier_json": "verifier/public_spt_0.json",
                    "highlights": {"oos_error": 0.05, "blind_delta_aic": 12.0},
                }
            ],
            "highlights": {
                "dataset_count": 1,
                "max_oos_error": 0.05,
                "blind_min_delta_aic": 12.0,
            },
        },
        "turbulence": {
            "status": True,
            "datasets": [
                {
                    "dataset": "jhtdb/sample",
                    "dataset_dir": "turbulence/sample",
                    "status": True,
                    "verifier_json": "verifier/turbulence_0.json",
                    "highlights": {
                        "sighted_rho": 0.95,
                        "blind_delta_aic": 11.5,
                        "rho_drop": 0.35,
                    },
                }
            ],
            "highlights": {
                "dataset_count": 1,
                "pass_rate": 1.0,
                "min_delta_aic": 11.5,
                "mean_rho_drop": 0.35,
            },
        },
    }
    manifest = {
        "run_tag": "unit-test",
        "created_at": "2025-01-01T00:00:00Z",
        "entries": [
            {"path": "summary.json", "sha256": "00", "bytes": 2},
            {"path": "protocol.json", "sha256": "11", "bytes": 2},
        ],
    }

    summary_text = proofpack.render_human_summary(aggregated, manifest, protocol_notes=["note"])
    assert "Thiele proofpack summary" in summary_text
    assert "unit-test" in summary_text
    assert "note" in summary_text
    assert "max |ΔW/(kT ln 2) − Σμ|" in summary_text
    assert "Public data" in summary_text
    assert "OOS error" in summary_text
    assert "Turbulence data" in summary_text
    assert "ρ drop" in summary_text

    summary_path = tmp_path / "summary.md"
    proofpack.write_human_summary(summary_text, summary_path)
    stored = summary_path.read_text(encoding="utf-8")
    assert stored.endswith("\n")
    assert "PASS" in stored

