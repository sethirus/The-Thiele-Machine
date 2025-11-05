from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest
from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey

from experiments.red_team import structure_ablation
from experiments.run_cross_domain import main as cross_domain_main
from experiments.run_cwd import main as cwd_main
from experiments.run_einstein import main as einstein_main
from experiments.run_entropy import main as entropy_main
from experiments.run_landauer import main as landauer_main
from tools.proofpack_bundler import bundle_proofpack
from tools.receipts import ReceiptValidator


def _build_phase_runs(base_dir: Path) -> None:
    landauer_dir = base_dir / "landauer"
    landauer_main(
        [
            "--output-dir",
            str(landauer_dir),
            "--seeds",
            "0",
            "--temps",
            "1.0",
            "--trials-per-condition",
            "1",
            "--steps",
            "12",
        ]
    )

    einstein_dir = base_dir / "einstein"
    einstein_main(
        [
            "--output-dir",
            str(einstein_dir),
            "--seeds",
            "0",
            "--temps",
            "1.0",
            "--trials-per-condition",
            "1",
            "--steps",
            "24",
        ]
    )

    entropy_dir = base_dir / "entropy"
    entropy_main(
        [
            "--output-dir",
            str(entropy_dir),
            "--seeds",
            "0",
            "--temps",
            "1.0",
            "--trials-per-condition",
            "1",
            "--steps",
            "32",
        ]
    )

    cwd_root = base_dir / "cwd"
    for protocol in ("sighted", "blind", "destroyed"):
        cwd_main(
            [
                "--output-dir",
                str(cwd_root / protocol),
                "--protocol",
                protocol,
                "--seeds",
                "1",
                "--temps",
                "0.9",
                "--trials-per-condition",
                "1",
                "--modules",
                "3",
                "--steps-per-module",
                "4",
            ]
        )

    cross_root = base_dir / "cross_domain"
    cross_common = [
        "--seeds",
        "0",
        "1",
        "--trials-per-condition",
        "3",
        "--modules",
        "5",
        "--mu-base",
        "0.24",
        "--mu-jitter",
        "0.03",
        "--runtime-base",
        "1.1",
        "--runtime-scale",
        "0.75",
    ]
    for protocol in ("sighted", "blind", "destroyed"):
        cross_domain_main(
            [
                "--output-dir",
                str(cross_root / protocol),
                "--protocol",
                protocol,
                *cross_common,
            ]
        )


def _write_key(path: Path) -> None:
    private_key = Ed25519PrivateKey.generate()
    path.write_bytes(
        private_key.private_bytes(
            encoding=serialization.Encoding.Raw,
            format=serialization.PrivateFormat.Raw,
            encryption_algorithm=serialization.NoEncryption(),
        )
    )


def test_bundle_proofpack_generates_archive(tmp_path: Path) -> None:
    root = tmp_path / "artifacts" / "experiments" / "runA"
    run_dir = root / "proofpack"
    run_dir.mkdir(parents=True, exist_ok=True)
    _build_phase_runs(run_dir)

    key_path = tmp_path / "key.bin"
    _write_key(key_path)

    bundle_dir = root / "bundle"
    result = bundle_proofpack(run_dir, bundle_dir, signing_key_path=key_path, run_tag="runA")

    manifest_path = result.manifest_path
    assert manifest_path.exists()
    manifest = json.loads(manifest_path.read_text())
    assert manifest["run_tag"] == "runA"
    assert manifest["metadata"]["attachment_count"] == len(result.attachments)

    summary = json.loads(result.summary_path.read_text())
    assert summary["status"] is True

    receipt_data = json.loads(result.receipt_path.read_text())
    validator = ReceiptValidator(require_signature=True)
    mu_total = validator.validate(receipt_data)
    assert mu_total == pytest.approx(0.0, abs=1e-12)

    copied_paths = {path.relative_to(bundle_dir).as_posix() for path in result.attachments}
    assert "artefacts/verifier/proofpack_verifier.json" in copied_paths
    if any("plots/" in path for path in copied_paths):
        assert any(path.endswith("plots/sighted_mu_vs_entropy.svg") for path in copied_paths)
    assert result.human_summary_path.exists()
    summary_text = result.human_summary_path.read_text(encoding="utf-8")
    assert "Thiele proofpack summary" in summary_text
    assert "runA" in summary_text


def test_proofpack_bundler_cli(tmp_path: Path) -> None:
    root = tmp_path / "artifacts" / "experiments" / "run_cli"
    run_dir = root / "proofpack"
    run_dir.mkdir(parents=True, exist_ok=True)
    _build_phase_runs(run_dir)

    key_path = tmp_path / "key.bin"
    _write_key(key_path)

    bundle_dir = root / "bundle"
    completed = subprocess.run(
        [
            sys.executable,
            "-m",
            "tools.proofpack_bundler",
            str(run_dir),
            "--output-dir",
            str(bundle_dir),
            "--signing-key",
            str(key_path),
            "--note",
            "cli",
            "--created-at",
            "2025-01-01T00:00:00Z",
            "--run-tag",
            "run_cli",
        ],
        capture_output=True,
        text=True,
        check=True,
    )
    lines = completed.stdout.strip().splitlines()
    assert lines[0].startswith("BUNDLE_OK")
    assert any(line.startswith("SUMMARY_MD:") for line in lines)
    assert (bundle_dir / "manifest.json").exists()
    protocol = json.loads((bundle_dir / "protocol.json").read_text())
    assert "cli" in protocol["notes"]


def test_bundle_rejects_red_team_failure(tmp_path: Path) -> None:
    root = tmp_path / "artifacts" / "experiments" / "run_fail"
    run_dir = root / "proofpack"
    run_dir.mkdir(parents=True, exist_ok=True)
    _build_phase_runs(run_dir)

    # Mutate the sighted cross-domain run so verification fails.
    structure_ablation(run_dir / "cross_domain" / "sighted", run_dir / "cross_domain" / "sighted")

    key_path = tmp_path / "key.bin"
    _write_key(key_path)

    with pytest.raises(RuntimeError, match="Proofpack verification failed"):
        bundle_proofpack(run_dir, root / "bundle", signing_key_path=key_path, run_tag="run_fail")


def test_bundle_byte_stability(tmp_path: Path) -> None:
    root = tmp_path / "artifacts" / "experiments" / "run_bytes"
    run_dir = root / "proofpack"
    run_dir.mkdir(parents=True, exist_ok=True)
    _build_phase_runs(run_dir)

    key_path = tmp_path / "key.bin"
    _write_key(key_path)

    bundle_dir = root / "bundle"
    bundle_proofpack(run_dir, bundle_dir, signing_key_path=key_path, created_at="2025-01-01T00:00:00Z")

    first_manifest = (bundle_dir / "manifest.json").read_bytes()
    first_receipt = (bundle_dir / "receipt.json").read_bytes()

    bundle_proofpack(run_dir, bundle_dir, signing_key_path=key_path, created_at="2025-01-01T00:00:00Z")

    second_manifest = (bundle_dir / "manifest.json").read_bytes()
    second_receipt = (bundle_dir / "receipt.json").read_bytes()

    assert second_manifest == first_manifest
    assert second_receipt == first_receipt


def test_bundle_requires_canonical_output(tmp_path: Path) -> None:
    run_dir = tmp_path / "artifacts" / "experiments" / "run_noncanonical" / "proofpack"
    run_dir.mkdir(parents=True, exist_ok=True)

    key_path = tmp_path / "key.bin"
    _write_key(key_path)

    with pytest.raises(ValueError):
        bundle_proofpack(run_dir, tmp_path / "bundle", signing_key_path=key_path)

