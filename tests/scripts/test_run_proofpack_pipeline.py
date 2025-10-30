import json
from pathlib import Path

from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
import yaml

from scripts.run_proofpack_pipeline import _load_profile_config, run_pipeline


def _write_key(path: Path) -> None:
    private_key = Ed25519PrivateKey.generate()
    path.write_bytes(
        private_key.private_bytes(
            encoding=serialization.Encoding.Raw,
            format=serialization.PrivateFormat.Raw,
            encryption_algorithm=serialization.NoEncryption(),
        )
    )


def test_run_pipeline_quick(tmp_path: Path) -> None:
    root = tmp_path / "artifacts" / "experiments"
    key_path = tmp_path / "key.bin"
    _write_key(key_path)

    result = run_pipeline(
        output_root=root,
        signing_key=key_path,
        run_tag="pytest-run",
        profile="quick",
        notes=["pytest"],
        created_at="2025-01-01T00:00:00Z",
    )

    bundle_dir = result.bundle_dir
    manifest_path = bundle_dir / "manifest.json"
    summary_json = bundle_dir / "summary.json"
    summary_md = bundle_dir / "summary.md"

    assert manifest_path.exists()
    assert summary_json.exists()
    assert summary_md.exists()

    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    assert manifest["run_tag"] == "pytest-run"

    summary_markdown = summary_md.read_text(encoding="utf-8")
    assert "Thiele proofpack summary" in summary_markdown
    assert "pytest" in summary_markdown
    assert "Highlight" in summary_markdown

    verifier_payload = bundle_dir / "artefacts" / "verifier" / "proofpack_verifier.json"
    assert verifier_payload.exists()

    assert result.bundle_result.aggregated_payload.get("status") is True


def test_run_pipeline_with_public_data(tmp_path: Path) -> None:
    root = tmp_path / "artifacts" / "experiments"
    key_path = tmp_path / "key.bin"
    _write_key(key_path)

    public_root = tmp_path / "public_data"
    dataset_dir = public_root / "osf" / "calibration"
    (dataset_dir / "raw").mkdir(parents=True)
    sample_dir = Path(__file__).resolve().parents[1] / "data" / "public"
    (dataset_dir / "raw" / "tracks.csv").write_text((sample_dir / "sample_tracks.csv").read_text())
    (dataset_dir / "anchors.json").write_text((sample_dir / "sample_anchors.json").read_text())

    turbulence_dir = public_root / "jhtdb" / "sample"
    turbulence_dir.mkdir(parents=True)
    turbulence_sample = (
        Path(__file__).resolve().parents[1]
        / "data"
        / "turbulence"
        / "sample_jhtdb_samples.json"
    )
    (turbulence_dir / "jhtdb_samples.json").write_text(turbulence_sample.read_text())

    result = run_pipeline(
        output_root=root,
        signing_key=key_path,
        run_tag="pytest-public",
        profile="quick",
        public_data_root=public_root,
        public_data_seed=0,
        turbulence_protocols=("blind",),
        turbulence_seed=3,
        turbulence_datasets=("sample",),
    )

    public_payload = result.bundle_result.aggregated_payload.get("public_data", {})
    assert public_payload.get("status") is True
    datasets = public_payload.get("datasets") or []
    assert len(datasets) == 1
    summary_markdown = (result.bundle_result.human_summary_path).read_text(encoding="utf-8")
    assert "Public data" in summary_markdown
    assert "Turbulence data" in summary_markdown

    proofpack_dataset_dir = result.proofpack_dir / "public_data" / "osf" / dataset_dir.name
    assert (proofpack_dataset_dir / "public_spt_metadata.json").exists()
    verifier_rel = datasets[0].get("verifier_json")
    assert verifier_rel
    assert (result.proofpack_dir / verifier_rel).exists()

    turbulence_dataset_dir = result.proofpack_dir / "turbulence" / turbulence_dir.relative_to(public_root)
    assert (turbulence_dataset_dir / "turbulence_metadata.json").exists()
    turbulence_payload = result.bundle_result.aggregated_payload.get("turbulence", {})
    assert turbulence_payload.get("status") is True
    assert len(turbulence_payload.get("datasets") or []) == 1
    ledgers_root = turbulence_dataset_dir / "ledgers"
    assert (ledgers_root / "blind.jsonl").exists()
    assert not (ledgers_root / "sighted.jsonl").exists()
    assert not (ledgers_root / "destroyed.jsonl").exists()
    dataset_highlights = turbulence_payload["datasets"][0]["highlights"]
    assert dataset_highlights.get("skipped_protocols") == ["sighted", "destroyed"]


def test_run_pipeline_with_profile_config(tmp_path: Path) -> None:
    root = tmp_path / "artifacts" / "experiments"
    key_path = tmp_path / "key.bin"
    _write_key(key_path)

    profile_file = tmp_path / "profiles.yaml"
    profile_payload = {
        "custom": {
            "landauer": [
                "--seeds",
                "0",
                "--temps",
                "0.5",
                "1.0",
                "--trials-per-condition",
                "3",
                "--steps",
                "18",
            ],
            "einstein": [
                "--seeds",
                "0",
                "--temps",
                "0.75",
                "1.25",
                "--trials-per-condition",
                "2",
                "--steps",
                "24",
                "--dt",
                "0.5",
                "--mobility",
                "0.4",
                "--force",
                "0.6",
            ],
            "entropy": [
                "--seeds",
                "0",
                "--temps",
                "0.75",
                "1.25",
                "--trials-per-condition",
                "2",
                "--steps",
                "24",
                "--dt",
                "0.5",
                "--mobility",
                "0.4",
                "--force",
                "0.6",
                "--entropy-smoothing",
                "0.04",
            ],
            "cwd": [
                "--seeds",
                "0",
                "--temps",
                "0.85",
                "--trials-per-condition",
                "1",
                "--modules",
                "3",
                "--steps-per-module",
                "4",
                "--mu-base",
                "0.18",
                "--mu-jitter",
                "0.02",
                "--penalty-scale",
                "1.5",
            ],
            "cross_domain": [
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
            ],
        }
    }
    profile_file.write_text(yaml.safe_dump(profile_payload))

    loaded_profiles = _load_profile_config(profile_file)

    result = run_pipeline(
        output_root=root,
        signing_key=key_path,
        run_tag="pytest-profile",
        profile="custom",
        profile_arguments=loaded_profiles,
    )

    landauer_metadata = json.loads(
        (result.proofpack_dir / "landauer" / "sighted" / "landauer_metadata.json").read_text(
            encoding="utf-8"
        )
    )
    assert landauer_metadata.get("num_trials") == 6


def test_run_pipeline_enforces_turbulence_allowlist(tmp_path: Path) -> None:
    root = tmp_path / "artifacts" / "experiments"
    key_path = tmp_path / "key.bin"
    _write_key(key_path)

    mirror_root = tmp_path / "mirror"
    allowed_slugs = ("isotropic1024_8pt", "isotropic1024_12pt")
    sample_json = (
        Path(__file__).resolve().parents[1]
        / "data"
        / "turbulence"
        / "sample_jhtdb_samples.json"
    ).read_text(encoding="utf-8")

    for slug in allowed_slugs + ("other_fixture",):
        dataset_dir = mirror_root / "jhtdb" / slug
        dataset_dir.mkdir(parents=True, exist_ok=True)
        (dataset_dir / "jhtdb_samples.json").write_text(sample_json, encoding="utf-8")

    result = run_pipeline(
        output_root=root,
        signing_key=key_path,
        run_tag="allowlist",
        profile="quick",
        public_data_root=mirror_root,
    )

    turbulence_root = result.proofpack_dir / "turbulence"
    discovered = {path.parent.name for path in turbulence_root.rglob("turbulence_metadata.json")}
    assert set(allowed_slugs).issubset(discovered)
    assert "other_fixture" not in discovered
