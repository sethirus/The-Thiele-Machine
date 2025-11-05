from __future__ import annotations

from pathlib import Path

from experiments.turbulence import PROTOCOLS, run_dataset
from verifier.check_turbulence import verify_turbulence

DATA_DIR = Path(__file__).resolve().parents[2] / "data" / "turbulence"


def _prepare_dataset(tmp_path: Path) -> Path:
    dataset_dir = tmp_path / "dataset"
    dataset_dir.mkdir()
    sample_path = DATA_DIR / "sample_jhtdb_samples.json"
    (dataset_dir / "jhtdb_samples.json").write_text(sample_path.read_text(encoding="utf-8"))
    return dataset_dir


def test_run_dataset_emits_ledgers(tmp_path: Path) -> None:
    dataset_dir = _prepare_dataset(tmp_path)
    output_dir = tmp_path / "artefacts"
    summaries = run_dataset(dataset_dir, output_dir, seed=7)

    for protocol in PROTOCOLS:
        ledger_path = output_dir / "ledgers" / f"{protocol}.jsonl"
        assert ledger_path.exists()
        assert protocol in summaries

    metadata_path = output_dir / "turbulence_metadata.json"
    assert metadata_path.exists()
    protocol_path = output_dir / "protocol.json"
    assert protocol_path.exists()


def test_verify_turbulence(tmp_path: Path) -> None:
    dataset_dir = _prepare_dataset(tmp_path)
    output_dir = tmp_path / "artefacts"
    run_dataset(dataset_dir, output_dir, seed=11)

    out_path, payload = verify_turbulence(output_dir)
    assert out_path.exists()
    assert payload["status"] is True
    assert payload["protocols"]["blind"]["delta_aic"] >= 10.0
    assert payload.get("time_count") == 4
    assert payload.get("point_count") == 4
    assert payload.get("skipped_protocols") == []


def test_verify_turbulence_threshold_failure(tmp_path: Path) -> None:
    dataset_dir = _prepare_dataset(tmp_path)
    output_dir = tmp_path / "artefacts"
    run_dataset(dataset_dir, output_dir, seed=5)

    _, baseline = verify_turbulence(output_dir)
    delta_aic = baseline["protocols"]["blind"]["delta_aic"]

    _, payload = verify_turbulence(output_dir, delta_aic_threshold=delta_aic + 5.0)
    assert payload["status"] is False
