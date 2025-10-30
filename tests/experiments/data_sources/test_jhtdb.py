from __future__ import annotations

import io
import json
from pathlib import Path
from typing import Any
from unittest import mock

import pytest

from experiments.data_sources import jhtdb


class _FakeResponse:
    def __init__(self, payload: dict[str, Any]):
        self._buffer = io.BytesIO(json.dumps(payload).encode("utf-8"))

    def read(self) -> bytes:
        return self._buffer.read()

    def close(self) -> None:
        self._buffer.close()

    def __enter__(self) -> "_FakeResponse":
        return self

    def __exit__(self, exc_type, exc, tb) -> None:
        self.close()


@pytest.fixture
def sample_payload() -> dict[str, Any]:
    return {
        "values": [
            [[1.0, 0.0, 0.5], [0.5, 0.5, 0.0]],
            [[1.1, 0.1, 0.4], [0.4, 0.4, 0.1]],
        ],
        "metadata": {"dataset": "isotropic1024coarse", "field": "velocity"},
    }


def test_fetch_samples_round_trip(sample_payload: dict[str, Any]) -> None:
    fake = _FakeResponse(sample_payload)
    with mock.patch("urllib.request.urlopen", return_value=fake):
        sample = jhtdb.fetch_samples(
            dataset="isotropic1024coarse",
            field="velocity",
            times=[0.0, 0.1],
            points=[[0.0, 0.0, 0.0], [0.1, 0.1, 0.1]],
        )
    assert sample.dataset == "isotropic1024coarse"
    assert sample.field == "velocity"
    assert sample.times == [0.0, 0.1]
    assert sample.points == [[0.0, 0.0, 0.0], [0.1, 0.1, 0.1]]
    assert sample.values[0][0][0] == 1.0
    assert sample.metadata["dataset"] == "isotropic1024coarse"


def test_fetch_samples_missing_values(sample_payload: dict[str, Any]) -> None:
    payload = dict(sample_payload)
    payload.pop("values", None)
    fake = _FakeResponse(payload)
    with mock.patch("urllib.request.urlopen", return_value=fake):
        with pytest.raises(ValueError):
            jhtdb.fetch_samples(
                dataset="isotropic1024coarse",
                field="velocity",
                times=[0.0],
                points=[[0.0, 0.0, 0.0]],
            )


def test_write_sample_bundle(tmp_path: Path, sample_payload: dict[str, Any]) -> None:
    fake = _FakeResponse(sample_payload)
    with mock.patch("urllib.request.urlopen", return_value=fake):
        sample = jhtdb.fetch_samples(
            dataset="iso",
            field="vel",
            times=[0.0, 0.1],
            points=[[0.0, 0.0, 0.0], [0.1, 0.1, 0.1]],
        )
    sample_path = jhtdb.write_sample_bundle(sample, tmp_path)
    manifest_path = tmp_path / "manifest.json"
    assert sample_path.exists()
    assert manifest_path.exists()
    manifest = json.loads(manifest_path.read_text())
    sample_entry = manifest["files"]["jhtdb_samples.json"]
    assert sample_entry["bytes"] == sample_path.stat().st_size
    assert sample_entry["sha256"]

