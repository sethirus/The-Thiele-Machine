from __future__ import annotations

import json
from pathlib import Path
from unittest import mock

import pytest

from experiments.data_sources.jhtdb import DEFAULT_BASE_URL, DEFAULT_SAMPLE_ENDPOINT
from scripts import sample_jhtdb


class _FakeResponse:
    def __init__(self, payload: dict[str, object]):
        self._payload = json.dumps(payload).encode("utf-8")

    def read(self) -> bytes:
        return self._payload

    def close(self) -> None:
        pass

    def __enter__(self) -> "_FakeResponse":
        return self

    def __exit__(self, exc_type, exc, tb) -> None:
        pass


@pytest.fixture
def config_file(tmp_path: Path) -> Path:
    config = {
        "dataset": "isotropic1024coarse",
        "field": "velocity",
        "times": [0.0, 0.1],
        "points": [[0.0, 0.0, 0.0], [0.1, 0.1, 0.1]],
        "extra_payload": {"spatial_interp": "lagrangian"},
    }
    path = tmp_path / "config.json"
    path.write_text(json.dumps(config))
    return path


def test_sample_cli_round_trip(tmp_path: Path, config_file: Path) -> None:
    payload = {
        "values": [
            [[1.0, 0.0, 0.5], [0.5, 0.5, 0.0]],
            [[1.1, 0.1, 0.4], [0.4, 0.4, 0.1]],
        ],
        "metadata": {"dataset": "isotropic1024coarse", "field": "velocity"},
    }
    fake = _FakeResponse(payload)
    with mock.patch("urllib.request.urlopen", return_value=fake) as patched:
        sample_jhtdb.main(
            [
                "--config",
                str(config_file),
                "--output-dir",
                str(tmp_path / "bundle"),
            ]
        )
    assert patched.call_args is not None
    args, kwargs = patched.call_args
    req = args[0]
    assert DEFAULT_BASE_URL in req.full_url
    assert DEFAULT_SAMPLE_ENDPOINT in req.full_url
    bundle_dir = tmp_path / "bundle"
    sample_path = bundle_dir / "jhtdb_samples.json"
    manifest_path = bundle_dir / "manifest.json"
    assert sample_path.exists()
    assert manifest_path.exists()
    manifest = json.loads(manifest_path.read_text())
    assert manifest["files"]["jhtdb_samples.json"]["sha256"]

