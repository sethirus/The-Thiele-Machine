"""Integration tests for the download_public_files CLI."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Dict

import pytest

from scripts import download_public_files


class FakeResponse:
    def __init__(self, content: bytes) -> None:
        self._content = content
        self.status_code = 200

    def iter_content(self, chunk_size: int):  # pragma: no cover - simple generator
        yield self._content


class FakeSession:
    def __init__(self, mapping: Dict[str, bytes]) -> None:
        self._mapping = mapping

    def __enter__(self) -> "FakeSession":
        return self

    def __exit__(self, exc_type, exc, tb) -> None:
        return None

    def get(self, url: str, stream: bool = True, timeout: float = 30.0) -> FakeResponse:
        if url not in self._mapping:
            raise AssertionError(f"Unexpected URL requested: {url}")
        return FakeResponse(self._mapping[url])


@pytest.fixture()
def selected_payload(tmp_path: Path) -> Path:
    data = {
        "summary": {"input_candidates": 1, "selected_candidates": 1},
        "selected": [
            {
                "candidate": {
                    "node_id": "abc123",
                    "title": "Optical tweezers calibration",
                    "files": [
                        {
                            "file_id": "f1",
                            "name": "track1.csv",
                            "path": "tracks/track1.csv",
                            "download_url": "https://example.org/track1.csv",
                        },
                        {
                            "file_id": "f2",
                            "name": "track2.csv",
                            "download_url": "https://example.org/track2.csv",
                        },
                    ],
                },
                "anchors": {
                    "T_K": 298.0,
                    "pixel_scale_um_per_px": 0.16,
                    "frame_interval_s": 0.005,
                    "bead_radius_um": 0.5,
                    "viscosity_pa_s": 0.001,
                    "temperature_verbatim": "Temperature: 298 K",
                    "pixel_scale_verbatim": "Pixel size 0.16 µm/pixel",
                    "frame_interval_verbatim": "Frame interval 5 ms",
                    "radius_verbatim": "Bead radius 0.5 µm",
                    "viscosity_verbatim": "Viscosity 1.0 mPa·s",
                    "derived_flags": {
                        "temperature": False,
                        "pixel_scale": False,
                        "frame_interval": False,
                        "bead_radius": False,
                        "viscosity": True,
                    },
                },
            }
        ],
    }
    path = tmp_path / "selected.json"
    path.write_text(json.dumps(data))
    return path


def test_download_public_files_cli(monkeypatch, tmp_path: Path, selected_payload: Path) -> None:
    output_dir = tmp_path / "downloads"
    mapping = {
        "https://example.org/track1.csv": b"track1",
        "https://example.org/track2.csv": b"track2",
    }

    def _session_factory() -> FakeSession:
        return FakeSession(mapping)

    monkeypatch.setattr(
        download_public_files,
        "requests",
        type("_R", (), {"Session": staticmethod(_session_factory)}),
    )

    exit_code = download_public_files.main(
        [
            str(selected_payload),
            "--source",
            "osf",
            "--output-dir",
            str(output_dir),
            "--report",
            str(tmp_path / "report.json"),
        ]
    )
    assert exit_code == 0

    source_dir = output_dir / "osf"
    assert source_dir.exists()
    dataset_dirs = list(source_dir.iterdir())
    assert len(dataset_dirs) == 1
    dataset_dir = dataset_dirs[0]
    manifest = json.loads((dataset_dir / "MANIFEST.json").read_text())
    assert manifest["file_count"] == 2

    for entry in manifest["files"]:
        file_path = dataset_dir / entry["path"]
        assert file_path.exists()
        expected_hash = hashlib.sha256(file_path.read_bytes()).hexdigest()
        assert expected_hash == entry["sha256"]

    anchors = json.loads((dataset_dir / "anchors.json").read_text())
    assert pytest.approx(anchors["pixel_scale_um_per_px"], rel=1e-12) == 0.16

    summary = json.loads((tmp_path / "report.json").read_text())
    assert summary["summary"]["downloaded_count"] == 1
