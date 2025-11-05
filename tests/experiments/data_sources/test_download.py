"""Unit tests for the dataset download utilities."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Dict

import pytest

from experiments.data_sources import download


@pytest.mark.parametrize(
    "parts, expected",
    [
        (("OSF", "ABC123", "Optical Tweezers"), "osf-abc123-optical-tweezers"),
        (("", ""), "dataset"),
        (("  Title  ",), "title"),
    ],
)
def test_slugify(parts: tuple[str, ...], expected: str) -> None:
    assert download.slugify(parts) == expected[:120]


def test_verify_manifest_detects_checksum_mismatch(tmp_path: Path) -> None:
    data_dir = tmp_path / "dataset"
    data_dir.mkdir()
    file_path = data_dir / "raw" / "track.csv"
    file_path.parent.mkdir()
    file_path.write_text("content")
    manifest = {
        "files": [
            {
                "path": "raw/track.csv",
                "sha256": "deadbeef",
                "size": 3,
            }
        ]
    }
    manifest_path = data_dir / "MANIFEST.json"
    manifest_path.write_text(json.dumps(manifest))
    with pytest.raises(download.DownloadError):
        download.verify_manifest(manifest_path)


@pytest.mark.parametrize(
    "source,candidate,expected",
    [
        (
            "osf",
            {"node_id": "abc123", "title": "Optical tweezers calibration"},
            "osf-abc123-optical-tweezers-calibration",
        ),
        (
            "figshare",
            {"article_id": "42", "description": "Brownian study"},
            "figshare-42-brownian-study",
        ),
        (
            "dryad",
            {"identifier": "doi:10.1/demo", "doi": "10.1/demo"},
            "dryad-doi-10-1-demo-10-1-demo",
        ),
    ],
)
def test_derive_dataset_slug(source: str, candidate: Dict[str, object], expected: str) -> None:
    assert download.derive_dataset_slug(source, candidate) == expected[:120]
