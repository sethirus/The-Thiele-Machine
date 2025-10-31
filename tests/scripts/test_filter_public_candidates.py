"""Integration tests for the filter_public_candidates CLI."""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from scripts import filter_public_candidates


@pytest.fixture()
def candidates_path(tmp_path: Path) -> Path:
    source = Path(__file__).resolve().parents[1] / "data" / "sample_candidates.json"
    destination = tmp_path / "candidates.json"
    destination.write_text(source.read_text())
    return destination


def test_filter_public_candidates_selects_complete_entries(tmp_path: Path, candidates_path: Path) -> None:
    output = tmp_path / "selected.json"
    exit_code = filter_public_candidates.main([str(candidates_path), "--output", str(output)])
    assert exit_code == 0
    payload = json.loads(output.read_text())
    assert payload["summary"]["input_candidates"] == 2
    assert payload["summary"]["selected_candidates"] == 1
    entry = payload["selected"][0]
    assert entry["candidate"]["node_id"] == "abc123"
    assert entry["candidate"]["title"] == "Optical tweezers calibration"
    assert abs(entry["anchors"]["frame_interval_s"] - 0.005) < 1e-12
    assert abs(entry["anchors"]["bead_radius_um"] - 0.5) < 1e-9
    assert abs(entry["anchors"]["viscosity_pa_s"] - 0.001) < 1e-12

