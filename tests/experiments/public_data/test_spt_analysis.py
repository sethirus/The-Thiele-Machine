"""Tests for public single-particle tracking analysis helpers."""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from experiments.public_data import (
    Anchors,
    diffusion_residuals,
    estimate_diffusion,
    iter_tracks,
    load_anchors,
    oos_diffusion_error,
    predicted_diffusion,
)

DATA_DIR = Path(__file__).resolve().parents[2] / "data" / "public"


def _load_tracks() -> list:
    return list(iter_tracks(DATA_DIR / "sample_tracks.csv"))


def _load_anchors() -> Anchors:
    return load_anchors(DATA_DIR / "sample_anchors.json")


def test_predicted_diffusion_matches_stokes_relation() -> None:
    anchors = _load_anchors()
    predicted = predicted_diffusion(anchors)
    assert predicted is not None
    gamma = 6.0 * 3.141592653589793 * anchors.viscosity_pa_s * anchors.bead_radius_m
    expected = 1.380649e-23 * anchors.temperature_K / gamma * 1e12
    assert predicted == pytest.approx(expected, rel=1e-12)


def test_estimate_diffusion_uses_msd_slope() -> None:
    anchors = _load_anchors()
    tracks = _load_tracks()
    track = tracks[0]
    diffusion = estimate_diffusion(track, anchors)
    # The sample data is built so the MSD slope yields a stable value.
    assert diffusion == pytest.approx(0.44928, rel=1e-5)


def test_diffusion_residuals_zero_mean_when_matching_prediction() -> None:
    anchors = _load_anchors()
    tracks = _load_tracks()
    predicted = predicted_diffusion(anchors)
    assert predicted is not None
    residuals = diffusion_residuals(tracks, anchors)
    # The synthetic data is tuned so measured diffusion is close to predicted.
    assert all(abs(value) < 1.5e-2 for value in residuals)


def test_oos_diffusion_error_computes_mape() -> None:
    anchors = _load_anchors()
    tracks = _load_tracks()
    error = oos_diffusion_error(tracks, anchors)
    assert error < 0.01


def test_oos_diffusion_error_requires_optional_anchors() -> None:
    anchors = _load_anchors()
    anchors = Anchors(
        temperature_K=anchors.temperature_K,
        pixel_scale_um_per_px=anchors.pixel_scale_um_per_px,
        frame_interval_s=anchors.frame_interval_s,
    )
    tracks = _load_tracks()
    with pytest.raises(ValueError):
        oos_diffusion_error(tracks, anchors)


def test_load_anchors_accepts_bundle_schema(tmp_path: Path) -> None:
    payload = {
        "temperature_K": 297.0,
        "pixel_size_m": 1.5e-07,
        "time_step_s": 0.008,
        "bead_radius_m": 4.0e-07,
        "viscosity_mPa_s": 0.98,
        "source": "repacked bundle",
        "assumptions": ["Converted viscosity from mPa·s"],
    }
    anchor_path = tmp_path / "anchors.json"
    anchor_path.write_text(json.dumps(payload), encoding="utf-8")

    anchors = load_anchors(anchor_path)

    assert anchors.temperature_K == pytest.approx(297.0)
    assert anchors.pixel_scale_um_per_px == pytest.approx(0.15)
    assert anchors.frame_interval_s == pytest.approx(0.008)
    assert anchors.bead_radius_um == pytest.approx(0.4)
    assert anchors.viscosity_pa_s == pytest.approx(0.00098)
    assert anchors.source_verbatim is not None
