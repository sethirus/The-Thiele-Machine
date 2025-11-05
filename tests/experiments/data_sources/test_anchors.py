"""Tests for metadata anchor extraction."""

from __future__ import annotations

from experiments.data_sources import AnchoringResult, extract_anchors


def test_extract_anchors_complete() -> None:
    lines = [
        "Temperature: 298 K (room temperature).",
        "Imaging pixel size 0.108 µm/pixel calibrated with slide.",
        "Frame interval = 12.5 ms for all acquisitions.",
        "Bead radius 0.5 µm per datasheet.",
        "Viscosity of medium 1.2 mPa·s (buffer).",
    ]
    result = extract_anchors(lines)
    assert isinstance(result, AnchoringResult)
    assert result.is_complete()
    assert result.temperature and abs(result.temperature.value - 298.0) < 1e-9
    assert result.pixel_scale and abs(result.pixel_scale.value - 0.108) < 1e-9
    assert result.frame_interval and abs(result.frame_interval.value - 0.0125) < 1e-12
    assert result.bead_radius and abs(result.bead_radius.value - 0.5) < 1e-9
    assert result.viscosity and abs(result.viscosity.value - 0.0012) < 1e-12


def test_extract_anchors_converts_units() -> None:
    lines = [
        "Temperature maintained at 25 C throughout experiments.",
        "Pixel scale: 110 nm/pixel using calibration grid.",
        "Acquisition rate 200 Hz (stroboscopic).",
    ]
    result = extract_anchors(lines)
    assert result.is_complete()
    assert result.temperature and abs(result.temperature.value - (25 + 273.15)) < 1e-9
    assert result.pixel_scale and abs(result.pixel_scale.value - 0.11) < 1e-12
    assert result.frame_interval and abs(result.frame_interval.value - 0.005) < 1e-12


def test_extract_anchors_incomplete_when_missing_field() -> None:
    lines = [
        "Temperature 296 K.",
        "Frame interval: 10 ms.",
    ]
    result = extract_anchors(lines)
    assert not result.is_complete()

