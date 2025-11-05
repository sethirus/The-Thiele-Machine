"""Analysis helpers for single-particle tracking public datasets."""

from __future__ import annotations

import csv
import json
import math
from dataclasses import dataclass
from pathlib import Path
from statistics import median
from typing import Dict, Iterable, Iterator, List, Sequence, Tuple

K_BOLTZMANN = 1.380_649e-23


@dataclass(frozen=True)
class Anchors:
    """Physical anchors extracted from public metadata."""

    temperature_K: float
    pixel_scale_um_per_px: float
    frame_interval_s: float
    bead_radius_um: float | None = None
    viscosity_pa_s: float | None = None
    source_verbatim: Dict[str, str] | None = None

    @property
    def bead_radius_m(self) -> float | None:
        if self.bead_radius_um is None:
            return None
        return self.bead_radius_um * 1e-6


@dataclass(frozen=True)
class TrackSample:
    track_id: str
    frame_index: int
    x_px: float
    y_px: float

    def as_um(self, pixel_scale_um_per_px: float) -> Tuple[float, float]:
        scale = pixel_scale_um_per_px
        return self.x_px * scale, self.y_px * scale


@dataclass(frozen=True)
class TrackSeries:
    track_id: str
    samples: Sequence[TrackSample]

    def __post_init__(self) -> None:
        if not self.samples:
            raise ValueError(f"Track {self.track_id} has no samples")
        frames = [sample.frame_index for sample in self.samples]
        if frames != sorted(frames):
            raise ValueError(f"Track {self.track_id} frame indices must be sorted")


def load_anchors(path: Path) -> Anchors:
    data = json.loads(path.read_text())

    def _first(keys: Sequence[str]) -> object | None:
        for key in keys:
            if key in data and data[key] is not None:
                return data[key]
        return None

    def _require(keys: Sequence[str], *, label: str) -> float:
        value = _first(keys)
        if value is None:
            raise KeyError(f"Missing required anchor field: {label}")
        return float(value)

    temperature = _require(("T_K", "temperature_K"), label="temperature")
    pixel_scale_raw = _first(("pixel_scale_um_per_px", "pixel_size_um", "pixel_size_m"))
    if pixel_scale_raw is None:
        raise KeyError("Missing required anchor field: pixel scale")
    if "pixel_size_m" in data and data["pixel_size_m"] == pixel_scale_raw:
        pixel_scale = float(pixel_scale_raw) * 1e6
    else:
        pixel_scale = float(pixel_scale_raw)
    frame_interval = _require(("frame_interval_s", "time_step_s", "dt_s"), label="frame interval")

    bead_radius = _first(("bead_radius_um", "particle_radius_um", "bead_radius_m"))
    if bead_radius is not None and "bead_radius_m" in data and data["bead_radius_m"] == bead_radius:
        bead_radius = float(bead_radius) * 1e6
    viscosity = _first(("viscosity_pa_s", "fluid_viscosity_pa_s", "viscosity_mPa_s"))
    if viscosity is not None and "viscosity_mPa_s" in data and data["viscosity_mPa_s"] == viscosity:
        viscosity = float(viscosity) * 1e-3

    source_fields = {
        key: data[key]
        for key in (
            "temperature_verbatim",
            "pixel_scale_verbatim",
            "frame_interval_verbatim",
            "radius_verbatim",
            "viscosity_verbatim",
        )
        if key in data
    }
    if "source" in data:
        source_fields["source"] = data["source"]
    if "assumptions" in data:
        source_fields["assumptions"] = data["assumptions"]

    return Anchors(
        temperature_K=temperature,
        pixel_scale_um_per_px=pixel_scale,
        frame_interval_s=frame_interval,
        bead_radius_um=float(bead_radius) if bead_radius is not None else None,
        viscosity_pa_s=float(viscosity) if viscosity is not None else None,
        source_verbatim=source_fields or None,
    )


def iter_tracks(path: Path) -> Iterator[TrackSeries]:
    by_track: Dict[str, List[TrackSample]] = {}
    with path.open(newline="") as handle:
        reader = csv.DictReader(handle)
        required = {"track_id", "frame", "x_px", "y_px"}
        missing = required - set(reader.fieldnames or [])
        if missing:
            raise ValueError(f"Missing columns: {sorted(missing)}")
        for row in reader:
            track_id = row["track_id"]
            frame_index = int(row["frame"])
            x_px = float(row["x_px"])
            y_px = float(row["y_px"])
            by_track.setdefault(track_id, []).append(
                TrackSample(track_id=track_id, frame_index=frame_index, x_px=x_px, y_px=y_px)
            )
    for track_id, samples in by_track.items():
        samples.sort(key=lambda sample: sample.frame_index)
        yield TrackSeries(track_id=track_id, samples=tuple(samples))


def _squared_displacements(track: TrackSeries, pixel_scale: float) -> List[float]:
    displacements: List[float] = []
    samples = track.samples
    for prev, curr in zip(samples, samples[1:]):
        x_prev, y_prev = prev.as_um(pixel_scale)
        x_curr, y_curr = curr.as_um(pixel_scale)
        dx = x_curr - x_prev
        dy = y_curr - y_prev
        displacements.append(dx * dx + dy * dy)
    return displacements


def _msd_slope(displacements: Sequence[float], dt: float) -> float:
    if not displacements:
        raise ValueError("Cannot compute MSD slope for empty sequence")
    mean_displacement = sum(displacements) / len(displacements)
    return mean_displacement / (4.0 * dt)


def estimate_diffusion(track: TrackSeries, anchors: Anchors) -> float:
    displacements = _squared_displacements(track, anchors.pixel_scale_um_per_px)
    return _msd_slope(displacements, anchors.frame_interval_s)


def predicted_diffusion(anchors: Anchors) -> float | None:
    if anchors.bead_radius_m is None or anchors.viscosity_pa_s is None:
        return None
    gamma = 6.0 * math.pi * anchors.viscosity_pa_s * anchors.bead_radius_m
    # Convert diffusion from m^2/s to µm^2/s to match ledger units.
    return K_BOLTZMANN * anchors.temperature_K / gamma * 1e12


def diffusion_residuals(tracks: Iterable[TrackSeries], anchors: Anchors) -> List[float]:
    predicted = predicted_diffusion(anchors)
    results: List[float] = []
    for track in tracks:
        measured = estimate_diffusion(track, anchors)
        if predicted is None:
            results.append(measured)
        else:
            results.append(measured - predicted)
    return results


def split_tracks(tracks: Sequence[TrackSeries]) -> Tuple[List[TrackSeries], List[TrackSeries]]:
    midpoint = len(tracks) // 2
    return list(tracks[:midpoint]), list(tracks[midpoint:])


def median_absolute_percentage_error(predicted: Sequence[float], observed: Sequence[float]) -> float:
    if len(predicted) != len(observed):
        raise ValueError("Predicted and observed sequences must have the same length")
    errors = []
    for pred, obs in zip(predicted, observed):
        if obs == 0:
            continue
        errors.append(abs((pred - obs) / obs))
    if not errors:
        return 0.0
    return median(errors)


def oos_diffusion_error(tracks: Sequence[TrackSeries], anchors: Anchors) -> float:
    if not tracks:
        raise ValueError("At least one track is required")
    train, test = split_tracks(tracks)
    if not train or not test:
        raise ValueError("Need at least two tracks to compute OOS error")
    predicted = predicted_diffusion(anchors)
    if predicted is None:
        raise ValueError("Cannot compute OOS error without viscosity and bead radius anchors")
    observed = [estimate_diffusion(track, anchors) for track in test]
    preds = [predicted for _ in observed]
    return median_absolute_percentage_error(preds, observed)


__all__ = [
    "Anchors",
    "TrackSample",
    "TrackSeries",
    "load_anchors",
    "iter_tracks",
    "estimate_diffusion",
    "predicted_diffusion",
    "diffusion_residuals",
    "oos_diffusion_error",
]
