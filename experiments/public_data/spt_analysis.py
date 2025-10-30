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
    source_verbatim = {
        key: data[key]
        for key in (
            "temperature_verbatim",
            "pixel_scale_verbatim",
            "frame_interval_verbatim",
            "radius_verbatim",
            "viscosity_verbatim",
        )
        if key in data
    } or None
    return Anchors(
        temperature_K=float(data["T_K"]),
        pixel_scale_um_per_px=float(data["pixel_scale_um_per_px"]),
        frame_interval_s=float(data["frame_interval_s"]),
        bead_radius_um=float(data.get("bead_radius_um")) if data.get("bead_radius_um") is not None else None,
        viscosity_pa_s=float(data.get("viscosity_pa_s")) if data.get("viscosity_pa_s") is not None else None,
        source_verbatim=source_verbatim,
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
