"""Anchor extraction utilities for public dataset metadata."""

from __future__ import annotations

import dataclasses
import re
from typing import Iterable, List, Optional

__all__ = [
    "AnchorEvidence",
    "AnchoringResult",
    "extract_anchors",
    "result_to_protocol_dict",
]


_TEMPERATURE_PATTERN = re.compile(
    r"(?P<value>[+-]?[0-9]+(?:\.[0-9]+)?)\s*(?P<unit>K|kelvin|°C|C|celsius|°F|F|fahrenheit)",
    re.IGNORECASE,
)

_PIXEL_SCALE_PATTERN = re.compile(
    r"(?P<value>[0-9]+(?:\.[0-9]+)?)\s*(?P<unit>nm|µm|um|micromet(?:er|re)s?|mm|nm)\s*(?:/|per)\s*(?:px|pixel|pixels)",
    re.IGNORECASE,
)

_FRAME_INTERVAL_PATTERN = re.compile(
    r"(?P<value>[0-9]+(?:\.[0-9]+)?)\s*(?P<unit>ns|µs|us|ms|s|sec|secs|second|seconds|hz)",
    re.IGNORECASE,
)

_RADIUS_PATTERN = re.compile(
    r"(?:radius|bead radius|particle radius|bead size)\D*?(?P<value>[0-9]+(?:\.[0-9]+)?)\s*(?P<unit>nm|µm|um|micromet(?:er|re)s?|mm)",
    re.IGNORECASE,
)

_VISCOSITY_PATTERN = re.compile(
    r"(?P<value>[0-9]+(?:\.[0-9]+)?)\s*(?P<unit>pa\s*s|pa·s|pas|m?pa\s*s|m?pa·s|cp|centipoise)",
    re.IGNORECASE,
)

_KELVIN_OFFSET_C = 273.15
_KELVIN_OFFSET_F = 459.67


@dataclasses.dataclass(frozen=True)
class AnchorEvidence:
    """Represents a single extracted anchor with provenance."""

    value: float
    units: str
    verbatim: str
    derived: bool = False


@dataclasses.dataclass(frozen=True)
class AnchoringResult:
    """Holds the anchors required by the public data protocol."""

    temperature: Optional[AnchorEvidence]
    pixel_scale: Optional[AnchorEvidence]
    frame_interval: Optional[AnchorEvidence]
    bead_radius: Optional[AnchorEvidence] = None
    viscosity: Optional[AnchorEvidence] = None

    def is_complete(self) -> bool:
        return (
            self.temperature is not None
            and self.pixel_scale is not None
            and self.frame_interval is not None
        )


def _normalise_temperature(match: re.Match[str], line: str) -> AnchorEvidence:
    value = float(match.group("value"))
    unit = match.group("unit").lower()
    derived = False
    kelvin: float
    if unit in {"k", "kelvin"}:
        kelvin = value
        units = "K"
    elif unit in {"°c", "c", "celsius"}:
        kelvin = value + _KELVIN_OFFSET_C
        units = "K"
        derived = True
    elif unit in {"°f", "f", "fahrenheit"}:
        kelvin = (value + _KELVIN_OFFSET_F) * 5.0 / 9.0
        units = "K"
        derived = True
    else:
        # Should not happen but fall back to raw units.
        kelvin = value
        units = unit
    return AnchorEvidence(value=kelvin, units=units, verbatim=line.strip(), derived=derived)


def _normalise_pixel_scale(match: re.Match[str], line: str) -> AnchorEvidence:
    value = float(match.group("value"))
    unit = match.group("unit").lower()
    derived = False
    if unit in {"µm", "um", "micrometer", "micrometre", "micrometers", "micrometres"}:
        micrometers = value
        units = "µm/pixel"
    elif unit == "mm":
        micrometers = value * 1000.0
        units = "µm/pixel"
        derived = True
    elif unit == "nm":
        micrometers = value / 1000.0
        units = "µm/pixel"
        derived = True
    else:
        micrometers = value
        units = f"{unit}/pixel"
    return AnchorEvidence(value=micrometers, units=units, verbatim=line.strip(), derived=derived)


def _normalise_frame_interval(match: re.Match[str], line: str) -> Optional[AnchorEvidence]:
    value = float(match.group("value"))
    unit = match.group("unit").lower()
    derived = False
    if unit in {"s", "sec", "secs", "second", "seconds"}:
        seconds = value
        units = "s"
    elif unit in {"ms"}:
        seconds = value / 1000.0
        units = "s"
        derived = True
    elif unit in {"µs", "us"}:
        seconds = value / 1_000_000.0
        units = "s"
        derived = True
    elif unit == "ns":
        seconds = value / 1_000_000_000.0
        units = "s"
        derived = True
    elif unit == "hz":
        if value == 0:
            return None
        seconds = 1.0 / value
        units = "s"
        derived = True
    else:
        seconds = value
        units = unit
    return AnchorEvidence(value=seconds, units=units, verbatim=line.strip(), derived=derived)


def _normalise_radius(match: re.Match[str], line: str) -> AnchorEvidence:
    value = float(match.group("value"))
    unit = match.group("unit").lower()
    derived = False
    if unit in {"µm", "um", "micrometer", "micrometre", "micrometers", "micrometres"}:
        micrometers = value
        units = "µm"
    elif unit == "mm":
        micrometers = value * 1000.0
        units = "µm"
        derived = True
    elif unit == "nm":
        micrometers = value / 1000.0
        units = "µm"
        derived = True
    else:
        micrometers = value
        units = unit
    return AnchorEvidence(value=micrometers, units=units, verbatim=line.strip(), derived=derived)


def _normalise_viscosity(match: re.Match[str], line: str) -> AnchorEvidence:
    value = float(match.group("value"))
    unit = (
        match.group("unit")
        .lower()
        .replace("·", "")
        .replace(" ", "")
        .replace("*", "")
    )
    derived = False
    if unit in {"pas"}:
        pas = value
        units = "Pa·s"
    elif unit in {"mpas"}:
        pas = value / 1000.0
        units = "Pa·s"
        derived = True
    elif unit in {"cp", "centipoise"}:
        pas = value / 1000.0
        units = "Pa·s"
        derived = True
    else:
        pas = value
        units = unit
    return AnchorEvidence(value=pas, units=units, verbatim=line.strip(), derived=derived)


def _scan_lines(pattern: re.Pattern[str], lines: Iterable[str]) -> Optional[re.Match[str]]:
    for line in lines:
        match = pattern.search(line)
        if match:
            return match
    return None


def extract_anchors(lines: Iterable[str]) -> AnchoringResult:
    """Return anchoring evidence from metadata text."""

    buffered_lines: List[str] = [line for line in lines if line and line.strip()]

    temp_match = _scan_lines(_TEMPERATURE_PATTERN, buffered_lines)
    temperature = _normalise_temperature(temp_match, temp_match.string) if temp_match else None

    scale_match = _scan_lines(_PIXEL_SCALE_PATTERN, buffered_lines)
    pixel_scale = _normalise_pixel_scale(scale_match, scale_match.string) if scale_match else None

    frame_match = _scan_lines(_FRAME_INTERVAL_PATTERN, buffered_lines)
    frame_interval = _normalise_frame_interval(frame_match, frame_match.string) if frame_match else None

    radius_match = _scan_lines(_RADIUS_PATTERN, buffered_lines)
    bead_radius = _normalise_radius(radius_match, radius_match.string) if radius_match else None

    viscosity_match = _scan_lines(_VISCOSITY_PATTERN, buffered_lines)
    viscosity = _normalise_viscosity(viscosity_match, viscosity_match.string) if viscosity_match else None

    return AnchoringResult(
        temperature=temperature,
        pixel_scale=pixel_scale,
        frame_interval=frame_interval,
        bead_radius=bead_radius,
        viscosity=viscosity,
    )


def result_to_protocol_dict(result: AnchoringResult) -> dict:
    """Serialise an anchoring result to a protocol.json-compatible mapping."""

    payload = {
        "anchors": {
            "k_B_J_per_K": 1.380649e-23,
        },
    }
    if result.temperature:
        payload["anchors"]["T_K"] = result.temperature.value
        payload["anchors"]["temperature_verbatim"] = result.temperature.verbatim
    if result.pixel_scale:
        payload["anchors"]["pixel_scale_um_per_px"] = result.pixel_scale.value
        payload["anchors"]["pixel_scale_verbatim"] = result.pixel_scale.verbatim
    if result.frame_interval:
        payload["anchors"]["frame_interval_s"] = result.frame_interval.value
        payload["anchors"]["frame_interval_verbatim"] = result.frame_interval.verbatim
    if result.bead_radius:
        payload["anchors"]["bead_radius_um"] = result.bead_radius.value
        payload["anchors"]["radius_verbatim"] = result.bead_radius.verbatim
    if result.viscosity:
        payload["anchors"]["viscosity_pa_s"] = result.viscosity.value
        payload["anchors"]["viscosity_verbatim"] = result.viscosity.verbatim
    return payload

