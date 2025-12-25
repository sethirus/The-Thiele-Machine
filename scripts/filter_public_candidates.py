"""Filter discovered dataset candidates for complete anchoring metadata."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Iterable, List, Sequence

from experiments.data_sources import AnchoringResult, extract_anchors


def _extract_text_fields(candidate: dict, keys: Sequence[str]) -> List[str]:
    lines: List[str] = []
    for key in keys:
        value = candidate.get(key)
        if isinstance(value, str):
            lines.extend(value.splitlines())
        elif isinstance(value, dict):
            for element in value.values():
                if isinstance(element, str):
                    lines.extend(element.splitlines())
        elif isinstance(value, Iterable):
            for element in value:
                if isinstance(element, str):
                    lines.extend(element.splitlines())
    return lines


def _parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("candidates", type=Path, help="Path to the discovery JSON file.")
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("selected_candidates.json"),
        help="Path to write the filtered output JSON.",
    )
    parser.add_argument(
        "--metadata-keys",
        nargs="*",
        default=["description", "notes", "metadata"],
        help="Candidate keys to scan for anchoring evidence.",
    )
    return parser.parse_args(argv)


def _build_entry(candidate: dict, result: AnchoringResult) -> dict:
    anchors: dict = {
        "T_K": result.temperature.value if result.temperature else None,
        "pixel_scale_um_per_px": result.pixel_scale.value if result.pixel_scale else None,
        "frame_interval_s": result.frame_interval.value if result.frame_interval else None,
        "temperature_verbatim": result.temperature.verbatim if result.temperature else None,
        "pixel_scale_verbatim": result.pixel_scale.verbatim if result.pixel_scale else None,
        "frame_interval_verbatim": result.frame_interval.verbatim if result.frame_interval else None,
        "derived_flags": {
            "temperature": result.temperature.derived if result.temperature else None,
            "pixel_scale": result.pixel_scale.derived if result.pixel_scale else None,
            "frame_interval": result.frame_interval.derived if result.frame_interval else None,
        },
    }
    if result.bead_radius:
        anchors["bead_radius_um"] = result.bead_radius.value
        anchors["radius_verbatim"] = result.bead_radius.verbatim
        anchors["derived_flags"]["bead_radius"] = result.bead_radius.derived
    if result.viscosity:
        anchors["viscosity_pa_s"] = result.viscosity.value
        anchors["viscosity_verbatim"] = result.viscosity.verbatim
        anchors["derived_flags"]["viscosity"] = result.viscosity.derived
    payload = {
        "candidate": candidate,
        "anchors": anchors,
    }
    return payload


def main(argv: Sequence[str] | None = None) -> int:
    args = _parse_args(argv)
    data = json.loads(args.candidates.read_text(encoding="utf-8"))
    candidates = data.get("candidates", [])
    selected: List[dict] = []

    for candidate in candidates:
        lines = _extract_text_fields(candidate, args.metadata_keys)
        result = extract_anchors(lines)
        if result.is_complete():
            selected.append(_build_entry(candidate, result))

    summary = {
        "input_candidates": len(candidates),
        "selected_candidates": len(selected),
    }

    document = {
        "summary": summary,
        "selected": selected,
    }
    args.output.write_text(json.dumps(document, indent=2, sort_keys=True))
    print(json.dumps(summary, indent=2, sort_keys=True))
    print(f"Wrote {len(selected)} anchored candidates to {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

