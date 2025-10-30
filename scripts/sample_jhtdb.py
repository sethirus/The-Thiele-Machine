"""CLI for sampling small turbulence trajectories from the JHTDB service."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any, Mapping

from experiments.data_sources.jhtdb import fetch_samples, write_sample_bundle


def _load_config(path: Path) -> Mapping[str, Any]:
    with path.open("r", encoding="utf-8") as handle:
        data = json.load(handle)
    if not isinstance(data, Mapping):
        raise ValueError("Configuration must contain a JSON object")
    return data


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Sample trajectories from JHTDB")
    parser.add_argument("--config", type=Path, required=True, help="JSON configuration file")
    parser.add_argument(
        "--output-dir",
        type=Path,
        required=True,
        help="Directory where the sample bundle will be written",
    )
    parser.add_argument(
        "--sample-endpoint",
        default=None,
        help="Override the default REST endpoint for sampling",
    )
    return parser


def main(argv: list[str] | None = None) -> None:  # pragma: no cover - CLI wrapper
    parser = _build_parser()
    args = parser.parse_args(argv)
    config = dict(_load_config(args.config))

    endpoint_override = args.sample_endpoint
    if endpoint_override:
        config["endpoint"] = endpoint_override

    sample = fetch_samples(**config)
    write_sample_bundle(sample, args.output_dir)


if __name__ == "__main__":  # pragma: no cover - script entry point
    main()

