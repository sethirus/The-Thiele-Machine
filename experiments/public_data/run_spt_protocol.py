"""CLI wrapper for generating public SPT proofpack artefacts."""

from __future__ import annotations

import argparse
from pathlib import Path
from typing import Iterable, Sequence

from .spt_protocol import PROTOCOLS, run_dataset


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Run anchored public SPT protocol")
    parser.add_argument("dataset_dir", type=Path, help="Mirrored dataset directory with anchors.json")
    parser.add_argument("--output-dir", type=Path, required=True, help="Destination directory for artefacts")
    parser.add_argument(
        "--protocol",
        choices=PROTOCOLS,
        action="append",
        help="Limit execution to the selected protocol(s)",
    )
    parser.add_argument("--seed", type=int, default=0, help="Deterministic seed for destroyed protocol shuffling")
    parser.add_argument(
        "--tracks",
        type=Path,
        default=None,
        help="Optional explicit path to the mirrored tracks CSV",
    )
    return parser


def main(argv: Iterable[str] | None = None) -> None:  # pragma: no cover - CLI glue
    parser = _build_parser()
    args = parser.parse_args(argv)

    protocols: Sequence[str] | None = tuple(args.protocol) if args.protocol else None
    try:
        run_dataset(
            dataset_dir=args.dataset_dir,
            output_dir=args.output_dir,
            protocols=protocols,
            seed=args.seed,
            tracks_path=args.tracks,
        )
    except Exception as exc:  # pragma: no cover - surfaced via tests
        print(f"PUBLIC_SPT_FAIL: {exc}")
        raise SystemExit(1) from exc

    print("PUBLIC_SPT_OK")


if __name__ == "__main__":  # pragma: no cover
    main()

