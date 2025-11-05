from __future__ import annotations

import argparse
from pathlib import Path
from typing import Iterable, Sequence

from experiments.turbulence import PROTOCOLS, run_dataset


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Run anchored turbulence protocol")
    parser.add_argument(
        "dataset_dir",
        type=Path,
        help="Directory containing jhtdb_samples.json",
    )
    parser.add_argument(
        "--output-dir",
        type=Path,
        required=True,
        help="Destination directory for generated artefacts",
    )
    parser.add_argument(
        "--protocol",
        choices=PROTOCOLS,
        action="append",
        help="Limit execution to the selected protocol(s)",
    )
    parser.add_argument(
        "--seed",
        type=int,
        default=0,
        help="Deterministic seed used by destroyed protocol shuffling",
    )
    return parser


def main(argv: Iterable[str] | None = None) -> None:  # pragma: no cover - CLI wrapper
    parser = _build_parser()
    args = parser.parse_args(argv)

    protocols: Sequence[str] | None = tuple(args.protocol) if args.protocol else None
    try:
        run_dataset(
            dataset_dir=args.dataset_dir,
            output_dir=args.output_dir,
            protocols=protocols,
            seed=args.seed,
        )
    except Exception as exc:  # pragma: no cover - surfaced in tests
        print(f"TURBULENCE_FAIL: {exc}")
        raise SystemExit(1) from exc

    print("TURBULENCE_OK")


if __name__ == "__main__":  # pragma: no cover
    main()
