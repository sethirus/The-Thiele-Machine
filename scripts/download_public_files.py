"""Download filtered public dataset candidates and build manifests."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any, Dict, Sequence

import requests

from experiments.data_sources.download import (
    DownloadConfig,
    DownloadError,
    download_selected_candidate,
)

_SUPPORTED_SOURCES = {"osf", "figshare", "dryad", "zenodo"}


def _parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "selected",
        type=Path,
        help="Path to the filtered candidates JSON file produced by filter_public_candidates.",
    )
    parser.add_argument(
        "--source",
        choices=sorted(_SUPPORTED_SOURCES),
        required=True,
        help="Data source identifier (required to build deterministic slugs).",
    )
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path("public_data"),
        help="Root directory to mirror downloaded datasets into.",
    )
    parser.add_argument(
        "--chunk-size",
        type=int,
        default=64 * 1024,
        help="Download chunk size in bytes.",
    )
    parser.add_argument(
        "--timeout",
        type=float,
        default=30.0,
        help="HTTP request timeout in seconds.",
    )
    parser.add_argument(
        "--no-skip-existing",
        dest="skip_existing",
        action="store_false",
        help="Re-download files even if they already exist on disk.",
    )
    parser.add_argument(
        "--report",
        type=Path,
        help="Optional path to write a JSON summary of downloaded datasets.",
    )
    parser.set_defaults(skip_existing=True)
    return parser.parse_args(argv)


def _load_selected(path: Path) -> Dict[str, Any]:
    payload = json.loads(path.read_text())
    if not isinstance(payload, dict):
        raise DownloadError("Selected file does not contain a JSON object")
    return payload


def main(argv: Sequence[str] | None = None) -> int:
    args = _parse_args(argv)
    payload = _load_selected(args.selected)
    entries = payload.get("selected", [])
    if not isinstance(entries, list):
        raise DownloadError("Selected payload is missing the 'selected' list")

    config = DownloadConfig(
        base_dir=args.output_dir,
        chunk_size=args.chunk_size,
        request_timeout=args.timeout,
        skip_existing=args.skip_existing,
    )

    results = []
    with requests.Session() as session:
        for entry in entries:
            outcome = download_selected_candidate(
                entry,
                source=args.source,
                config=config,
                session=session,
            )
            results.append(
                {
                    "dataset_id": outcome.manifest["dataset_id"],
                    "directory": str(outcome.dataset_dir),
                    "file_count": outcome.manifest["file_count"],
                }
            )

    summary = {
        "source": args.source,
        "selected_count": len(entries),
        "downloaded_count": len(results),
        "output_dir": str(args.output_dir),
    }
    document = {"summary": summary, "datasets": results}
    text = json.dumps(document, indent=2, sort_keys=True)
    if args.report:
        args.report.write_text(text)
    print(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
