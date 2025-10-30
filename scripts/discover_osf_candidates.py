"""CLI utility to enumerate OSF dataset candidates for the Thiele protocol."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Sequence

from experiments.data_sources.osf import (
    OSFSearchConfig,
    discover_osf_candidates,
    serialise_candidates,
)

DEFAULT_QUERIES = (
    '"optical tweezers"',
    '"single particle tracking"',
    '"Brownian"',
    '"MSD"',
    '"optical tweezers" csv',
    '"single particle tracking" csv',
)


def _parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("osf_candidates.json"),
        help="Path to write the discovery JSON output.",
    )
    parser.add_argument(
        "--queries",
        nargs="*",
        default=list(DEFAULT_QUERIES),
        help="Override the default OSF search queries.",
    )
    parser.add_argument(
        "--page-size",
        type=int,
        default=75,
        help="Number of results to request per OSF API page.",
    )
    parser.add_argument(
        "--max-pages",
        type=int,
        default=4,
        help="Maximum number of pages to pull per query.",
    )
    parser.add_argument(
        "--per-query-limit",
        type=int,
        default=200,
        help="Upper bound on results considered per query.",
    )
    parser.add_argument(
        "--extensions",
        nargs="*",
        default=None,
        help="Allowed file extensions (defaults to csv/tsv/h5/hdf5/mat/tif/tiff).",
    )
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = _parse_args(argv)
    config = OSFSearchConfig(
        queries=args.queries,
        page_size=args.page_size,
        max_pages=args.max_pages,
        per_query_limit=args.per_query_limit,
    )
    if args.extensions is not None:
        allowed_extensions = tuple(args.extensions)
        config.allowed_extensions = allowed_extensions
    else:
        allowed_extensions = config.allowed_extensions
    candidates, summary = discover_osf_candidates(config)
    summary["allowed_extensions"] = list(allowed_extensions)
    document = serialise_candidates(candidates, summary)
    args.output.write_text(document)
    print(json.dumps(summary, indent=2, sort_keys=True))
    print(f"Wrote {len(candidates)} candidates to {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
