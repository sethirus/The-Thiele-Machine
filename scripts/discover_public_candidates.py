"""CLI utility to enumerate public dataset candidates for the Thiele protocol."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Callable, Dict, Sequence, Tuple, Type

from experiments.data_sources import (
    DryadSearchConfig,
    FigshareSearchConfig,
    OSFSearchConfig,
    ZenodoSearchConfig,
    discover_dryad_candidates,
    discover_figshare_candidates,
    discover_osf_candidates,
    discover_zenodo_candidates,
    serialise_dryad_candidates,
    serialise_figshare_candidates,
    serialise_osf_candidates,
    serialise_zenodo_candidates,
)

DiscoverFn = Callable[[object], Tuple[Sequence[object], Dict[str, object]]]
SerialiseFn = Callable[[Sequence[object], Dict[str, object]], str]

_DEFAULT_QUERIES = {
    "osf": [
        '"optical tweezers"',
        '"single particle tracking"',
        '"Brownian"',
        '"MSD"',
    ],
    "figshare": [
        '"optical tweezers"',
        '"single particle tracking"',
        '"Brownian motion"',
    ],
    "dryad": [
        '"optical tweezers"',
        '"single-molecule"',
        '"single particle tracking"',
        '"Brownian"',
    ],
    "zenodo": [
        '"optical tweezers"',
        '"single particle tracking"',
        '"Brownian"',
    ],
}

_SOURCES: Dict[str, Tuple[Type[object], DiscoverFn, SerialiseFn, Sequence[str]]] = {
    "osf": (OSFSearchConfig, discover_osf_candidates, serialise_osf_candidates, _DEFAULT_QUERIES["osf"]),
    "figshare": (FigshareSearchConfig, discover_figshare_candidates, serialise_figshare_candidates, _DEFAULT_QUERIES["figshare"]),
    "dryad": (DryadSearchConfig, discover_dryad_candidates, serialise_dryad_candidates, _DEFAULT_QUERIES["dryad"]),
    "zenodo": (ZenodoSearchConfig, discover_zenodo_candidates, serialise_zenodo_candidates, _DEFAULT_QUERIES["zenodo"]),
}

_DEFAULT_OUTPUTS = {
    "osf": Path("osf_candidates.json"),
    "figshare": Path("figshare_candidates.json"),
    "dryad": Path("dryad_candidates.json"),
    "zenodo": Path("zenodo_candidates.json"),
}


def _parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--source",
        choices=sorted(_SOURCES.keys()),
        default="osf",
        help="Data repository to query.",
    )
    parser.add_argument(
        "--output",
        type=Path,
        help="Path to write the discovery JSON output (defaults per source).",
    )
    parser.add_argument(
        "--queries",
        nargs="*",
        help="Override the default search queries.",
    )
    parser.add_argument(
        "--page-size",
        type=int,
        default=75,
        help="Number of results to request per API page.",
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
        help="Allowed file extensions (defaults provided by each source).",
    )
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = _parse_args(argv)
    config_cls, discover, serialise, default_queries = _SOURCES[args.source]
    output_path = args.output or _DEFAULT_OUTPUTS[args.source]
    queries = args.queries or list(default_queries)
    kwargs = {
        "queries": queries,
        "page_size": args.page_size,
        "max_pages": args.max_pages,
        "per_query_limit": args.per_query_limit,
    }
    if args.extensions is not None:
        kwargs["allowed_extensions"] = tuple(args.extensions)
    config = config_cls(**kwargs)  # type: ignore[call-arg]
    candidates, summary = discover(config)  # type: ignore[arg-type]
    summary["allowed_extensions"] = list(getattr(config, "allowed_extensions", []))
    document = serialise(candidates, summary)
    output_path.write_text(document)
    print(json.dumps(summary, indent=2, sort_keys=True))
    print(f"Wrote {len(candidates)} candidates to {output_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
