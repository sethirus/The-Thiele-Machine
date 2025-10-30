"""End-to-end automation for the public-data proofpack pipeline."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Iterable, Mapping, MutableMapping, Sequence

import requests

from experiments.data_sources import (
    AnchoringResult,
    DownloadConfig,
    download_selected_candidate,
    extract_anchors,
    serialise_dryad_candidates,
    serialise_figshare_candidates,
    serialise_osf_candidates,
    serialise_zenodo_candidates,
)
from experiments.data_sources.download import DownloadError, derive_dataset_slug
from experiments.data_sources.dryad import DryadSearchConfig, discover_dryad_candidates
from experiments.data_sources.figshare import FigshareSearchConfig, discover_figshare_candidates
from experiments.data_sources.osf import OSFSearchConfig, discover_osf_candidates
from experiments.data_sources.zenodo import ZenodoSearchConfig, discover_zenodo_candidates
from experiments.public_data import PROTOCOLS as PUBLIC_PROTOCOLS
from experiments.turbulence import PROTOCOLS as TURBULENCE_PROTOCOLS
from scripts.run_proofpack_pipeline import _load_profile_config, run_pipeline

SOURCE_MAP = {
    "osf": (
        OSFSearchConfig,
        discover_osf_candidates,
        serialise_osf_candidates,
        ['"optical tweezers"', '"single particle tracking"', '"Brownian"', '"MSD"'],
    ),
    "figshare": (
        FigshareSearchConfig,
        discover_figshare_candidates,
        serialise_figshare_candidates,
        ['"optical tweezers"', '"single particle tracking"', '"Brownian motion"'],
    ),
    "dryad": (
        DryadSearchConfig,
        discover_dryad_candidates,
        serialise_dryad_candidates,
        ['"optical tweezers"', '"single-molecule"', '"single particle tracking"', '"Brownian"'],
    ),
    "zenodo": (
        ZenodoSearchConfig,
        discover_zenodo_candidates,
        serialise_zenodo_candidates,
        ['"optical tweezers"', '"single particle tracking"', '"Brownian"'],
    ),
}


def _extract_text_fields(candidate: Mapping[str, object], keys: Sequence[str]) -> list[str]:
    lines: list[str] = []
    for key in keys:
        value = candidate.get(key)
        if isinstance(value, str):
            lines.extend(value.splitlines())
        elif isinstance(value, Mapping):
            for element in value.values():
                if isinstance(element, str):
                    lines.extend(element.splitlines())
        elif isinstance(value, Iterable):
            for element in value:
                if isinstance(element, str):
                    lines.extend(element.splitlines())
    return lines


def _filter_candidates(payload: Mapping[str, object], *, metadata_keys: Sequence[str], limit: int | None) -> dict:
    candidates = payload.get("candidates", [])
    selected: list[dict] = []
    for candidate in candidates:
        if not isinstance(candidate, Mapping):
            continue
        lines = _extract_text_fields(candidate, metadata_keys)
        anchors: AnchoringResult = extract_anchors(lines)
        if not anchors.is_complete():
            continue
        entry: MutableMapping[str, object] = {
            "candidate": dict(candidate),
            "anchors": {
                "T_K": anchors.temperature.value if anchors.temperature else None,
                "pixel_scale_um_per_px": anchors.pixel_scale.value if anchors.pixel_scale else None,
                "frame_interval_s": anchors.frame_interval.value if anchors.frame_interval else None,
            },
        }
        if anchors.temperature:
            entry["anchors"]["temperature_verbatim"] = anchors.temperature.verbatim
        if anchors.pixel_scale:
            entry["anchors"]["pixel_scale_verbatim"] = anchors.pixel_scale.verbatim
        if anchors.frame_interval:
            entry["anchors"]["frame_interval_verbatim"] = anchors.frame_interval.verbatim
        if anchors.bead_radius:
            entry["anchors"]["bead_radius_um"] = anchors.bead_radius.value
            entry["anchors"]["radius_verbatim"] = anchors.bead_radius.verbatim
        if anchors.viscosity:
            entry["anchors"]["viscosity_pa_s"] = anchors.viscosity.value
            entry["anchors"]["viscosity_verbatim"] = anchors.viscosity.verbatim
        selected.append(dict(entry))
        if limit is not None and len(selected) >= limit:
            break
    summary = {
        "input_candidates": len(candidates) if isinstance(candidates, Sequence) else 0,
        "selected_candidates": len(selected),
    }
    return {"summary": summary, "selected": selected}


def _download_datasets(
    selected: Sequence[Mapping[str, object]],
    *,
    source: str,
    mirror_root: Path,
    skip_download: bool,
    chunk_size: int,
    timeout: float,
) -> list[Path]:
    dataset_dirs: list[Path] = []
    if skip_download:
        for entry in selected:
            candidate = entry.get("candidate")
            if not isinstance(candidate, Mapping):
                continue
            slug = derive_dataset_slug(source, dict(candidate))
            dataset_dir = mirror_root / source / slug
            if not dataset_dir.exists():
                raise FileNotFoundError(f"Mirrored dataset missing: {dataset_dir}")
            dataset_dirs.append(dataset_dir)
        return dataset_dirs

    config = DownloadConfig(base_dir=mirror_root, chunk_size=chunk_size, request_timeout=timeout)
    with requests.Session() as session:
        for entry in selected:
            outcome = download_selected_candidate(
                dict(entry),
                source=source,
                config=config,
                session=session,
            )
            dataset_dirs.append(outcome.dataset_dir)
    return dataset_dirs


def _parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", choices=sorted(SOURCE_MAP.keys()), default="osf")
    parser.add_argument("--output-root", type=Path, default=Path("artifacts") / "experiments")
    parser.add_argument("--mirror-root", type=Path, default=Path("public_data"))
    parser.add_argument("--signing-key", type=Path, default=Path("kernel_secret.key"))
    parser.add_argument("--run-tag", type=str)
    parser.add_argument("--profile", type=str, default="quick")
    parser.add_argument("--profile-config", type=Path)
    parser.add_argument("--note", dest="notes", action="append")
    parser.add_argument("--created-at", type=str)
    parser.add_argument("--queries", nargs="*")
    parser.add_argument("--candidates", type=Path, help="Optional pre-fetched candidates JSON")
    parser.add_argument("--candidates-output", type=Path)
    parser.add_argument("--selected-output", type=Path)
    parser.add_argument("--skip-download", action="store_true")
    parser.add_argument("--max-datasets", type=int, default=1)
    parser.add_argument("--chunk-size", type=int, default=64 * 1024)
    parser.add_argument("--timeout", type=float, default=30.0)
    parser.add_argument("--public-data-protocol", dest="public_protocols", action="append", choices=PUBLIC_PROTOCOLS)
    parser.add_argument("--public-data-seed", type=int, default=0)
    parser.add_argument("--epsilon", type=float, default=0.05)
    parser.add_argument("--delta", type=float, default=0.05)
    parser.add_argument("--eta", type=float, default=0.05)
    parser.add_argument("--delta-aic", type=float, default=10.0)
    parser.add_argument(
        "--turbulence-protocol",
        dest="turbulence_protocols",
        action="append",
        choices=TURBULENCE_PROTOCOLS,
    )
    parser.add_argument("--turbulence-seed", type=int, default=0)
    parser.add_argument(
        "--turbulence-dataset",
        dest="turbulence_datasets",
        action="append",
        help="Restrict turbulence execution to mirrored dataset slugs",
    )
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = _parse_args(argv)
    config_cls, discover, serialise, default_queries = SOURCE_MAP[args.source]

    if args.candidates and args.candidates.exists():
        candidates_payload = json.loads(args.candidates.read_text(encoding="utf-8"))
    else:
        search_kwargs = {
            "queries": args.queries or list(default_queries),
        }
        config = config_cls(**search_kwargs)  # type: ignore[arg-type]
        candidates, summary = discover(config)  # type: ignore[arg-type]
        document = serialise(candidates, summary)
        candidates_payload = json.loads(document)
        if args.candidates_output:
            args.candidates_output.write_text(document, encoding="utf-8")

    selected_payload = _filter_candidates(
        candidates_payload,
        metadata_keys=("description", "notes", "metadata"),
        limit=args.max_datasets,
    )
    if args.selected_output:
        args.selected_output.write_text(json.dumps(selected_payload, indent=2, sort_keys=True), encoding="utf-8")

    selected_entries = selected_payload.get("selected", [])
    if not selected_entries:
        print(
            json.dumps(
                {
                    "error": "no_anchored_datasets",
                    "candidates": selected_payload.get("summary", {}),
                },
                sort_keys=True,
            )
        )
        return 1

    try:
        dataset_dirs = _download_datasets(
            selected_entries,
            source=args.source,
            mirror_root=args.mirror_root,
            skip_download=args.skip_download,
            chunk_size=args.chunk_size,
            timeout=args.timeout,
        )
    except (DownloadError, FileNotFoundError) as exc:
        print(
            json.dumps(
                {"error": "download_failed", "message": str(exc)},
                sort_keys=True,
            )
        )
        return 1

    profile_args = _load_profile_config(args.profile_config) if args.profile_config else None

    try:
        pipeline_result = run_pipeline(
            output_root=args.output_root,
            signing_key=args.signing_key,
            run_tag=args.run_tag,
            profile=args.profile,
            profile_arguments=profile_args,
            notes=args.notes,
            created_at=args.created_at,
            epsilon=args.epsilon,
            delta=args.delta,
            eta=args.eta,
            delta_aic=args.delta_aic,
            public_data_root=args.mirror_root,
            public_data_protocols=args.public_protocols,
            public_data_seed=args.public_data_seed,
            turbulence_protocols=args.turbulence_protocols,
            turbulence_seed=args.turbulence_seed,
            turbulence_datasets=args.turbulence_datasets,
        )
    except Exception as exc:  # pragma: no cover - surfaced in tests
        print(
            json.dumps(
                {"error": "pipeline_failed", "message": str(exc)},
                sort_keys=True,
            )
        )
        return 1

    manifest = json.loads(pipeline_result.bundle_result.manifest_path.read_text(encoding="utf-8"))
    summary = {
        "source": args.source,
        "candidates_considered": candidates_payload.get("summary", {}).get("candidate_count")
        or candidates_payload.get("summary", {}).get("total_results"),
        "selected_count": len(selected_entries),
        "downloaded_count": len(dataset_dirs),
        "run_tag": pipeline_result.run_tag,
        "manifest_digest": manifest.get("manifest_digest_sha256"),
        "bundle_dir": str(pipeline_result.bundle_dir),
        "proofpack_dir": str(pipeline_result.proofpack_dir),
    }
    print(json.dumps(summary, sort_keys=True))
    return 0


if __name__ == "__main__":  # pragma: no cover - CLI entry
    raise SystemExit(main())
