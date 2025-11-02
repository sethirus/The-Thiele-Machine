"""CLI utilities for bundling verified proofpacks into archive directories."""

from __future__ import annotations

import argparse
import json
import shutil
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, MutableMapping, Sequence

from experiments import proofpack
from tools.thiele_verifier import verify_proofpack


DEFAULT_INCLUDE_PATTERNS: Sequence[str] = (
    "**/*_metadata.json",
    "**/*_summary.csv",
    "**/*_steps.jsonl",
    "**/plots/*.svg",
    "verifier/*.json",
)


@dataclass
class BundleResult:
    summary_path: Path
    protocol_path: Path
    manifest_path: Path
    receipt_path: Path
    attachments: Sequence[Path]
    aggregated_payload: MutableMapping[str, object]
    human_summary_path: Path


def _resolve_patterns(run_dir: Path, patterns: Sequence[str]) -> list[Path]:
    attachments: set[Path] = set()
    for pattern in patterns:
        for candidate in run_dir.glob(pattern):
            if candidate.is_file():
                attachments.add(candidate.resolve())
    return sorted(attachments)


def _copy_attachment(run_dir: Path, destination_root: Path, path: Path) -> Path:
    try:
        relative = path.resolve().relative_to(run_dir.resolve())
    except ValueError as exc:  # pragma: no cover - defensive guard
        raise ValueError(f"Attachment outside run directory: {path}") from exc
    target = destination_root / relative
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(path, target)
    return target


def _enforce_artifact_layout(path: Path) -> Path:
    resolved = Path(path).resolve()
    parts = resolved.parts
    try:
        idx = parts.index("artifacts")
    except ValueError as exc:  # pragma: no cover - defensive guard
        raise ValueError("Bundle output must live under artifacts/experiments/<tag>/...") from exc
    if idx + 1 >= len(parts) or parts[idx + 1] != "experiments":
        raise ValueError("Bundle output must live under artifacts/experiments/<tag>/...")
    if idx + 2 >= len(parts):
        raise ValueError("Bundle output must include a run tag directory")
    return resolved


def bundle_proofpack(
    run_dir: Path,
    output_dir: Path,
    *,
    signing_key_path: Path,
    run_tag: str | None = None,
    include_patterns: Sequence[str] | None = None,
    extra_attachments: Sequence[Path] | None = None,
    notes: Sequence[str] | None = None,
    created_at: str | None = None,
    epsilon: float = 0.05,
    delta: float = 0.05,
    eta: float = 0.05,
    delta_aic: float = 10.0,
    spearman_threshold: float = 0.9,
    pvalue_threshold: float = 1e-6,
    oos_threshold: float = 0.1,
) -> BundleResult:
    """Bundle a verified proofpack directory into an archivist-friendly layout."""

    run_dir = Path(run_dir).resolve()
    output_dir = _enforce_artifact_layout(output_dir)

    try:
        aggregated = verify_proofpack(
            run_dir,
            epsilon=epsilon,
            delta=delta,
            eta=eta,
            delta_aic=delta_aic,
            spearman_threshold=spearman_threshold,
            pvalue_threshold=pvalue_threshold,
            oos_threshold=oos_threshold,
        )
    except Exception as exc:  # pragma: no cover - surfaced in tests via failure path
        raise RuntimeError(f"Verifier invocation failed: {exc}") from exc

    if not aggregated.get("status"):
        raise RuntimeError("Proofpack verification failed; aborting bundle generation")

    output_dir.mkdir(parents=True, exist_ok=True)
    artefact_root = output_dir / "artefacts"
    artefact_root.mkdir(parents=True, exist_ok=True)

    patterns = list(DEFAULT_INCLUDE_PATTERNS)
    if include_patterns:
        patterns.extend(include_patterns)

    attachments = _resolve_patterns(run_dir, patterns)

    if extra_attachments:
        for extra in extra_attachments:
            extra_path = Path(extra)
            if not extra_path.is_absolute():
                extra_path = run_dir / extra_path
            if extra_path.is_file():
                attachments.append(extra_path.resolve())

    verifier_payload = run_dir / "verifier" / "proofpack_verifier.json"
    if verifier_payload.is_file():
        attachments.append(verifier_payload.resolve())

    # Deduplicate while preserving deterministic order
    unique_attachments: list[Path] = []
    seen: set[Path] = set()
    for attachment in sorted(attachments):
        if attachment in seen:
            continue
        seen.add(attachment)
        unique_attachments.append(attachment)

    copied_paths = [
        _copy_attachment(run_dir, artefact_root, attachment) for attachment in unique_attachments
    ]

    summary_payload = proofpack.build_summary_payload(aggregated)
    summary_path = proofpack.write_summary(summary_payload, output_dir / "summary.json")

    thresholds = {
        "epsilon": aggregated.get("epsilon"),
        "delta": aggregated.get("delta"),
        "eta": aggregated.get("eta"),
        "delta_aic": aggregated.get("delta_aic"),
    }
    protocol_notes = list(notes) if notes else ["Bundled with tools.proofpack_bundler"]

    protocol_path = proofpack.write_protocol_document(
        thresholds,
        output_dir / "protocol.json",
        notes=protocol_notes,
    )

    manifest_path = output_dir / "manifest.json"
    existing_created_at = None
    existing_run_tag = None
    if manifest_path.exists():
        with manifest_path.open("r", encoding="utf-8") as handle:
            manifest_data = json.load(handle)
        existing_created_at = manifest_data.get("created_at")
        existing_run_tag = manifest_data.get("run_tag")

    run_tag_value = run_tag or existing_run_tag or run_dir.name

    manifest_entries = proofpack.collect_manifest_entries(
        output_dir,
        [summary_path, protocol_path, *copied_paths],
    )

    manifest_path = proofpack.write_manifest(
        output_dir,
        manifest_entries,
        run_tag=run_tag_value,
        metadata={"attachment_count": len(copied_paths)},
        out_path=manifest_path,
        created_at=created_at or existing_created_at,
    )

    manifest_payload = json.loads(manifest_path.read_text(encoding="utf-8"))

    human_summary_text = proofpack.render_human_summary(
        aggregated,
        manifest_payload,
        protocol_notes=protocol_notes,
    )
    human_summary_path = proofpack.write_human_summary(
        human_summary_text,
        output_dir / "summary.md",
    )

    signer = proofpack.ReceiptSigner.load(Path(signing_key_path))
    receipt_path = proofpack.write_receipt(
        manifest_entries,
        signer,
        manifest_digest=manifest_payload["manifest_digest_sha256"],
        run_tag=run_tag_value,
        out_path=output_dir / "receipt.json",
    )

    return BundleResult(
        summary_path=summary_path,
        protocol_path=protocol_path,
        manifest_path=manifest_path,
        receipt_path=receipt_path,
        attachments=copied_paths,
        aggregated_payload=aggregated,
        human_summary_path=human_summary_path,
    )


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Bundle verified proofpacks into archives")
    parser.add_argument("run_dir", type=Path, help="Directory containing builder outputs")
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=None,
        help="Directory that will receive summary, protocol, manifest, and receipt",
    )
    parser.add_argument(
        "--signing-key",
        type=Path,
        required=True,
        help="Path to Ed25519 private key used for signing receipts",
    )
    parser.add_argument("--run-tag", type=str, default=None, help="Run tag recorded in manifest")
    parser.add_argument(
        "--include",
        action="append",
        dest="include_patterns",
        help="Additional glob patterns (relative to run_dir) to include in the bundle",
    )
    parser.add_argument(
        "--extra",
        action="append",
        dest="extra_attachments",
        help="Additional file paths (relative to run_dir) to copy into the bundle",
    )
    parser.add_argument(
        "--note",
        action="append",
        dest="notes",
        help="Additional protocol notes to embed in protocol.json",
    )
    parser.add_argument(
        "--created-at",
        type=str,
        default=None,
        help="Override manifest timestamp (ISO-8601)",
    )
    parser.add_argument("--epsilon", type=float, default=0.05, help="Landauer/CWD tolerance")
    parser.add_argument("--delta", type=float, default=0.05, help="Einstein tolerance")
    parser.add_argument("--eta", type=float, default=0.05, help="CWD penalty margin")
    parser.add_argument(
        "--delta-aic",
        type=float,
        default=10.0,
        dest="delta_aic",
        help="ΔAIC threshold for blind cross-domain runs",
    )
    parser.add_argument(
        "--spearman-threshold",
        type=float,
        default=0.9,
        help="Minimum Spearman ρ for public-data proofpacks",
    )
    parser.add_argument(
        "--spearman-p-threshold",
        type=float,
        default=1e-6,
        dest="pvalue_threshold",
        help="Maximum Spearman p-value for public-data proofpacks",
    )
    parser.add_argument(
        "--oos-threshold",
        type=float,
        default=0.1,
        help="Maximum median absolute percent error for public-data OOS predictions",
    )
    return parser


def main(argv: Iterable[str] | None = None) -> None:  # pragma: no cover - CLI wrapper
    parser = _build_parser()
    args = parser.parse_args(argv)

    run_dir = Path(args.run_dir).resolve()
    output_dir = Path(args.output_dir) if args.output_dir else (run_dir / "proofpack_bundle")

    try:
        result = bundle_proofpack(
            run_dir,
            output_dir,
            signing_key_path=args.signing_key,
            run_tag=args.run_tag,
            include_patterns=args.include_patterns or None,
            extra_attachments=[Path(p) for p in args.extra_attachments] if args.extra_attachments else None,
            notes=args.notes or None,
            created_at=args.created_at,
            epsilon=args.epsilon,
            delta=args.delta,
            eta=args.eta,
            delta_aic=args.delta_aic,
            spearman_threshold=args.spearman_threshold,
            pvalue_threshold=args.pvalue_threshold,
            oos_threshold=args.oos_threshold,
        )
    except Exception as exc:
        print(f"BUNDLE_FAIL: {exc}")
        raise SystemExit(1)

    print(f"BUNDLE_OK: {result.manifest_path.parent}")
    print(f"SUMMARY_MD: {result.human_summary_path}")


if __name__ == "__main__":  # pragma: no cover
    main()

