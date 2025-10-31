"""Render a Markdown digest history dashboard from proofpack smoke runs."""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Iterable, Sequence

DEFAULT_HISTORY_PATH = Path("artifacts") / "digests" / "history.json"
DEFAULT_OUTPUT_PATH = Path("docs") / "digest_history.md"
DEFAULT_LIMIT = 20


@dataclass(frozen=True)
class HistoryRecord:
    run_tag: str
    manifest_digest_sha256: str
    updated: str
    timestamp: datetime


def _parse_timestamp(value: str) -> datetime:
    try:
        return datetime.fromisoformat(value.replace("Z", "+00:00"))
    except ValueError:
        return datetime.fromtimestamp(0, tz=timezone.utc)


def _load_history(path: Path) -> list[HistoryRecord]:
    if not path.exists():
        return []
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, list):
        raise ValueError("History file must contain a JSON array")

    records: list[HistoryRecord] = []
    for entry in data:
        if not isinstance(entry, dict):
            continue
        run_tag = entry.get("run_tag")
        digest = entry.get("manifest_digest_sha256") or entry.get("digest")
        updated = entry.get("updated")
        if isinstance(run_tag, str) and isinstance(digest, str) and isinstance(updated, str):
            records.append(
                HistoryRecord(
                    run_tag=run_tag,
                    manifest_digest_sha256=digest,
                    updated=updated,
                    timestamp=_parse_timestamp(updated),
                )
            )
    records.sort(key=lambda record: record.timestamp, reverse=True)
    return records


def _render_table(records: Sequence[HistoryRecord]) -> list[str]:
    lines = ["| Run tag | manifest_digest_sha256 | Updated |", "| --- | --- | --- |"]
    for record in records:
        lines.append(
            f"| {record.run_tag} | {record.manifest_digest_sha256} | {record.updated} |"
        )
    return lines


def _render_summary(records: Sequence[HistoryRecord]) -> str:
    if not records:
        return "**Digest history:** runs=0, unique_digests=0, last_updated=NA."
    unique_digests = {record.manifest_digest_sha256 for record in records}
    latest = max(records, key=lambda record: record.timestamp)
    return (
        "**Digest history:** "
        f"runs={len(records)}, unique_digests={len(unique_digests)}, last_updated={latest.updated}."
    )


def render_digest_history(
    history_path: Path,
    output_path: Path,
    *,
    limit: int = DEFAULT_LIMIT,
    generated_at: datetime | None = None,
) -> Path:
    output_path.parent.mkdir(parents=True, exist_ok=True)
    records = _load_history(history_path)
    generated = (generated_at or datetime.now(timezone.utc)).replace(microsecond=0)
    lines: list[str] = [
        "# Proofpack smoke digest history",
        "",
        f"Generated from `{history_path}` at {generated.isoformat().replace('+00:00', 'Z')}.",
        "",
    ]

    if not records:
        lines.append("No manifest digests recorded yet. Run `scripts/update_smoke_digest.py` to seed the history.")
    else:
        lines.extend(_render_table(records[: max(limit, 0)]))
        lines.append("")
        lines.append(_render_summary(records))

    output_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return output_path


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--history", type=Path, default=DEFAULT_HISTORY_PATH)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT_PATH)
    parser.add_argument("--limit", type=int, default=DEFAULT_LIMIT)
    return parser


def main(argv: Iterable[str] | None = None) -> int:  # pragma: no cover - CLI wrapper
    parser = _build_parser()
    args = parser.parse_args(list(argv) if argv is not None else None)
    render_digest_history(args.history, args.output, limit=args.limit)
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
