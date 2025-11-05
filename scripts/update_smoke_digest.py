"""Update the proofpack smoke manifest digest table in RESULTS.md."""

from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Mapping, Sequence, Tuple

DEFAULT_HISTORY_PATH = Path("artifacts") / "digests" / "history.json"
HISTORY_LIMIT = 50


def _current_timestamp() -> str:
    now = datetime.now(timezone.utc)
    return now.replace(microsecond=0).isoformat().replace("+00:00", "Z")


def _normalise_row(run_tag: str, digest: str, updated: str) -> str:
    return f"| {run_tag} | {digest} | {updated} |"


def _table_bounds(lines: list[str]) -> Tuple[int, int]:
    header = "| Run tag | manifest_digest_sha256 | Updated |"
    try:
        header_index = lines.index(header)
    except ValueError:
        # Table is missing entirely; append a fresh skeleton at the end of the
        # document so callers can continue updating it.
        if lines and lines[-1].strip():
            lines.append("")
        lines.extend([header, "| --- | --- | --- |"])
        header_index = len(lines) - 2

    separator_index = header_index + 1
    if separator_index >= len(lines) or not lines[separator_index].startswith("| ---"):
        raise ValueError("Manifest digest table separator missing in RESULTS.md")

    start = separator_index + 1
    end = len(lines)
    for index in range(start, len(lines)):
        if not lines[index].strip().startswith("|"):
            end = index
            break
    return start, end


def _update_table(lines: list[str], run_tag: str, digest: str, updated: str) -> Tuple[list[str], Tuple[int, int]]:
    start, end = _table_bounds(lines)
    for index in range(start, end):
        cells = [cell.strip() for cell in lines[index].strip().strip("|").split("|")]
        if len(cells) >= 3 and cells[0] in {run_tag, "_pending_"}:
            lines[index] = _normalise_row(run_tag, digest, updated)
            return lines, (start, end)

    insertion = _normalise_row(run_tag, digest, updated)
    lines.insert(end, insertion)
    return lines, (start, end + 1)


def _parse_rows(lines: list[str], bounds: Tuple[int, int]) -> list[tuple[str, str, str]]:
    start, end = bounds
    rows: list[tuple[str, str, str]] = []
    for index in range(start, end):
        line = lines[index].strip()
        if not line.startswith("|"):
            continue
        cells = [cell.strip() for cell in line.strip("|").split("|")]
        if len(cells) >= 3 and cells[0] not in {"Run tag", "---", ""}:
            rows.append((cells[0], cells[1], cells[2]))
    return rows


def _update_summary(lines: list[str], bounds: Tuple[int, int]) -> list[str]:
    rows = _parse_rows(lines, bounds)
    prefix = "**Digest history:**"
    if not rows:
        summary = f"{prefix} runs=0, unique_digests=0, last_updated=NA."
    else:
        unique_digests = {digest for _, digest, _ in rows}
        last_updated = max(updated for *_, updated in rows)
        summary = (
            f"{prefix} runs={len(rows)}, unique_digests={len(unique_digests)}, "
            f"last_updated={last_updated}."
        )

    _, end = bounds
    for index in range(end, len(lines)):
        if lines[index].startswith(prefix):
            lines[index] = summary
            return lines
        if lines[index].strip():
            break

    if end > 0 and (end == len(lines) or lines[end - 1].strip()):
        lines.insert(end, "")
        end += 1

    lines.insert(end, summary)
    return lines


def _load_history(path: Path) -> list[dict[str, str]]:
    if not path.exists():
        return []
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, list):
        raise ValueError("History file must contain a JSON array")
    records: list[dict[str, str]] = []
    for entry in data:
        if not isinstance(entry, Mapping):
            continue
        run_tag = entry.get("run_tag")
        digest = entry.get("manifest_digest_sha256") or entry.get("digest")
        updated = entry.get("updated")
        if isinstance(run_tag, str) and isinstance(digest, str) and isinstance(updated, str):
            records.append(
                {
                    "run_tag": run_tag,
                    "manifest_digest_sha256": digest,
                    "updated": updated,
                }
            )
    return records


def _update_history(path: Path, run_tag: str, digest: str, updated: str) -> None:
    entries = [entry for entry in _load_history(path) if entry["run_tag"] != run_tag]
    entries.append(
        {
            "run_tag": run_tag,
            "manifest_digest_sha256": digest,
            "updated": updated,
        }
    )
    entries = sorted(entries, key=lambda entry: (entry["updated"], entry["run_tag"]))[-HISTORY_LIMIT:]
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(entries, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def update_results(
    results_path: Path,
    run_tag: str,
    digest: str,
    updated: str | None = None,
    *,
    history_path: Path | None = None,
) -> None:
    updated_stamp = updated or _current_timestamp()
    text = results_path.read_text(encoding="utf-8")
    lines = text.splitlines()
    updated_lines, bounds = _update_table(lines, run_tag, digest, updated_stamp)
    updated_lines = _update_summary(updated_lines, bounds)
    results_path.write_text("\n".join(updated_lines) + "\n", encoding="utf-8")

    if history_path is not None:
        _update_history(history_path, run_tag, digest, updated_stamp)


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--results", type=Path, default=Path("RESULTS.md"))
    parser.add_argument("--history", type=Path, default=DEFAULT_HISTORY_PATH)
    parser.add_argument("--run-tag", required=True)
    parser.add_argument("--digest", required=True)
    parser.add_argument("--updated")
    return parser


def main(argv: Sequence[str] | None = None) -> int:  # pragma: no cover - CLI wrapper
    parser = _build_parser()
    args = parser.parse_args(argv)
    update_results(
        args.results,
        args.run_tag,
        args.digest,
        args.updated,
        history_path=args.history,
    )
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())

