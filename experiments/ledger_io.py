"""Deterministic μ-ledger load/store helpers.

This module provides a small set of utilities for reading and writing the
JSONL-style μ-ledger captures used throughout the zero-trust experiment
pipeline.  Builders are expected to log one JSON object per line with the
fields required by the verifiers (`step`, `module`, `mu_answer`, `work`,
etc.), while Auditors and Archivists need deterministic replays to compute
hashes and digests.

The helpers below avoid dynamic code generation or complex dependencies so
they can be imported by both experiment runners and verifiers without
introducing hidden state.  All serialization paths normalise keys to ensure
stable hashing.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
from typing import Any, Iterable, Iterator, List, Mapping, MutableMapping, Sequence


LedgerRow = MutableMapping[str, Any]


@dataclass(frozen=True)
class LedgerEntry:
    """In-memory representation of a single μ-ledger row.

    Parameters
    ----------
    payload:
        Canonicalised dictionary that mirrors the JSON object stored on disk.
        Keys are sorted and nested dictionaries are recursively normalised.
        Lists are preserved in order because experiment logs rely on
        positional semantics (e.g. module ordering).
    """

    payload: Mapping[str, Any]

    def __getitem__(self, key: str) -> Any:  # pragma: no cover - simple proxy
        return self.payload[key]

    def get(self, key: str, default: Any = None) -> Any:  # pragma: no cover
        return self.payload.get(key, default)


def _normalise(obj: Any) -> Any:
    """Recursively normalise dictionaries for deterministic hashing."""

    if isinstance(obj, dict):
        return {k: _normalise(obj[k]) for k in sorted(obj)}
    if isinstance(obj, list):
        return [_normalise(item) for item in obj]
    return obj


def load_ledger(path: Path | str) -> List[LedgerEntry]:
    """Load a JSONL ledger capture into canonicalised entries."""

    ledger_path = Path(path)
    entries: List[LedgerEntry] = []
    with ledger_path.open("r", encoding="utf-8") as handle:
        for line_number, line in enumerate(handle, start=1):
            stripped = line.strip()
            if not stripped:
                continue
            try:
                raw: LedgerRow = json.loads(stripped)
            except json.JSONDecodeError as exc:  # pragma: no cover - defensive
                raise ValueError(f"Invalid JSON on line {line_number}: {exc}") from exc
            entries.append(LedgerEntry(payload=_normalise(raw)))
    return entries


def iter_ledger(path: Path | str) -> Iterator[LedgerEntry]:
    """Yield ledger entries lazily without materialising the entire file."""

    ledger_path = Path(path)
    with ledger_path.open("r", encoding="utf-8") as handle:
        for line_number, line in enumerate(handle, start=1):
            stripped = line.strip()
            if not stripped:
                continue
            raw: LedgerRow = json.loads(stripped)
            yield LedgerEntry(payload=_normalise(raw))


def dump_ledger(entries: Iterable[Mapping[str, Any]], path: Path | str) -> None:
    """Write canonicalised ledger rows to disk in JSONL format."""

    ledger_path = Path(path)
    ledger_path.parent.mkdir(parents=True, exist_ok=True)
    with ledger_path.open("w", encoding="utf-8") as handle:
        for row in entries:
            handle.write(json.dumps(_normalise(dict(row)), separators=(",", ":")))
            handle.write("\n")


def ledger_digest(entries: Sequence[LedgerEntry]) -> str:
    """Return a SHA-256 digest of the ledger payloads.

    The digest is computed over UTF-8 JSON encodings with sorted keys so that
    repeated loads and dumps are byte-stable.
    """

    digest = hashlib.sha256()
    for entry in entries:
        digest.update(
            json.dumps(entry.payload, separators=(",", ":"), sort_keys=True).encode("utf-8")
        )
        digest.update(b"\n")
    return digest.hexdigest()


def ledger_summary(entries: Sequence[LedgerEntry], key: str) -> float:
    """Convenience helper that sums a numerical field across the ledger."""

    total = 0.0
    for entry in entries:
        value = entry.payload.get(key)
        if value is None:
            continue
        total += float(value)
    return total


__all__ = [
    "LedgerEntry",
    "dump_ledger",
    "iter_ledger",
    "ledger_digest",
    "ledger_summary",
    "load_ledger",
]

