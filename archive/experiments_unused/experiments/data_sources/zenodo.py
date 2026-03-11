"""Zenodo dataset discovery helpers for the Thiele proofpack pipeline."""

from __future__ import annotations

import dataclasses
import datetime as _dt
from datetime import UTC
import json
import time
from pathlib import Path
from typing import Any, Dict, Iterator, List, Optional, Sequence, Tuple

import requests

__all__ = [
    "ZenodoFile",
    "ZenodoCandidate",
    "ZenodoSearchConfig",
    "discover_zenodo_candidates",
    "serialise_candidates",
]

API_ROOT = "https://zenodo.org/api"
_ALLOWED_EXTENSIONS = {
    ".csv",
    ".tsv",
    ".h5",
    ".hdf5",
    ".mat",
    ".tif",
    ".tiff",
    ".zip",
    ".json",
}


@dataclasses.dataclass(frozen=True)
class ZenodoFile:
    """Metadata about a Zenodo file entry."""

    file_id: str
    name: str
    size: Optional[int]
    download_url: Optional[str]
    checksum: Optional[str]

    @property
    def extension(self) -> str:
        return Path(self.name).suffix.lower()


@dataclasses.dataclass(frozen=True)
class ZenodoCandidate:
    """Grouped Zenodo record that exposes potentially relevant files."""

    record_id: int
    doi: Optional[str]
    title: Optional[str]
    url: Optional[str]
    description: Optional[str]
    creators: Tuple[str, ...]
    files: Tuple[ZenodoFile, ...]
    query_hits: Tuple[str, ...]

    def to_dict(self) -> Dict[str, Any]:
        return {
            "record_id": self.record_id,
            "doi": self.doi,
            "title": self.title,
            "url": self.url,
            "description": self.description,
            "creators": list(self.creators),
            "files": [dataclasses.asdict(f) for f in self.files],
            "query_hits": list(self.query_hits),
        }


@dataclasses.dataclass
class ZenodoSearchConfig:
    """Configuration for Zenodo discovery."""

    queries: Sequence[str]
    allowed_extensions: Sequence[str] = tuple(sorted(_ALLOWED_EXTENSIONS))
    max_pages: int = 5
    page_size: int = 100
    per_query_limit: int = 200
    request_timeout: float = 20.0
    inter_request_pause: float = 0.25

    def extension_set(self) -> set[str]:
        return {ext.lower() for ext in self.allowed_extensions}


class ZenodoDiscoveryError(RuntimeError):
    """Raised when the Zenodo API cannot be queried."""


def _iter_search_hits(
    session: requests.Session,
    query: str,
    config: ZenodoSearchConfig,
) -> Iterator[Dict[str, Any]]:
    """Yield search hits for a given Zenodo query."""

    page = 1
    fetched = 0
    while page <= config.max_pages and fetched < config.per_query_limit:
        params = {
            "q": query,
            "size": config.page_size,
            "page": page,
        }
        response = session.get(
            f"{API_ROOT}/records",
            params=params,
            timeout=config.request_timeout,
        )
        if response.status_code >= 400:
            raise ZenodoDiscoveryError(
                f"Zenodo search failed with {response.status_code}: {response.text[:200]}"
            )
        payload = response.json()
        hits = payload.get("hits", {}).get("hits", [])
        if not hits:
            break
        for hit in hits:
            yield hit
            fetched += 1
            if fetched >= config.per_query_limit:
                break
        if fetched >= config.per_query_limit:
            break
        total_hits = payload.get("hits", {}).get("total", 0)
        if page * config.page_size >= total_hits:
            break
        page += 1
        if page <= config.max_pages:
            time.sleep(config.inter_request_pause)


def discover_zenodo_candidates(
    config: ZenodoSearchConfig,
    session: Optional[requests.Session] = None,
) -> Tuple[List[ZenodoCandidate], Dict[str, Any]]:
    """Run the Zenodo discovery pipeline and return candidates with summary stats."""

    if session is None:
        session = requests.Session()

    allowed = config.extension_set()
    grouped: Dict[int, Dict[str, Any]] = {}

    for query in config.queries:
        for hit in _iter_search_hits(session, query, config):
            record_id = hit.get("id")
            if record_id is None:
                continue
            record_id = int(record_id)
            entry = grouped.setdefault(
                record_id,
                {
                    "hit": hit,
                    "query_hits": set(),
                },
            )
            entry["query_hits"].add(query)

    candidates: List[ZenodoCandidate] = []
    for record_id, info in grouped.items():
        hit = info.get("hit") or {}
        metadata = hit.get("metadata", {})
        files: List[ZenodoFile] = []
        for file_info in hit.get("files", []) or []:
            name = file_info.get("key")
            if not name:
                continue
            ext = Path(name).suffix.lower()
            if ext not in allowed:
                continue
            files.append(
                ZenodoFile(
                    file_id=str(file_info.get("id")),
                    name=name,
                    size=file_info.get("size"),
                    download_url=file_info.get("links", {}).get("self"),
                    checksum=file_info.get("checksum"),
                )
            )
        if not files:
            continue
        creators: List[str] = []
        for creator in metadata.get("creators", []) or []:
            if isinstance(creator, dict):
                name = creator.get("name") or creator.get("family")
            else:
                name = str(creator)
            if name:
                creators.append(name)
        candidate = ZenodoCandidate(
            record_id=record_id,
            doi=metadata.get("doi") or hit.get("doi"),
            title=metadata.get("title"),
            url=hit.get("links", {}).get("html"),
            description=metadata.get("description"),
            creators=tuple(creators),
            files=tuple(sorted(files, key=lambda f: f.name.lower())),
            query_hits=tuple(sorted(info["query_hits"])),
        )
        candidates.append(candidate)

    candidates.sort(key=lambda c: (c.title or "", c.record_id))

    summary = {
        "generated_at": _dt.datetime.now(UTC).isoformat().replace("+00:00", "Z"),
        "query_count": len(config.queries),
        "candidate_count": len(candidates),
        "unique_records": len({c.record_id for c in candidates}),
    }

    return candidates, summary


def serialise_candidates(
    candidates: Sequence[ZenodoCandidate],
    summary: Dict[str, Any],
    *,
    indent: int = 2,
) -> str:
    """Return a JSON document representing the discovery results."""

    payload = {
        "summary": summary,
        "candidates": [candidate.to_dict() for candidate in candidates],
    }
    return json.dumps(payload, indent=indent, sort_keys=True)
