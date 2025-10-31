"""Figshare dataset discovery helpers for the Thiele proofpack pipeline."""

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
    "FigshareFile",
    "FigshareCandidate",
    "FigshareSearchConfig",
    "discover_figshare_candidates",
    "serialise_candidates",
]

API_ROOT = "https://api.figshare.com/v2"
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
class FigshareFile:
    """Metadata about a Figshare file entry."""

    file_id: int
    name: str
    size: Optional[int]
    download_url: Optional[str]
    checksum: Optional[str]
    mimetype: Optional[str]

    @property
    def extension(self) -> str:
        return Path(self.name).suffix.lower()


@dataclasses.dataclass(frozen=True)
class FigshareCandidate:
    """Grouped Figshare record that exposes potentially relevant files."""

    article_id: int
    title: Optional[str]
    doi: Optional[str]
    url: Optional[str]
    description: Optional[str]
    tags: Tuple[str, ...]
    files: Tuple[FigshareFile, ...]
    query_hits: Tuple[str, ...]

    def to_dict(self) -> Dict[str, Any]:
        return {
            "article_id": self.article_id,
            "title": self.title,
            "doi": self.doi,
            "url": self.url,
            "description": self.description,
            "tags": list(self.tags),
            "files": [dataclasses.asdict(f) for f in self.files],
            "query_hits": list(self.query_hits),
        }


@dataclasses.dataclass
class FigshareSearchConfig:
    """Configuration for Figshare discovery."""

    queries: Sequence[str]
    allowed_extensions: Sequence[str] = tuple(sorted(_ALLOWED_EXTENSIONS))
    max_pages: int = 5
    page_size: int = 100
    per_query_limit: int = 250
    request_timeout: float = 20.0
    inter_request_pause: float = 0.25

    def extension_set(self) -> set[str]:
        return {ext.lower() for ext in self.allowed_extensions}


class FigshareDiscoveryError(RuntimeError):
    """Raised when the Figshare API cannot be queried."""


def _iter_search_hits(
    session: requests.Session,
    query: str,
    config: FigshareSearchConfig,
) -> Iterator[Dict[str, Any]]:
    """Yield raw search hits for a given Figshare query."""

    page = 1
    fetched = 0
    while page <= config.max_pages and fetched < config.per_query_limit:
        params = {
            "search_for": query,
            "page": page,
            "page_size": config.page_size,
        }
        response = session.get(
            f"{API_ROOT}/articles",
            params=params,
            timeout=config.request_timeout,
        )
        if response.status_code >= 400:
            raise FigshareDiscoveryError(
                f"Figshare search failed with {response.status_code}: {response.text[:200]}"
            )
        payload = response.json()
        if not isinstance(payload, list):
            break
        if not payload:
            break
        for hit in payload:
            yield hit
            fetched += 1
            if fetched >= config.per_query_limit:
                break
        if len(payload) < config.page_size:
            break
        page += 1
        if page <= config.max_pages:
            time.sleep(config.inter_request_pause)


def _safe_get(
    session: requests.Session,
    url: str,
    config: FigshareSearchConfig,
) -> Optional[Dict[str, Any]]:
    response = session.get(url, timeout=config.request_timeout)
    if response.status_code == 404:
        return None
    if response.status_code >= 400:
        raise FigshareDiscoveryError(f"Request to {url} failed with {response.status_code}")
    return response.json()


def _extract_files(
    detail: Dict[str, Any],
    allowed: set[str],
) -> List[FigshareFile]:
    files: List[FigshareFile] = []
    for file_info in detail.get("files", []) or []:
        name = file_info.get("name")
        if not name:
            continue
        ext = Path(name).suffix.lower()
        if ext not in allowed:
            continue
        files.append(
            FigshareFile(
                file_id=int(file_info.get("id", 0)),
                name=name,
                size=file_info.get("size"),
                download_url=file_info.get("download_url"),
                checksum=file_info.get("supplied_md5")
                or file_info.get("computed_md5"),
                mimetype=file_info.get("mimetype"),
            )
        )
    return files


def discover_figshare_candidates(
    config: FigshareSearchConfig,
    session: Optional[requests.Session] = None,
) -> Tuple[List[FigshareCandidate], Dict[str, Any]]:
    """Run the Figshare discovery pipeline and return candidates with summary stats."""

    if session is None:
        session = requests.Session()

    allowed = config.extension_set()
    grouped: Dict[int, Dict[str, Any]] = {}

    for query in config.queries:
        for hit in _iter_search_hits(session, query, config):
            article_id = hit.get("id")
            if article_id is None:
                continue
            article_id = int(article_id)
            entry = grouped.setdefault(
                article_id,
                {
                    "detail": None,
                    "query_hits": set(),
                },
            )
            entry["query_hits"].add(query)
            if entry["detail"] is None:
                detail = _safe_get(session, f"{API_ROOT}/articles/{article_id}", config)
                entry["detail"] = detail

    candidates: List[FigshareCandidate] = []
    for article_id, info in grouped.items():
        detail = info.get("detail") or {}
        files = tuple(sorted(_extract_files(detail, allowed), key=lambda f: f.name.lower()))
        if not files:
            continue
        metadata = detail or {}
        tags = metadata.get("tags") or []
        if isinstance(tags, dict):
            # Some records expose tags as mapping of tag -> count.
            tags = list(tags.keys())
        candidate = FigshareCandidate(
            article_id=article_id,
            title=metadata.get("title"),
            doi=metadata.get("doi"),
            url=metadata.get("url_public_html") or metadata.get("url"),
            description=metadata.get("description"),
            tags=tuple(sorted(t for t in tags if isinstance(t, str))),
            files=files,
            query_hits=tuple(sorted(info["query_hits"])),
        )
        candidates.append(candidate)

    candidates.sort(key=lambda c: (c.title or "", c.article_id))

    summary = {
        "generated_at": _dt.datetime.now(UTC).isoformat().replace("+00:00", "Z"),
        "query_count": len(config.queries),
        "candidate_count": len(candidates),
        "unique_articles": len({c.article_id for c in candidates}),
    }

    return candidates, summary


def serialise_candidates(
    candidates: Sequence[FigshareCandidate],
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
