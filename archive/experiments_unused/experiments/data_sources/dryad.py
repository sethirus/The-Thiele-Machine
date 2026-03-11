"""Dryad dataset discovery helpers for the Thiele proofpack pipeline."""

from __future__ import annotations

import dataclasses
import datetime as _dt
from datetime import UTC
import json
import time
from pathlib import Path
from typing import Any, Dict, Iterator, List, Optional, Sequence, Tuple
from urllib.parse import urljoin

import requests

__all__ = [
    "DryadFile",
    "DryadCandidate",
    "DryadSearchConfig",
    "discover_dryad_candidates",
    "serialise_candidates",
]

API_BASE = "https://datadryad.org"
API_ROOT = f"{API_BASE}/api/v2"
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
class DryadFile:
    """Metadata about a Dryad file entry."""

    file_id: int
    name: str
    size: Optional[int]
    download_url: Optional[str]
    checksum: Optional[str]
    checksum_type: Optional[str]
    mimetype: Optional[str]

    @property
    def extension(self) -> str:
        return Path(self.name).suffix.lower()


@dataclasses.dataclass(frozen=True)
class DryadCandidate:
    """Grouped Dryad dataset that exposes potentially relevant files."""

    identifier: str
    title: Optional[str]
    doi: Optional[str]
    url: Optional[str]
    authors: Tuple[str, ...]
    description: Optional[str]
    files: Tuple[DryadFile, ...]
    query_hits: Tuple[str, ...]

    def to_dict(self) -> Dict[str, Any]:
        return {
            "identifier": self.identifier,
            "title": self.title,
            "doi": self.doi,
            "url": self.url,
            "authors": list(self.authors),
            "description": self.description,
            "files": [dataclasses.asdict(f) for f in self.files],
            "query_hits": list(self.query_hits),
        }


@dataclasses.dataclass
class DryadSearchConfig:
    """Configuration for Dryad discovery."""

    queries: Sequence[str]
    allowed_extensions: Sequence[str] = tuple(sorted(_ALLOWED_EXTENSIONS))
    max_pages: int = 5
    page_size: int = 50
    per_query_limit: int = 200
    request_timeout: float = 20.0
    inter_request_pause: float = 0.25

    def extension_set(self) -> set[str]:
        return {ext.lower() for ext in self.allowed_extensions}


class DryadDiscoveryError(RuntimeError):
    """Raised when the Dryad API cannot be queried."""


def _iter_search_hits(
    session: requests.Session,
    query: str,
    config: DryadSearchConfig,
) -> Iterator[Dict[str, Any]]:
    """Yield search hits for a given Dryad query."""

    page = 1
    fetched = 0
    while page <= config.max_pages and fetched < config.per_query_limit:
        params = {
            "query": query,
            "per_page": config.page_size,
            "page": page,
        }
        response = session.get(
            f"{API_ROOT}/search",
            params=params,
            timeout=config.request_timeout,
        )
        if response.status_code >= 400:
            raise DryadDiscoveryError(
                f"Dryad search failed with {response.status_code}: {response.text[:200]}"
            )
        payload = response.json()
        embedded = payload.get("_embedded", {})
        datasets = embedded.get("stash:datasets", [])
        if not datasets:
            break
        for hit in datasets:
            yield hit
            fetched += 1
            if fetched >= config.per_query_limit:
                break
        if fetched >= config.per_query_limit:
            break
        if len(datasets) < config.page_size:
            break
        page += 1
        if page <= config.max_pages:
            time.sleep(config.inter_request_pause)


def _safe_get(
    session: requests.Session,
    url: str,
    config: DryadSearchConfig,
) -> Optional[Dict[str, Any]]:
    response = session.get(url, timeout=config.request_timeout)
    if response.status_code == 404:
        return None
    if response.status_code >= 400:
        raise DryadDiscoveryError(f"Request to {url} failed with {response.status_code}")
    return response.json()


def _fetch_version_files(
    session: requests.Session,
    version_href: str,
    config: DryadSearchConfig,
) -> List[DryadFile]:
    version_url = urljoin(API_BASE, version_href)
    version_payload = _safe_get(session, version_url, config)
    if not version_payload:
        return []
    files_link = (
        version_payload.get("_links", {})
        .get("stash:files", {})
        .get("href")
    )
    if not files_link:
        return []
    files_url = urljoin(API_BASE, files_link)
    files_payload = _safe_get(session, files_url, config)
    if not files_payload:
        return []
    embedded = files_payload.get("_embedded", {})
    records = embedded.get("stash:files", [])
    allowed = config.extension_set()
    result: List[DryadFile] = []
    for record in records:
        name = record.get("path")
        if not name:
            continue
        ext = Path(name).suffix.lower()
        if ext not in allowed:
            continue
        download_href = (
            record.get("_links", {})
            .get("stash:download", {})
            .get("href")
        )
        result.append(
            DryadFile(
                file_id=int(record.get("_links", {}).get("self", {}).get("href", "0").split("/")[-1] or 0),
                name=name,
                size=record.get("size"),
                download_url=urljoin(API_BASE, download_href) if download_href else None,
                checksum=record.get("digest"),
                checksum_type=record.get("digestType"),
                mimetype=record.get("mimeType"),
            )
        )
    return result


def discover_dryad_candidates(
    config: DryadSearchConfig,
    session: Optional[requests.Session] = None,
) -> Tuple[List[DryadCandidate], Dict[str, Any]]:
    """Run the Dryad discovery pipeline and return candidates with summary stats."""

    if session is None:
        session = requests.Session()

    grouped: Dict[str, Dict[str, Any]] = {}

    for query in config.queries:
        for hit in _iter_search_hits(session, query, config):
            identifier = hit.get("identifier") or hit.get("id")
            if not identifier:
                continue
            identifier = str(identifier)
            entry = grouped.setdefault(
                identifier,
                {
                    "dataset": hit,
                    "files": None,
                    "query_hits": set(),
                },
            )
            entry["query_hits"].add(query)

    candidates: List[DryadCandidate] = []
    for identifier, info in grouped.items():
        dataset = info.get("dataset") or {}
        version_href = (
            dataset.get("_links", {})
            .get("stash:version", {})
            .get("href")
        )
        files: List[DryadFile] = []
        if version_href:
            files = _fetch_version_files(session, version_href, config)
        if not files:
            continue
        metadata = dataset
        authors = []
        for author in metadata.get("authors", []) or []:
            name = author.get("fullName") if isinstance(author, dict) else author
            if name:
                authors.append(name)
        doi = metadata.get("identifier")
        url = urljoin(API_BASE, metadata.get("_links", {}).get("self", {}).get("href", ""))
        candidate = DryadCandidate(
            identifier=identifier,
            title=metadata.get("title"),
            doi=doi,
            url=url or None,
            authors=tuple(authors),
            description=metadata.get("abstract"),
            files=tuple(sorted(files, key=lambda f: f.name.lower())),
            query_hits=tuple(sorted(info["query_hits"])),
        )
        candidates.append(candidate)

    candidates.sort(key=lambda c: (c.title or "", c.identifier))

    summary = {
        "generated_at": _dt.datetime.now(UTC).isoformat().replace("+00:00", "Z"),
        "query_count": len(config.queries),
        "candidate_count": len(candidates),
        "unique_identifiers": len({c.identifier for c in candidates}),
    }

    return candidates, summary


def serialise_candidates(
    candidates: Sequence[DryadCandidate],
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
