"""OSF dataset discovery helpers for the Thiele proofpack pipeline."""

from __future__ import annotations

import dataclasses
import datetime as _dt
from datetime import UTC
import json
import time
from collections import defaultdict
from pathlib import Path
from typing import Any, Dict, Iterator, List, Optional, Sequence, Tuple

import requests

__all__ = [
    "OSFFile",
    "OSFCandidate",
    "OSFSearchConfig",
    "discover_osf_candidates",
    "serialise_candidates",
]

API_ROOT = "https://api.osf.io/v2"
_ALLOWED_EXTENSIONS = {
    ".csv",
    ".tsv",
    ".h5",
    ".hdf5",
    ".mat",
    ".tif",
    ".tiff",
}


@dataclasses.dataclass(frozen=True)
class OSFFile:
    """Metadata about a single OSF file hit."""

    file_id: str
    name: str
    path: str
    size: Optional[int]
    download_url: str
    hashes: Dict[str, str]
    provider: Optional[str]
    created: Optional[str]
    modified: Optional[str]

    @property
    def extension(self) -> str:
        return Path(self.name).suffix.lower()


@dataclasses.dataclass(frozen=True)
class OSFCandidate:
    """A grouped project/node that exposes potentially useful raw data."""

    node_id: str
    title: Optional[str]
    description: Optional[str]
    contributors: Tuple[str, ...]
    files: Tuple[OSFFile, ...]
    query_hits: Tuple[str, ...]
    node_url: Optional[str]

    def to_dict(self) -> Dict[str, Any]:
        return {
            "node_id": self.node_id,
            "title": self.title,
            "description": self.description,
            "contributors": list(self.contributors),
            "files": [dataclasses.asdict(f) for f in self.files],
            "query_hits": list(self.query_hits),
            "node_url": self.node_url,
        }


@dataclasses.dataclass
class OSFSearchConfig:
    """Configuration for OSF discovery."""

    queries: Sequence[str]
    allowed_extensions: Sequence[str] = tuple(sorted(_ALLOWED_EXTENSIONS))
    max_pages: int = 5
    page_size: int = 100
    per_query_limit: int = 250
    request_timeout: float = 20.0
    inter_request_pause: float = 0.25
    contributor_page_limit: int = 2

    def extension_set(self) -> set[str]:
        return {ext.lower() for ext in self.allowed_extensions}


class OSFDiscoveryError(RuntimeError):
    """Raised when the OSF API cannot be queried."""


def _iter_search_hits(
    session: requests.Session,
    query: str,
    config: OSFSearchConfig,
) -> Iterator[Dict[str, Any]]:
    """Yield search hits for a given query."""

    params = {"q": query, "size": config.page_size}
    url = f"{API_ROOT}/search/files/"
    fetched = 0
    page = 0
    while url and page < config.max_pages and fetched < config.per_query_limit:
        response = session.get(url, params=params, timeout=config.request_timeout)
        if response.status_code >= 400:
            raise OSFDiscoveryError(
                f"OSF search request failed with {response.status_code}: {response.text[:200]}"
            )
        payload = response.json()
        hits = payload.get("data", [])
        for hit in hits:
            yield hit
            fetched += 1
            if fetched >= config.per_query_limit:
                break
        if fetched >= config.per_query_limit:
            break
        url = payload.get("links", {}).get("next")
        params = None
        page += 1
        if url:
            time.sleep(config.inter_request_pause)


def _safe_get(session: requests.Session, url: str, config: OSFSearchConfig) -> Optional[Dict[str, Any]]:
    response = session.get(url, timeout=config.request_timeout)
    if response.status_code == 404:
        return None
    if response.status_code >= 400:
        raise OSFDiscoveryError(f"Request to {url} failed with {response.status_code}")
    return response.json()


def _extract_file(hit: Dict[str, Any]) -> Optional[OSFFile]:
    attributes = hit.get("attributes", {})
    name = attributes.get("name")
    if not name:
        return None
    path = attributes.get("materialized_path") or attributes.get("path") or ""
    size = attributes.get("size")
    hashes = attributes.get("extra", {}).get("hashes", {})
    download_url = hit.get("links", {}).get("download")
    provider = attributes.get("provider")
    created = attributes.get("date_created")
    modified = attributes.get("date_modified")
    return OSFFile(
        file_id=hit.get("id", ""),
        name=name,
        path=path,
        size=size,
        download_url=download_url,
        hashes=hashes,
        provider=provider,
        created=created,
        modified=modified,
    )


def _collect_node_metadata(
    session: requests.Session,
    node_id: str,
    config: OSFSearchConfig,
) -> Tuple[Optional[str], Optional[str], Tuple[str, ...], Optional[str]]:
    node_url = f"{API_ROOT}/nodes/{node_id}/"
    node_payload = _safe_get(session, node_url, config)
    title: Optional[str] = None
    description: Optional[str] = None
    contributors: List[str] = []
    node_html: Optional[str] = None

    if node_payload and "data" in node_payload:
        data = node_payload["data"]
        attributes = data.get("attributes", {})
        title = attributes.get("title")
        description = attributes.get("description")
        node_html = data.get("links", {}).get("html")
        contrib_link = data.get("relationships", {}).get("contributors", {}).get("links", {}).get("related", {}).get("href")
        if contrib_link:
            url = contrib_link
            pages = 0
            while url and pages < config.contributor_page_limit:
                contrib_payload = _safe_get(session, url, config)
                if not contrib_payload:
                    break
                for contributor in contrib_payload.get("data", []):
                    name = contributor.get("attributes", {}).get("full_name")
                    if name:
                        contributors.append(name)
                url = contrib_payload.get("links", {}).get("next")
                pages += 1
                if url:
                    time.sleep(config.inter_request_pause)

    return title, description, tuple(contributors), node_html


def discover_osf_candidates(
    config: OSFSearchConfig,
    session: Optional[requests.Session] = None,
) -> Tuple[List[OSFCandidate], Dict[str, Any]]:
    """Run the OSF discovery pipeline and return candidates with summary stats."""

    if session is None:
        session = requests.Session()

    allowed = config.extension_set()
    grouped: Dict[str, Dict[str, Any]] = defaultdict(lambda: {
        "files": {},
        "query_hits": set(),
    })

    for query in config.queries:
        for hit in _iter_search_hits(session, query, config):
            file_meta = _extract_file(hit)
            if not file_meta:
                continue
            if file_meta.extension not in allowed:
                continue
            relationships = hit.get("relationships", {})
            node = relationships.get("node", {}).get("data") or relationships.get("target", {}).get("data")
            if not node:
                continue
            node_id = node.get("id")
            if not node_id:
                continue
            entry = grouped[node_id]
            entry["files"][file_meta.file_id] = file_meta
            entry["query_hits"].add(query)

    candidates: List[OSFCandidate] = []
    for node_id, info in grouped.items():
        title, description, contributors, node_url = _collect_node_metadata(session, node_id, config)
        files = tuple(sorted(info["files"].values(), key=lambda f: f.name.lower()))
        candidate = OSFCandidate(
            node_id=node_id,
            title=title,
            description=description,
            contributors=contributors,
            files=files,
            query_hits=tuple(sorted(info["query_hits"])),
            node_url=node_url,
        )
        candidates.append(candidate)

    candidates.sort(key=lambda c: (c.title or "", c.node_id))

    summary = {
        "generated_at": _dt.datetime.now(UTC).isoformat().replace("+00:00", "Z"),
        "query_count": len(config.queries),
        "candidate_count": len(candidates),
        "unique_projects": len({c.node_id for c in candidates}),
    }

    return candidates, summary


def serialise_candidates(
    candidates: Sequence[OSFCandidate],
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
