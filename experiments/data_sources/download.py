from __future__ import annotations

import dataclasses
import datetime as _dt
from datetime import UTC
import hashlib
import json
import re
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

import requests

__all__ = [
    "DownloadConfig",
    "DownloadOutcome",
    "DownloadError",
    "slugify",
    "derive_dataset_slug",
    "download_selected_candidate",
    "verify_manifest",
]


class DownloadError(RuntimeError):
    """Raised when a dataset cannot be downloaded or verified."""


@dataclasses.dataclass(frozen=True)
class DownloadConfig:
    """Configuration for dataset downloads."""

    base_dir: Path
    chunk_size: int = 64 * 1024
    request_timeout: float = 30.0
    skip_existing: bool = True


@dataclasses.dataclass(frozen=True)
class DownloadOutcome:
    """Summary of a completed dataset download."""

    dataset_dir: Path
    manifest: Dict[str, object]


_slug_invalid = re.compile(r"[^a-z0-9]+")


def slugify(parts: Iterable[str]) -> str:
    """Return a filesystem-safe slug derived from the provided text parts."""

    filtered: List[str] = []
    for part in parts:
        if not part:
            continue
        normalised = part.strip().lower()
        normalised = _slug_invalid.sub("-", normalised)
        normalised = normalised.strip("-")
        if normalised:
            filtered.append(normalised)
    if not filtered:
        return "dataset"
    slug = "-".join(filtered)
    return slug[:120]


def _candidate_identifier(source: str, candidate: Dict[str, object]) -> str:
    if source == "osf":
        return str(candidate.get("node_id") or candidate.get("id") or "osf")
    if source == "figshare":
        return str(candidate.get("article_id") or candidate.get("id") or "figshare")
    if source == "dryad":
        return str(candidate.get("identifier") or candidate.get("id") or "dryad")
    if source == "zenodo":
        return str(candidate.get("record_id") or candidate.get("id") or "zenodo")
    return str(candidate.get("id") or "dataset")


def _candidate_title(candidate: Dict[str, object]) -> Optional[str]:
    for key in ("title", "description", "doi"):
        value = candidate.get(key)
        if isinstance(value, str) and value.strip():
            return value
    return None


def derive_dataset_slug(source: str, candidate: Dict[str, object]) -> str:
    """Return the canonical slug used for a mirrored dataset directory."""

    identifier = _candidate_identifier(source, candidate)
    title = _candidate_title(candidate) or ""
    return slugify((source, identifier, title))


def _normalise_relative_path(file_info: Dict[str, object]) -> str:
    for key in ("path", "name"):
        value = file_info.get(key)
        if isinstance(value, str) and value.strip():
            path = value.lstrip("/")
            if not path:
                continue
            return path
    raise DownloadError("File metadata is missing a usable path or name")


def _iter_file_content(response: requests.Response, chunk_size: int) -> Iterable[bytes]:
    try:
        iterator = response.iter_content(chunk_size)
    except AttributeError as exc:  # pragma: no cover - defensive guard
        raise DownloadError("Response object does not support streaming") from exc
    for chunk in iterator:
        if chunk:
            yield chunk


def _download_file(
    session: requests.Session,
    url: str,
    destination: Path,
    *,
    chunk_size: int,
    timeout: float,
) -> Tuple[int, str]:
    response = session.get(url, stream=True, timeout=timeout)
    if response.status_code >= 400:
        raise DownloadError(f"Failed to download {url}: {response.status_code}")
    destination.parent.mkdir(parents=True, exist_ok=True)
    hasher = hashlib.sha256()
    size = 0
    with destination.open("wb") as handle:
        for chunk in _iter_file_content(response, chunk_size):
            handle.write(chunk)
            size += len(chunk)
            hasher.update(chunk)
    return size, hasher.hexdigest()


def _hash_file(path: Path) -> Tuple[int, str]:
    hasher = hashlib.sha256()
    size = 0
    with path.open("rb") as handle:
        while True:
            chunk = handle.read(128 * 1024)
            if not chunk:
                break
            size += len(chunk)
            hasher.update(chunk)
    return size, hasher.hexdigest()


def download_selected_candidate(
    entry: Dict[str, object],
    *,
    source: str,
    config: DownloadConfig,
    session: Optional[requests.Session] = None,
) -> DownloadOutcome:
    """Download files for a filtered candidate and emit a manifest."""

    candidate = entry.get("candidate")
    if not isinstance(candidate, dict):
        raise DownloadError("Selected entry is missing candidate metadata")
    anchors = entry.get("anchors")
    if not isinstance(anchors, dict):
        raise DownloadError("Selected entry is missing anchor metadata")

    dataset_id = _candidate_identifier(source, candidate)
    slug = derive_dataset_slug(source, candidate)
    dataset_dir = config.base_dir / source / slug
    raw_dir = dataset_dir / "raw"
    raw_dir.mkdir(parents=True, exist_ok=True)

    candidate_path = dataset_dir / "candidate.json"
    anchors_path = dataset_dir / "anchors.json"
    candidate_path.write_text(json.dumps(candidate, indent=2, sort_keys=True))
    anchors_path.write_text(json.dumps(anchors, indent=2, sort_keys=True))

    close_session = False
    if session is None:
        session = requests.Session()
        close_session = True

    try:
        manifest_entries: List[Dict[str, object]] = []
        files = candidate.get("files")
        if not isinstance(files, Sequence):
            files = []
        for file_info in files:
            if not isinstance(file_info, dict):
                continue
            url = file_info.get("download_url")
            if not isinstance(url, str) or not url:
                continue
            rel_path = _normalise_relative_path(file_info)
            destination = raw_dir / rel_path
            if destination.exists() and config.skip_existing:
                size, sha256 = _hash_file(destination)
            else:
                size, sha256 = _download_file(
                    session,
                    url,
                    destination,
                    chunk_size=config.chunk_size,
                    timeout=config.request_timeout,
                )
            manifest_entry = {
                "path": str(Path("raw") / rel_path),
                "sha256": sha256,
                "size": size,
            }
            if file_info.get("checksum"):
                manifest_entry["source_checksum"] = file_info["checksum"]
            if file_info.get("hashes"):
                manifest_entry["source_hashes"] = file_info["hashes"]
            manifest_entries.append(manifest_entry)

        manifest_entries.sort(key=lambda item: item["path"])
        manifest = {
            "generated_at": _dt.datetime.now(UTC).isoformat().replace("+00:00", "Z"),
            "source": source,
            "dataset_id": dataset_id,
            "title": _candidate_title(candidate),
            "file_count": len(manifest_entries),
            "files": manifest_entries,
        }
        manifest_path = dataset_dir / "MANIFEST.json"
        manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True))
        verify_manifest(manifest_path)
        return DownloadOutcome(dataset_dir=dataset_dir, manifest=manifest)
    finally:
        if close_session:
            session.close()


def verify_manifest(manifest_path: Path) -> None:
    """Recompute file hashes to ensure the manifest matches the filesystem."""

    manifest = json.loads(manifest_path.read_text())
    files = manifest.get("files", [])
    if not isinstance(files, list):
        raise DownloadError("Manifest is missing file entries")
    for entry in files:
        if not isinstance(entry, dict):
            raise DownloadError("Manifest entry is not a dictionary")
        rel_path = entry.get("path")
        expected_hash = entry.get("sha256")
        expected_size = entry.get("size")
        if not isinstance(rel_path, str) or not isinstance(expected_hash, str) or not isinstance(expected_size, int):
            raise DownloadError("Manifest entry is missing required fields")
        file_path = manifest_path.parent / rel_path
        if not file_path.exists():
            raise DownloadError(f"Manifest references missing file: {rel_path}")
        actual_size, actual_hash = _hash_file(file_path)
        if actual_hash != expected_hash or actual_size != expected_size:
            raise DownloadError(f"Checksum mismatch for {rel_path}")
