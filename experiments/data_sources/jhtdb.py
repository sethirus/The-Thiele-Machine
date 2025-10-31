"""Utilities for sampling small datasets from the Johns Hopkins Turbulence Database.

The helpers in this module intentionally avoid any heavy third-party dependencies
so that agents can issue authenticated REST requests directly against the JHTDB
web services.  They expose thin wrappers that translate typed dataclass requests
into HTTP POST payloads, capture the JSON responses, and persist the resulting
samples for downstream proofpack generation.

The public API focuses on three operations:

* :func:`fetch_metadata` — query dataset metadata to locate available fields and
  default temporal windows.
* :func:`fetch_samples` — request a small trajectory or cutout from the selected
  dataset.  The function accepts an explicit list of spatial sample points and
  a temporal grid; it returns a :class:`JHTDBSample` containing normalised
  floating-point values along with verbatim provenance.
* :func:`write_sample_bundle` — persist the returned sample and a corresponding
  manifest so archivists can capture deterministic digests without committing
  large binary files to the repository.

The implementation deliberately refrains from making assumptions about the
underlying REST layout beyond the documented endpoints.  Tests patch
``urllib.request.urlopen`` so the helpers remain deterministic offline.
"""

from __future__ import annotations

from dataclasses import dataclass, field
import hashlib
import json
from pathlib import Path
from typing import Mapping, MutableMapping, Sequence
from urllib import error, request

__all__ = [
    "DEFAULT_BASE_URL",
    "DEFAULT_METADATA_ENDPOINT",
    "DEFAULT_SAMPLE_ENDPOINT",
    "JHTDBSample",
    "fetch_metadata",
    "fetch_samples",
    "write_sample_bundle",
]

DEFAULT_BASE_URL = "https://beta.jhtdb.org/JHTDB-WS/rest"
DEFAULT_METADATA_ENDPOINT = "/dataset"
DEFAULT_SAMPLE_ENDPOINT = "/sample"


@dataclass(slots=True)
class JHTDBSample:
    """Container for a small-budget JHTDB sample."""

    dataset: str
    field: str
    times: Sequence[float]
    points: Sequence[Sequence[float]]
    values: Sequence[Sequence[Sequence[float]]]
    metadata: MutableMapping[str, object] = field(default_factory=dict)

    def to_json(self) -> Mapping[str, object]:
        return {
            "dataset": self.dataset,
            "field": self.field,
            "times": list(self.times),
            "points": [list(point) for point in self.points],
            "values": [
                [list(component) for component in time_slice]
                for time_slice in self.values
            ],
            "metadata": dict(self.metadata),
        }


def _build_url(base_url: str, endpoint: str) -> str:
    base = base_url.rstrip("/")
    suffix = endpoint if endpoint.startswith("/") else f"/{endpoint}"
    return f"{base}{suffix}"


def _read_json(resp: request.addinfourl) -> Mapping[str, object]:
    try:
        payload = resp.read()
    finally:
        resp.close()
    return json.loads(payload.decode("utf-8"))


def fetch_metadata(
    *,
    base_url: str = DEFAULT_BASE_URL,
    endpoint: str = DEFAULT_METADATA_ENDPOINT,
    dataset: str,
    token: str | None = None,
) -> Mapping[str, object]:
    """Fetch metadata for ``dataset`` from the JHTDB REST service."""

    url = _build_url(base_url, endpoint)
    payload = json.dumps({"dataset": dataset}).encode("utf-8")
    req = request.Request(url, data=payload, headers={"Content-Type": "application/json"})
    if token:
        req.add_header("Authorization", f"Bearer {token}")
    try:
        with request.urlopen(req) as resp:
            return _read_json(resp)
    except error.HTTPError as exc:  # pragma: no cover - network error path
        raise RuntimeError(f"Failed to fetch JHTDB metadata: {exc}") from exc


def fetch_samples(
    *,
    base_url: str = DEFAULT_BASE_URL,
    endpoint: str = DEFAULT_SAMPLE_ENDPOINT,
    dataset: str,
    field: str,
    times: Sequence[float],
    points: Sequence[Sequence[float]],
    token: str | None = None,
    extra_payload: Mapping[str, object] | None = None,
) -> JHTDBSample:
    """Request a deterministic sample from the JHTDB REST service."""

    if not times:
        raise ValueError("times must be a non-empty sequence")
    if not points:
        raise ValueError("points must be a non-empty sequence")

    url = _build_url(base_url, endpoint)
    body: MutableMapping[str, object] = {
        "dataset": dataset,
        "field": field,
        "times": list(times),
        "points": [list(point) for point in points],
    }
    if extra_payload:
        body.update(extra_payload)

    payload = json.dumps(body).encode("utf-8")
    headers = {"Content-Type": "application/json"}
    if token:
        headers["Authorization"] = f"Bearer {token}"

    req = request.Request(url, data=payload, headers=headers)

    try:
        with request.urlopen(req) as resp:
            response = _read_json(resp)
    except error.HTTPError as exc:  # pragma: no cover - network error path
        raise RuntimeError(f"Failed to fetch JHTDB samples: {exc}") from exc

    values = response.get("values")
    if not isinstance(values, Sequence):
        raise ValueError("JHTDB sample response missing 'values'")

    metadata = response.get("metadata")
    meta_map: MutableMapping[str, object]
    if isinstance(metadata, Mapping):
        meta_map = dict(metadata)
    else:
        meta_map = {}

    return JHTDBSample(
        dataset=dataset,
        field=field,
        times=list(times),
        points=[list(point) for point in points],
        values=[[list(component) for component in time_slice] for time_slice in values],
        metadata=meta_map,
    )


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(8192), b""):
            digest.update(chunk)
    return digest.hexdigest()


def write_sample_bundle(
    sample: JHTDBSample,
    output_dir: Path,
    *,
    sample_filename: str = "jhtdb_samples.json",
    manifest_filename: str = "manifest.json",
) -> Path:
    """Persist ``sample`` and its manifest into ``output_dir``."""

    output_dir.mkdir(parents=True, exist_ok=True)
    sample_path = output_dir / sample_filename
    manifest_path = output_dir / manifest_filename

    with sample_path.open("w", encoding="utf-8") as handle:
        json.dump(sample.to_json(), handle, indent=2, sort_keys=True)
        handle.write("\n")

    manifest = {
        "dataset": sample.dataset,
        "field": sample.field,
        "files": {
            sample_filename: {
                "sha256": _sha256(sample_path),
                "bytes": sample_path.stat().st_size,
            }
        },
    }

    with manifest_path.open("w", encoding="utf-8") as handle:
        json.dump(manifest, handle, indent=2, sort_keys=True)
        handle.write("\n")

    return sample_path

