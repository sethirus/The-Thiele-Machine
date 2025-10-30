from __future__ import annotations

import json
from pathlib import Path

import pytest

from experiments.data_sources import dryad


class DummyResponse:
    def __init__(self, status_code: int, payload: dict[str, object]):
        self.status_code = status_code
        self._payload = payload
        self.text = json.dumps(payload)

    def json(self) -> dict[str, object]:
        return self._payload


class DummySession:
    def __init__(self, fixtures: dict[tuple[str, tuple[tuple[str, object], ...] | None], dict[str, object]]):
        self.fixtures = fixtures

    def get(self, url: str, params=None, timeout: float | None = None):  # noqa: D401 - mimic requests.Session
        key = (url, tuple(sorted((params or {}).items())) or None)
        payload = self.fixtures.get(key)
        if payload is None:
            raise AssertionError(f"Unexpected request: {key}")
        return DummyResponse(200, payload)


@pytest.fixture()
def sample_session() -> DummySession:
    search_payload = json.loads(Path("tests/data/dryad_search_sample.json").read_text())
    version_111 = json.loads(Path("tests/data/dryad_version_111.json").read_text())
    files_111 = json.loads(Path("tests/data/dryad_files_111.json").read_text())
    version_222 = json.loads(Path("tests/data/dryad_version_222.json").read_text())
    files_222 = json.loads(Path("tests/data/dryad_files_222.json").read_text())
    fixtures = {
        (
            f"{dryad.API_ROOT}/search",
            (
                ("page", 1),
                ("per_page", 50),
                ("query", "optical tweezers"),
            ),
        ): search_payload,
        (f"{dryad.API_ROOT}/versions/111", None): version_111,
        (f"{dryad.API_ROOT}/versions/111/files", None): files_111,
        (f"{dryad.API_ROOT}/versions/222", None): version_222,
        (f"{dryad.API_ROOT}/versions/222/files", None): files_222,
    }
    return DummySession(fixtures)


def test_discover_dryad_candidates(sample_session: DummySession):
    config = dryad.DryadSearchConfig(
        queries=["optical tweezers"],
        max_pages=1,
        page_size=50,
        per_query_limit=10,
    )
    config.inter_request_pause = 0.0
    candidates, summary = dryad.discover_dryad_candidates(config, session=sample_session)
    assert summary["candidate_count"] == 2
    first = next(c for c in candidates if c.identifier == "doi:10.1234/alpha")
    assert first.title == "Optical tweezers dryad"
    assert first.authors == ("A. Researcher", "B. Analyst")
    assert len(first.files) == 1
    assert first.files[0].download_url.endswith("/api/v2/files/1/download")
    second = next(c for c in candidates if c.identifier == "doi:10.5678/beta")
    assert second.files[0].name == "trajectory.csv"


def test_serialise_dryad_candidates(sample_session: DummySession):
    config = dryad.DryadSearchConfig(
        queries=["optical tweezers"],
        max_pages=1,
        page_size=50,
        per_query_limit=10,
    )
    config.inter_request_pause = 0.0
    candidates, summary = dryad.discover_dryad_candidates(config, session=sample_session)
    document = dryad.serialise_candidates(candidates, summary)
    payload = json.loads(document)
    assert payload["summary"]["candidate_count"] == 2
    assert len(payload["candidates"]) == 2
    assert payload["candidates"][0]["files"][0]["name"] in {"data.zip", "trajectory.csv"}
