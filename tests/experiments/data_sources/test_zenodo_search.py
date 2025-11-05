from __future__ import annotations

import json
from pathlib import Path

import pytest

from experiments.data_sources import zenodo


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
    search_payload = json.loads(Path("tests/data/zenodo_search_sample.json").read_text())
    fixtures = {
        (
            f"{zenodo.API_ROOT}/records",
            (
                ("page", 1),
                ("q", "optical tweezers"),
                ("size", 100),
            ),
        ): search_payload
    }
    return DummySession(fixtures)


def test_discover_zenodo_candidates(sample_session: DummySession):
    config = zenodo.ZenodoSearchConfig(
        queries=["optical tweezers"],
        max_pages=1,
        page_size=100,
        per_query_limit=10,
    )
    config.inter_request_pause = 0.0
    candidates, summary = zenodo.discover_zenodo_candidates(config, session=sample_session)
    assert summary["candidate_count"] == 2
    first = next(c for c in candidates if c.record_id == 10)
    assert first.title == "Zenodo tweezers"
    assert len(first.files) == 1
    assert first.files[0].name == "tweezers.csv"
    assert first.creators == ("A. Researcher", "B. Analyst")
    second = next(c for c in candidates if c.record_id == 20)
    assert second.files[0].name == "stack.tif"


def test_serialise_zenodo_candidates(sample_session: DummySession):
    config = zenodo.ZenodoSearchConfig(
        queries=["optical tweezers"],
        max_pages=1,
        page_size=100,
        per_query_limit=10,
    )
    config.inter_request_pause = 0.0
    candidates, summary = zenodo.discover_zenodo_candidates(config, session=sample_session)
    document = zenodo.serialise_candidates(candidates, summary)
    payload = json.loads(document)
    assert payload["summary"]["candidate_count"] == 2
    assert len(payload["candidates"]) == 2
    assert payload["candidates"][0]["files"][0]["name"] in {"tweezers.csv", "stack.tif"}
