from __future__ import annotations

import json
from pathlib import Path

import pytest

from experiments.data_sources import figshare


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
    search_payload = json.loads(Path("tests/data/figshare_search_sample.json").read_text())
    article_101 = json.loads(Path("tests/data/figshare_article_101.json").read_text())
    article_202 = json.loads(Path("tests/data/figshare_article_202.json").read_text())
    fixtures = {
        (
            f"{figshare.API_ROOT}/articles",
            (
                ("page", 1),
                ("page_size", 50),
                ("search_for", "optical tweezers"),
            ),
        ): search_payload,
        (f"{figshare.API_ROOT}/articles/101", None): article_101,
        (f"{figshare.API_ROOT}/articles/202", None): article_202,
    }
    return DummySession(fixtures)


def test_discover_figshare_candidates(sample_session: DummySession):
    config = figshare.FigshareSearchConfig(
        queries=["optical tweezers"],
        max_pages=1,
        page_size=50,
        per_query_limit=20,
    )
    config.inter_request_pause = 0.0
    candidates, summary = figshare.discover_figshare_candidates(config, session=sample_session)
    assert summary["candidate_count"] == 2
    first = next(c for c in candidates if c.article_id == 101)
    assert first.title == "Optical tweezers record"
    assert first.tags == ("brownian", "optical tweezers")
    assert len(first.files) == 1
    assert first.files[0].name == "tracks.csv"
    second = next(c for c in candidates if c.article_id == 202)
    assert second.files[0].name == "image.tif"
    assert set(second.tags) == {"diffusion", "spt"}


def test_serialise_figshare_candidates(sample_session: DummySession):
    config = figshare.FigshareSearchConfig(
        queries=["optical tweezers"],
        max_pages=1,
        page_size=50,
        per_query_limit=20,
    )
    config.inter_request_pause = 0.0
    candidates, summary = figshare.discover_figshare_candidates(config, session=sample_session)
    document = figshare.serialise_candidates(candidates, summary)
    payload = json.loads(document)
    assert payload["summary"]["candidate_count"] == 2
    assert len(payload["candidates"]) == 2
    assert payload["candidates"][0]["files"][0]["name"] in {"tracks.csv", "image.tif"}
