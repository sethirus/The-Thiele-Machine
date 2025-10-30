from __future__ import annotations

import json
from pathlib import Path
import pytest

from experiments.data_sources import osf


class DummyResponse:
    def __init__(self, status_code: int, payload: dict[str, object]):
        self.status_code = status_code
        self._payload = payload
        self.text = json.dumps(payload)

    def json(self) -> dict[str, object]:
        return self._payload


class DummySession:
    def __init__(self, fixtures: dict[str, dict[str, object]]):
        self.fixtures = fixtures
        self.calls = []

    def get(self, url: str, params=None, timeout: float | None = None):  # noqa: D401 - mimic requests.Session
        lookup = url
        if params and "q" in params:
            lookup = f"{url}?q={params['q']}"
        self.calls.append(lookup)
        payload = self.fixtures.get(lookup)
        if payload is None:
            raise AssertionError(f"Unexpected URL requested: {lookup}")
        return DummyResponse(200, payload)


@pytest.fixture()
def sample_session() -> DummySession:
    search_payload = json.loads(Path("tests/data/osf_search_sample.json").read_text())
    fixtures = {
        f"{osf.API_ROOT}/search/files/?q=optical tweezers": search_payload,
        f"{osf.API_ROOT}/nodes/node1/": {
            "data": {
                "id": "node1",
                "attributes": {
                    "title": "Optical tweezers dataset",
                    "description": "Temperature 298 K; pixel scale 0.1 um/px",
                },
                "relationships": {
                    "contributors": {
                        "links": {
                            "related": {
                                "href": f"{osf.API_ROOT}/nodes/node1/contributors/"
                            }
                        }
                    }
                },
                "links": {"html": "https://osf.io/node1/"},
            }
        },
        f"{osf.API_ROOT}/nodes/node1/contributors/": {
            "data": [
                {"attributes": {"full_name": "A. Researcher"}},
                {"attributes": {"full_name": "B. Analyst"}},
            ],
            "links": {"next": None},
        },
        f"{osf.API_ROOT}/nodes/node2/": {
            "data": {
                "id": "node2",
                "attributes": {
                    "title": "SPT experiment",
                    "description": "Frame interval 0.01 s",
                },
                "relationships": {
                    "contributors": {
                        "links": {
                            "related": {
                                "href": f"{osf.API_ROOT}/nodes/node2/contributors/"
                            }
                        }
                    }
                },
                "links": {"html": "https://osf.io/node2/"},
            }
        },
        f"{osf.API_ROOT}/nodes/node2/contributors/": {
            "data": [
                {"attributes": {"full_name": "C. Scientist"}},
            ],
            "links": {"next": None},
        },
    }
    return DummySession(fixtures)


def test_extract_file_filters_extensions():
    payload = json.loads(Path("tests/data/osf_search_sample.json").read_text())
    hit = payload["data"][0]
    file_meta = osf._extract_file(hit)
    assert file_meta is not None
    assert file_meta.name == "track.csv"
    assert file_meta.extension == ".csv"
    assert file_meta.hashes["md5"] == "abc"


def test_discover_osf_candidates_groups_by_node(sample_session: DummySession):
    config = osf.OSFSearchConfig(queries=["optical tweezers"], max_pages=1, page_size=10, per_query_limit=20)
    config.inter_request_pause = 0.0
    candidates, summary = osf.discover_osf_candidates(config, session=sample_session)
    assert summary["candidate_count"] == 2
    assert summary["unique_projects"] == 2
    titles = {candidate.title for candidate in candidates}
    assert {"Optical tweezers dataset", "SPT experiment"} == titles
    tweezers = next(c for c in candidates if c.node_id == "node1")
    assert len(tweezers.files) == 1
    assert tweezers.files[0].download_url == "https://osf.io/download/file1/"
    assert tweezers.contributors == ("A. Researcher", "B. Analyst")
    spt = next(c for c in candidates if c.node_id == "node2")
    assert len(spt.files) == 1
    assert spt.files[0].name.endswith(".tif")


def test_serialise_candidates_round_trip(sample_session: DummySession):
    config = osf.OSFSearchConfig(queries=["optical tweezers"], max_pages=1, page_size=10, per_query_limit=20)
    config.inter_request_pause = 0.0
    candidates, summary = osf.discover_osf_candidates(config, session=sample_session)
    document = osf.serialise_candidates(candidates, summary)
    payload = json.loads(document)
    assert payload["summary"]["candidate_count"] == 2
    assert len(payload["candidates"]) == 2
    assert payload["candidates"][0]["files"][0]["name"] in {"track.csv", "image.tif"}
