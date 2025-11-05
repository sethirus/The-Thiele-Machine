from __future__ import annotations

import json
from pathlib import Path

import pytest

from scripts import discover_public_candidates as cli


class DummyConfig:
    def __init__(self, *, queries, page_size, max_pages, per_query_limit, allowed_extensions=None):
        self.queries = queries
        self.page_size = page_size
        self.max_pages = max_pages
        self.per_query_limit = per_query_limit
        self.allowed_extensions = allowed_extensions or (".csv",)


def test_cli_dispatches_selected_source(tmp_path: Path, monkeypatch: pytest.MonkeyPatch):
    captured: dict[str, object] = {}

    def discover(config: DummyConfig):
        captured["config"] = config
        return [], {"candidate_count": 0}

    def serialise(candidates, summary):
        captured["summary"] = summary
        return json.dumps({"summary": summary, "candidates": []})

    monkeypatch.setitem(cli._SOURCES, "dummy", (DummyConfig, discover, serialise, ["default query"]))

    exit_code = cli.main([
        "--source",
        "dummy",
        "--page-size",
        "5",
        "--max-pages",
        "2",
        "--per-query-limit",
        "3",
        "--extensions",
        ".csv",
        ".tsv",
        "--output",
        str(tmp_path / "out.json"),
    ])

    assert exit_code == 0
    config = captured["config"]
    assert isinstance(config, DummyConfig)
    assert config.page_size == 5
    assert config.max_pages == 2
    assert config.per_query_limit == 3
    assert config.allowed_extensions == (".csv", ".tsv")
    summary = captured["summary"]
    assert summary["allowed_extensions"] == [".csv", ".tsv"]
    output = json.loads((tmp_path / "out.json").read_text())
    assert output["summary"]["candidate_count"] == 0
    assert output["candidates"] == []
