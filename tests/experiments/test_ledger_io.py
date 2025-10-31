"""Tests for the deterministic ledger IO helpers."""

from pathlib import Path

import pytest

from experiments.ledger_io import (
    dump_ledger,
    iter_ledger,
    ledger_digest,
    ledger_summary,
    load_ledger,
)


@pytest.fixture()
def sample_path(tmp_path: Path) -> Path:
    fixture = Path("experiments/data/sample_ledger.jsonl")
    target = tmp_path / "sample.jsonl"
    target.write_text(fixture.read_text(encoding="utf-8"), encoding="utf-8")
    return target


def test_load_and_digest(sample_path: Path) -> None:
    entries = load_ledger(sample_path)
    assert len(entries) == 2
    digest_once = ledger_digest(entries)
    digest_twice = ledger_digest(load_ledger(sample_path))
    assert digest_once == digest_twice
    assert digest_once == "dde06dbac29343bf74b2a6785eb421784a73de98f3fa57e90fdef849fa0c106c"


def test_iter_matches_load(sample_path: Path) -> None:
    iterated = list(iter_ledger(sample_path))
    loaded = load_ledger(sample_path)
    assert iterated == loaded


def test_dump_round_trip(tmp_path: Path, sample_path: Path) -> None:
    entries = load_ledger(sample_path)
    target = tmp_path / "roundtrip.jsonl"
    dump_ledger([entry.payload for entry in entries], target)
    reloaded = load_ledger(target)
    assert reloaded == entries


def test_summary(sample_path: Path) -> None:
    entries = load_ledger(sample_path)
    assert pytest.approx(ledger_summary(entries, "mu_answer"), rel=1e-12) == 1.0
    assert pytest.approx(ledger_summary(entries, "delta_work"), rel=1e-12) == pytest.approx(
        0.69314718, rel=1e-12
    )
    assert ledger_summary(entries, "missing_key") == 0.0
