"""Integrity checks for the compliant Part 1 Item 1.3 freeze."""

from __future__ import annotations

import hashlib
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
CORE = ROOT / "coq/kernel/foundation/EventSwapCore.v"
FREEZE = ROOT / "research/rounds/2026-09-30-part1-item1.3-round1-freeze.md"
CORE_SHA256 = "a75244fd3c60c9ca3b8b1adaebcb8ef15d72cb4ab0c61435dc5b8540b4e026c2"


def test_item_13_freezes_the_exact_core_source() -> None:
    assert FREEZE.exists(), f"missing freeze record: {FREEZE}"
    assert hashlib.sha256(CORE.read_bytes()).hexdigest() == CORE_SHA256
    text = FREEZE.read_text()
    assert f"EventSwapCore.v SHA-256: `{CORE_SHA256}`" in text


def test_item_13_freezes_exact_targets_and_outcomes() -> None:
    text = FREEZE.read_text()
    assert "Exact target: `swap_preserves_main_results`" in text
    assert "Sanity target: `certification_main_results`" in text
    assert "Prediction for the exact target: REFUTED" in text
    assert "Prediction for the sanity target: PROVED" in text
    assert "~ swap_preserves_main_results" in text
    assert "certification_main_results" in text


def test_item_13_freeze_records_the_full_definition_chain() -> None:
    text = FREEZE.read_text()
    for name in (
        "Reading",
        "permanent_reading",
        "written",
        "latchable",
        "priced",
        "hidden_from_forget",
        "hidden_from_bare",
        "bare_price_inexact",
        "forget_price_inexact",
        "main_results",
        "swap_preserves_main_results",
        "certification_reading",
        "certification_main_results",
    ):
        assert f"Definition {name}" in text
