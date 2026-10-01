"""Semantic acceptance checks for Part 2 Item 2.1."""

from hashlib import sha256
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
CORE = ROOT / "coq/kernel/foundation/GrowingRecordCore.v"
PROOF = ROOT / "coq/kernel/foundation/GrowingRecord.v"
RESULT = ROOT / "research/rounds/2026-10-01-part2-item2.1-round1-results.md"


def test_frozen_core_is_unchanged() -> None:
    assert sha256(CORE.read_bytes()).hexdigest() == (
        "8f43e6636d5c7f32c9a32d01755749648ffe0bcc125d15f22d4a54b708e61530"
    )


def test_exact_targets_have_closed_named_results() -> None:
    text = PROOF.read_text()
    for declaration in (
        "Theorem growing_record_decomposes_holds : growing_record_decomposes.",
        "Theorem thresholds_determine_record_holds : thresholds_determine_record.",
        "Theorem record_price_iff_threshold_price_holds : record_price_iff_threshold_price.",
        "Theorem one_latch_refuted : ~ one_latch_suffices.",
        "Theorem chain_needs_bits_holds : chain_needs_bits.",
    ):
        assert declaration in text
    assert "Admitted." not in text
    assert "Axiom " not in text
    assert "Parameter " not in text


def test_result_reports_each_outcome_and_hollowness_check() -> None:
    text = RESULT.read_text()
    assert "growing_record_decomposes | PROVED" in text
    assert "thresholds_determine_record | PROVED" in text
    assert "record_price_iff_threshold_price | PROVED" in text
    assert "one_latch_suffices | REFUTED" in text
    assert "chain_needs_bits | PROVED" in text
    for check in (
        "Definitional:", "Built in:", "Vacuity:", "Swap test:",
        "Adversarial read:",
    ):
        assert text.count(check) >= 5
    assert "Adversarial read: PASS" in text

