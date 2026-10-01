"""TDD acceptance checks for Part 2 Item 2.3."""

from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
CORE = ROOT / "coq/kernel/foundation/ProbabilisticRecordCore.v"
PROOF = ROOT / "coq/kernel/foundation/ProbabilisticRecord.v"
FREEZE = ROOT / "research/rounds/2026-10-01-part2-item2.3-round1-freeze.md"
RESULT = ROOT / "research/rounds/2026-10-01-part2-item2.3-round1-results.md"


def test_item23_frozen_targets_exist() -> None:
    assert CORE.exists() and FREEZE.exists()
    freeze = FREEZE.read_text()
    assert "deterministic_latch_handles_branching" in freeze
    assert "schedule_determines_probabilities" in freeze
    assert "probability_preserving_equivalence_reflexive" in freeze


def test_item23_results_close_without_project_axioms() -> None:
    text = PROOF.read_text()
    assert "Theorem deterministic_latch_handles_branching_refuted" in text
    assert "Theorem schedule_determines_probabilities_refuted" in text
    assert "Theorem probability_preserving_equivalence_reflexive_holds" in text
    assert "Admitted." not in text and "Axiom " not in text


def test_item23_report_answers_uniqueness_question() -> None:
    text = RESULT.read_text()
    assert "uniqueness up to schedule: REFUTED" in text
    assert "probability kernel must be preserved" in text
    assert "Adversarial read: PASS" in text

