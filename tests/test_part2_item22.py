"""TDD acceptance checks for Part 2 Item 2.2."""

from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
CORE = ROOT / "coq/kernel/foundation/PricedRevocationCore.v"
PROOF = ROOT / "coq/kernel/foundation/PricedRevocation.v"
FREEZE = ROOT / "research/rounds/2026-10-01-part2-item2.2-round1-freeze.md"
RESULT = ROOT / "research/rounds/2026-10-01-part2-item2.2-round1-results.md"


def test_item22_freeze_exists_before_results() -> None:
    assert CORE.exists()
    assert FREEZE.exists()
    text = FREEZE.read_text()
    for target in (
        "actual_revocation_excludes_permanence",
        "revocation_price_does_not_price_writes",
        "casper_conflict_is_accountable",
        "casper_write_without_slashing",
    ):
        assert target in text


def test_item22_exact_results_close() -> None:
    text = PROOF.read_text()
    assert "Theorem actual_revocation_excludes_permanence_holds" in text
    assert "Theorem revocation_price_does_not_price_writes_refuted" in text
    assert "Theorem casper_conflict_is_accountable_holds" in text
    assert "Theorem casper_write_without_slashing_holds" in text
    assert "Admitted." not in text
    assert "Axiom " not in text


def test_item22_report_draws_the_casper_boundary() -> None:
    text = RESULT.read_text()
    assert "literal permanent-record axis: OUTSIDE" in text
    assert "accountable-conflict generalization: INSIDE" in text
    assert "not a transition-level deletion" in text
    assert "Adversarial read: PASS" in text

