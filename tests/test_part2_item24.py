"""TDD acceptance checks for Part 2 Item 2.4."""

from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
CORE = ROOT / "coq/kernel/foundation/CrossBaseGranularityCore.v"
PROOF = ROOT / "coq/kernel/foundation/CrossBaseGranularity.v"
FREEZE = ROOT / "research/rounds/2026-10-01-part2-item2.4-round1-freeze.md"
RESULT = ROOT / "research/rounds/2026-10-01-part2-item2.4-round1-results.md"


def test_item24_frozen_equivalence_exists() -> None:
    assert CORE.exists() and FREEZE.exists()
    text = FREEZE.read_text()
    assert "weak_base_equiv" in text
    assert "weak_equiv_preserves_round4" in text


def test_item24_generic_and_available_base_results_close() -> None:
    text = PROOF.read_text()
    for name in (
        "weak_base_equiv_refl_holds",
        "weak_base_equiv_sym_holds",
        "weak_base_equiv_trans_holds",
        "weak_equiv_preserves_round4_holds",
        "round4_tm_holds",
        "round4_vm_holds",
    ):
        assert f"Theorem {name}" in text
    assert "Admitted." not in text and "Axiom " not in text


def test_item24_reports_named_scope_without_fake_adapters() -> None:
    text = RESULT.read_text()
    assert "TM adapter | PROVED" in text
    assert "VM adapter | PROVED" in text
    assert "RAM adapter | BLOCKED" in text
    assert "L adapter | BLOCKED" in text
    assert "no prose adapter was substituted" in text
    assert "Adversarial read: PASS" in text
