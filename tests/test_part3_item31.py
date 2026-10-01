"""TDD acceptance checks for Part 3 Item 3.1."""

from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
CORE = ROOT / "coq/kernel/foundation/VMRecursionTarget.v"
PROOF = ROOT / "coq/kernel/foundation/VMRecursionAudit.v"
FREEZE = ROOT / "research/rounds/2026-10-01-part3-item3.1-round1-freeze.md"
RESULT = ROOT / "research/rounds/2026-10-01-part3-item3.1-round1-results.md"


def test_item31_exact_target_is_frozen() -> None:
    assert CORE.exists() and FREEZE.exists()
    text = FREEZE.read_text()
    assert "vm_guest_recursion_theorem" in text
    assert "vm_guest_rice" in text


def test_item31_closed_existing_execution_results() -> None:
    text = PROOF.read_text()
    assert "Theorem vm_guest_execution_is_actual" in text
    assert "Theorem vm_guest_rice_holds" in text
    assert "Admitted." not in text and "Axiom " not in text


def test_item31_reports_exact_dependency_boundary() -> None:
    text = RESULT.read_text()
    assert "vm_guest_recursion_theorem | BLOCKED" in text
    assert "vm_guest_rice | PROVED" in text
    assert "Rice theorem is independent of the blocked recursion theorem" in text
    assert "Adversarial read: PASS" in text

