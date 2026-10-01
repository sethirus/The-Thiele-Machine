from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
PROOF = ROOT / "coq/kernel/foundation/VMGuestRecursion.v"
TARGET = ROOT / "coq/kernel/foundation/VMRecursionTarget.v"


def test_internal_guest_recursion_theorem_is_closed_and_unweakened():
    text = PROOF.read_text()
    assert "Theorem vm_guest_recursion_theorem_closed :" in text
    assert "vm_guest_recursion_theorem." in text
    assert "Print Assumptions vm_guest_recursion_theorem_closed." in text
    for forbidden in ("Axiom ", "Admitted.", "admit.", "Hypothesis "):
        assert forbidden not in text


def test_frozen_target_still_quantifies_over_represented_transformers():
    text = TARGET.read_text()
    assert "Definition vm_guest_recursion_theorem : Prop :=" in text
    assert "g_represents_transformer D F ->" in text
    assert "exists p, g_wf_program p /\\ g_equiv p (F p)." in text
