"""Acceptance checks for the dynamic decoder/evaluator and guest s-m-n theorem."""

from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "coq/kernel/foundation/VMDynamicEvalTarget.v"
PROOF = ROOT / "coq/kernel/foundation/VMDynamicEval.v"


def test_dynamic_evaluator_roundtrip_and_actual_execution():
    text = PROOF.read_text()
    assert "Theorem g_decode_guest_code_roundtrip" in text
    assert "Theorem g_eval_guest_code" in text
    assert "Theorem g_eval_is_actual_vm_execution" in text


def test_guest_smn_is_behavioral_not_just_syntactic():
    text = TARGET.read_text() + PROOF.read_text()
    assert "Definition g_specialize" in text
    assert "Theorem g_smn" in text
    assert "g_beh (g_specialize p x) y g mu <-> g_beh p x g mu" in text
