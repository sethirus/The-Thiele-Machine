"""The Casper accountable-safety path is constructive, not merely axiom-clean by convention."""

from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
CASPER = ROOT / "coq/kernel/reductions/CasperFFG.v"


def test_casper_source_has_no_classical_shortcut():
    text = CASPER.read_text()
    assert "Import Arith.PeanoNat Lia Relations Classical." not in text
    assert "classic (" not in text


def test_accountable_safety_statement_is_unchanged():
    text = CASPER.read_text()
    assert (
        "Theorem accountable_safety : forall s, finalization_fork s -> "
        "quorum_slashed s."
    ) in text
    assert "Print Assumptions accountable_safety." in text
