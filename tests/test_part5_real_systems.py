from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def test_part5_targets_and_freezes_exist():
    rounds = ROOT / "research/rounds"
    for item in ("5.1", "5.2", "5.3", "5.4", "5.5"):
        assert list(rounds.glob(f"2026-10-01-part5-item{item}-round*-freeze.md"))


def test_necula_consumer_pipeline_is_modeled():
    text = (ROOT / "coq/kernel/reductions/NeculaPCCTarget.v").read_text()
    for token in ("policy_allows", "verification_condition", "PCCProof", "check_program"):
        assert token in text


def test_concrete_machine_cases_are_not_prose_only():
    text = (ROOT / "coq/kernel/reductions/ConcreteRecordMachinesTarget.v").read_text()
    for token in ("tied_step", "untied_step", "junbounded_step", "jbounded_step"):
        assert token in text


def test_tpm_authenticity_is_not_assumed():
    text = (ROOT / "coq/kernel/reductions/TPMQuoteAuthenticity.v").read_text()
    assert "interface_authenticity_refuted" in text
    assert "Print Assumptions tpm_interface_authenticity_refuted" in text


def test_framework_report_does_not_claim_full_embeddings():
    text = (ROOT / "research/rounds/2026-10-01-part5-item5.5-round1-results.md").read_text()
    assert "BLOCKED" in text
    assert "No full embedding" in text

