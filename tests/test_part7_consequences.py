from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def test_part7_survey_and_ranked_candidates_exist():
    survey = (ROOT / "research/rounds/2026-10-01-part7-field-survey.tsv").read_text()
    assert len([line for line in survey.splitlines() if line.strip()]) >= 11
    freeze = (ROOT / "research/rounds/2026-10-01-part7-top5-round1-freeze.md").read_text()
    assert "real-system-consequences-target.v.sha256" in freeze


def test_top_five_have_closed_named_results():
    proof = (ROOT / "coq/kernel/reductions/RealSystemConsequences.v").read_text()
    for name in (
        "ct_local_view_insufficient",
        "tpm_selection_binding_is_necessary",
        "weak_subjective_suffix_insufficient",
        "wal_ack_requires_durability",
        "audit_local_snapshot_insufficient",
    ):
        assert f"Theorem {name}" in proof


def test_no_part7_novelty_is_fabricated():
    result = (ROOT / "research/rounds/2026-10-01-part7-results.md").read_text()
    assert "No candidate passed all four criteria" in result
    assert "PROVED BUT KNOWN" in result
    assert "list exhausted" in result

