from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def test_part6_freeze_precedes_result_contract():
    freeze = ROOT / "research/rounds/2026-10-01-part6-round1-freeze.md"
    text = freeze.read_text()
    assert "record-proliferation-survey-target.v.sha256" in text
    assert "Predictions" in text


def test_twelve_candidates_are_reported():
    rows = (ROOT / "research/rounds/2026-10-01-part6-round1-measurements.tsv").read_text().splitlines()
    assert len(rows) == 13
    assert rows[0].startswith("candidate\t")


def test_part6_exact_bundle_and_swap_compile_contract():
    proof = (ROOT / "coq/kernel/frontier/RecordProliferationSurvey.v").read_text()
    assert "Theorem twelve_candidate_measurements_checked" in proof
    assert "Theorem swapped_event_is_pointer_checked" in proof


def test_strong_conjecture_is_not_resurrected():
    report = (ROOT / "research/rounds/2026-10-01-part6-round1-results.md").read_text()
    assert "6.3 | MODEL COUNTEREXAMPLE PROVED; real-system conclusion MODEL-DEPENDENT" in report
    assert "modeling judgment" in report
