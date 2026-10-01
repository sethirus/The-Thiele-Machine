from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


PUBLIC_DOCUMENTS = [
    ROOT / "README.md",
    ROOT / "THIELE_MACHINE.txt",
    ROOT / "monograph/monograph.tex",
    ROOT / "monograph/thiele_machine_math_spec.tex",
    ROOT / "CITATION.cff",
    ROOT / "research/rounds/outputs/2026-09-30-v3.4.0-release-notes.md",
]


def test_public_documents_read_as_finished_work():
    process_phrases = [
        "Ground-truth plan outcome",
        "Parts 0--7",
        "Parts 0-7",
        "No Part 7 candidate",
        "expanded ground-truth plan",
        "frozen uniqueness claim",
        "This release presents",
        "now also has",
        "is still missing",
        "remains a conjecture",
        "remains open",
        "had fallen behind",
        "earlier cited-theorem",
        "later exhaustive audit",
        "current committed assumption receipt",
        "A Checked Account with Open Questions",
        "What else belongs on the meter is open",
        "The rest is open",
        "future engineering",
        "What is still open",
    ]
    for path in PUBLIC_DOCUMENTS:
        text = path.read_text()
        for phrase in process_phrases:
            assert phrase not in text, (path, phrase)


def test_public_documents_preserve_the_final_scope_boundary():
    required_ideas = [
        ("threshold",),
        ("recursion theorem",),
        ("RFC 9162",),
        ("cost-framework",),
        ("observer model", "observer map", "modeling choice", "model-dependent"),
        ("conjecture",),
    ]
    for path in PUBLIC_DOCUMENTS:
        text = path.read_text()
        for alternatives in required_ideas:
            assert any(idea.lower() in text.lower() for idea in alternatives), (
                path, alternatives
            )


def test_citation_states_pointer_question_as_a_conjecture():
    text = (ROOT / "CITATION.cff").read_text()
    normalized = " ".join(text.split())
    assert "the pointer criterion is a conjecture" in normalized
    assert "No surveyed external consequence satisfied all four novelty and applicability criteria" in normalized
