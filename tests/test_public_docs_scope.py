"""The public documents read as finished work and keep their scope boundary."""

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

PUBLIC_DOCUMENTS = [
    ROOT / "README.md",
    ROOT / "THIELE_MACHINE.txt",
    ROOT / "monograph/monograph.tex",
    ROOT / "monograph/thiele_machine_math_spec.tex",
    ROOT / "CITATION.cff",
]


def normalized(path: Path) -> str:
    return " ".join(path.read_text(encoding="utf-8").split())


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
        "research/" + "rounds",
    ]
    for path in PUBLIC_DOCUMENTS + [ROOT / "coq/RESULTS.md"]:
        text = path.read_text(encoding="utf-8")
        for phrase in process_phrases:
            assert phrase not in text, (path, phrase)


def test_public_documents_preserve_the_scope_boundary():
    # Every public document says which claims are theses, names Landauer's
    # principle as an assumption, and keeps chosen apart from shown.
    required_ideas = [
        ("thesis",),
        ("landauer",),
        ("chosen",),
        ("shown",),
    ]
    for path in PUBLIC_DOCUMENTS:
        text = path.read_text(encoding="utf-8").lower()
        for alternatives in required_ideas:
            assert any(idea in text for idea in alternatives), (path, alternatives)


def test_pointer_criterion_is_stated_as_a_thesis():
    monograph = normalized(ROOT / "monograph/monograph.tex")
    assert r"\label{sec:worth-keeping}" in monograph
    assert "The pointer thesis: the established record is the event copied and relied on" in monograph
    assert "& thesis & 19" in monograph
    spec = normalized(ROOT / "monograph/thiele_machine_math_spec.tex")
    assert r"\begin{thesis}" in spec and "pointer" in spec.lower()
    assert "the pointer thesis (Chapter 19)" in normalized(ROOT / "README.md")
    assert "The pointer-observable criterion is a thesis." in normalized(
        ROOT / "coq/RESULTS.md"
    )
    assert "the pointer thesis and the Thiele thesis are theses" in normalized(ROOT / "CITATION.cff")
