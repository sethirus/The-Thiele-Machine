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
    for path in PUBLIC_DOCUMENTS + [ROOT / "docs/RESULTS.md"]:
        text = path.read_text(encoding="utf-8")
        for phrase in process_phrases:
            assert phrase not in text, (path, phrase)


def test_public_documents_preserve_the_scope_boundary():
    required_ideas = [
        ("threshold",),
        ("recursion theorem",),
        ("RFC 9162",),
        ("cost-framework",),
        ("observer model", "observer map", "modeling choice", "model-dependent"),
        ("conjecture", "thesis"),
    ]
    for path in PUBLIC_DOCUMENTS:
        text = path.read_text(encoding="utf-8").lower()
        for alternatives in required_ideas:
            assert any(idea.lower() in text for idea in alternatives), (path, alternatives)


def test_pointer_criterion_is_stated_as_a_thesis():
    monograph = normalized(ROOT / "monograph/monograph.tex")
    assert r"\label{sec:pointer}" in monograph
    # The book states the pointer criterion as a thesis (its worldly terms,
    # "faithfully model" and "deployed", can't be defined; the others are).
    assert r"\begin{thesis}[The pointer thesis]" in monograph
    assert "The thesis leans on two notions with no precise mathematical definition" in monograph
    assert "which systems count as" in monograph and "independent" in monograph
    assert "The general pointer criterion is a thesis." in normalized(ROOT / "README.md")
    assert "The pointer criterion is a thesis" in normalized(
        ROOT / "monograph/thiele_machine_math_spec.tex"
    )
    assert "The pointer-observable criterion is a thesis." in normalized(
        ROOT / "docs/RESULTS.md"
    )
    citation = normalized(ROOT / "CITATION.cff")
    assert "the pointer criterion is a thesis" in citation
    assert (
        "No surveyed external consequence satisfied all four novelty and applicability criteria"
        in citation
    )
