"""The semantic audit reads the prose around a citation, within its section.

Text across a section break belongs to another argument. A novelty
disclaimer in the next section must not count as prose about the citation.
"""

from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import audit_monograph_semantics as audit  # noqa: E402


def windows(tmp_path: Path, name: str, body: str) -> dict[str, str]:
    path = tmp_path / name
    path.write_text(body)
    return {token: prose for token, _, prose in audit.extract_citations_with_prose(path)}


def test_window_stops_at_the_next_section(tmp_path: Path) -> None:
    body = (
        "The floor restated as \\code{some\\_alias}, which is that theorem.\n\n"
        "\\section{Attribution}\n"
        "I have not read widely enough to say any result is historically new.\n"
    )
    prose = windows(tmp_path, "a.tex", body)["some_alias"]
    assert "restated" in prose
    assert "historically" not in prose


def test_window_stops_at_the_previous_section(tmp_path: Path) -> None:
    body = (
        "Everything proved here is new.\n\n"
        "\\subsection{Falsifiers}\n"
        "Break \\code{some\\_alias} to refute it.\n"
    )
    prose = windows(tmp_path, "b.tex", body)["some_alias"]
    assert "break" in prose
    assert "proved here" not in prose


def test_markdown_window_stops_at_headings(tmp_path: Path) -> None:
    body = "Break `some_alias` to refute it.\n\n## Novelty\nEverything here is new.\n"
    prose = windows(tmp_path, "c.md", body)["some_alias"]
    assert "refute" in prose
    assert "novelty" not in prose.lower()


def test_window_keeps_text_in_the_same_section(tmp_path: Path) -> None:
    body = (
        "\\section{Results}\n"
        "This is established as a new theorem, \\code{some\\_alias}, in the kernel.\n"
    )
    prose = windows(tmp_path, "d.tex", body)["some_alias"]
    assert "established" in prose and "new" in prose


def test_wrapped_identifiers_are_read(tmp_path: Path) -> None:
    body = "See \\texttt{some\\_\\allowbreak{}alias} for the floor.\n"
    assert "some_alias" in windows(tmp_path, "e.tex", body)


def test_markdown_table_row_is_its_own_window(tmp_path: Path) -> None:
    body = (
        "| Reduction | The floor, `some_alias`. | file.v |\n"
        "| Ledger | It lists a selected set of established claims. | other.v |\n"
    )
    prose = windows(tmp_path, "f.md", body)["some_alias"]
    assert "floor" in prose
    assert "established" not in prose


def test_published_documents_have_no_structural_concerns() -> None:
    import subprocess

    result = subprocess.run(
        [sys.executable, str(ROOT / "scripts" / "audit_monograph_semantics.py")],
        cwd=ROOT, capture_output=True, text=True, timeout=600,
    )
    assert result.returncode == 0, result.stdout[-4000:]
