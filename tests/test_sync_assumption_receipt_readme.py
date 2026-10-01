"""The published README counters are generated from the assumption receipt."""

from __future__ import annotations

import json
from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]


def test_sync_rewrites_every_published_receipt_counter(tmp_path: Path) -> None:
    readme = tmp_path / "README.md"
    readme.write_text(
        """The committed assumption receipt: 1 theorems probed.\n"
        "1 of those theorems are closed under the global context outright; the remaining 2 use only Coq standard-library assumptions.\n"
        "records 1 addressable theorems probed across 1 files and no findings.\n"
        "reports 1 addressable theorems probed across 1 files and no findings.\n"
        "The split: 1 close under the global context outright, and the remaining 2 lean only on Coq-stdlib axiom families.\n"
        "Those families are `functional_extensionality_dep` (1), `eq_rect_eq` (1), the classical-reals pair `sig_forall_dec` (1) and `sig_not_dec` (1), and `classic` (1).\n"
        """
    )
    receipt = tmp_path / "receipt.json"
    receipt.write_text(json.dumps({
        "files_probed": 450,
        "summary": {
        "theorems_probed": 13318,
        "closed_under_global_context": 5965,
        "depend_on_axioms": 7353,
        "unique_axioms_used": {
            "FunctionalExtensionality.functional_extensionality_dep": 7050,
            "Eqdep.Eq_rect_eq.eq_rect_eq": 3849,
            "ClassicalDedekindReals.sig_forall_dec": 1063,
            "ClassicalDedekindReals.sig_not_dec": 309,
            "Classical_Prop.classic": 107,
        },
    }}))
    monograph = tmp_path / "monograph.tex"
    monograph.write_text(
        "The current full-corpus probe covers 1 named theorems across 1 files: "
        "1 close under the global Coq context outright, and 2 use only Coq "
        "standard-library assumptions. Zero project-local axioms appear in "
        "any of the 1 dependency trees.\n"
    )
    distillation = tmp_path / "THIELE_MACHINE.txt"
    distillation.write_text(
        "The receipt committed with this tree covers 1 statements across 1 files: "
        "1 closed and 2 depending on standard-library assumptions.\n"
    )
    citation = tmp_path / "CITATION.cff"
    citation.write_text(
        "  and the mathematical specification. The assumption receipt covers 1\n"
        "  statements across 1 files: 1 are closed under the global context, 2 depend on\n"
    )
    corrections = tmp_path / "corrections.tsv"
    corrections.write_text(
        "document\tline\toriginal\treplacement\treason\n"
        "monograph/monograph.tex\t1\tfrozen monograph\tstale monograph\taudit\n"
        "THIELE_MACHINE.txt\t1\tfrozen distillation\tstale distillation\taudit\n"
        "CITATION.cff\t2\tfrozen citation\tstale citation\taudit\n"
    )

    subprocess.run([
        sys.executable,
        str(ROOT / "scripts/sync_assumption_receipt_readme.py"),
        "--receipt", str(receipt),
        "--readme", str(readme),
        "--monograph", str(monograph),
        "--distillation", str(distillation),
        "--citation", str(citation),
        "--corrections", str(corrections),
    ], check=True)

    text = readme.read_text()
    assert text.count("13,318") == 3
    assert text.count("450 files") == 2
    assert text.count("5,965") == 2
    assert text.count("7,353") == 2
    assert "`functional_extensionality_dep` (7,050)" in text
    assert "`eq_rect_eq` (3,849)" in text
    assert "`sig_forall_dec` (1,063)" in text
    assert "`sig_not_dec` (309)" in text
    assert "`classic` (107)" in text
    assert "13,318 named theorems across 450 files" in monograph.read_text()
    assert "5,965 close under the global Coq context" in monograph.read_text()
    assert "any of the 13,318 dependency trees" in monograph.read_text()
    assert "13,318 statements across 450 files" in distillation.read_text()
    assert "5,965 closed and 7,353" in distillation.read_text()
    assert "covers 13,318" in citation.read_text()
    assert "statements across 450 files: 5,965" in citation.read_text()
    correction_lines = corrections.read_text().splitlines()
    assert correction_lines[1].split("\t")[3] == monograph.read_text().splitlines()[0]
    assert correction_lines[2].split("\t")[3] == distillation.read_text().splitlines()[0]
    assert correction_lines[3].split("\t")[3] == citation.read_text().splitlines()[1]
