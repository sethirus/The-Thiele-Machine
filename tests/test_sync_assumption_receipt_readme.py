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
    receipt.write_text(json.dumps({"summary": {
        "files_probed": 450,
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

    subprocess.run([
        sys.executable,
        str(ROOT / "scripts/sync_assumption_receipt_readme.py"),
        "--receipt", str(receipt),
        "--readme", str(readme),
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
