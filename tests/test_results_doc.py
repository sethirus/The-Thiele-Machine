"""docs/RESULTS.md states the settled results, and its citations are checked.

Every identifier the document cites in a code span must be declared in
coq/ or minimal/. Every cited theorem must appear in the assumption receipt,
closed under the global context unless the document's "Standard-library
axioms" list names it; a listed theorem may use only the standard-library
axioms named there.
"""

from __future__ import annotations

import re
import sys
from functools import lru_cache
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
from check_assumption_receipt import theorem_results  # noqa: E402

DOC = ROOT / "docs" / "RESULTS.md"
COQ = ROOT / "coq"
MINIMAL = ROOT / "minimal"
SOURCE_ROOTS = (COQ, MINIMAL)
PROBE = COQ / "AssumptionsProbeAll.v"
RECEIPT_TEXT = ROOT / "artifacts" / "print_assumptions_all_proofs.txt"

THEOREM_KINDS = {"Theorem", "Lemma", "Corollary", "Proposition", "Fact", "Remark"}
DECLARATION = re.compile(
    r"^\s*(Theorem|Lemma|Corollary|Proposition|Fact|Remark|Example|Definition|"
    r"Fixpoint|CoFixpoint|Inductive|CoInductive|Record|Structure|Class|Instance|"
    r"Module\s+Type|Module|Let)\s+([A-Za-z_][\w']*)",
    re.MULTILINE,
)
IDENTIFIER = re.compile(r"^[A-Za-z_][\w']*$")
STDLIB_AXIOMS = {
    "ClassicalDedekindReals.sig_forall_dec",
    "ClassicalDedekindReals.sig_not_dec",
    "Classical_Prop.classic",
    "FunctionalExtensionality.functional_extensionality_dep",
}


def doc_text() -> str:
    return DOC.read_text(encoding="utf-8")


@lru_cache(maxsize=1)
def declarations() -> dict[str, set[str]]:
    kinds: dict[str, set[str]] = {}
    for path in (p for root in SOURCE_ROOTS for p in root.rglob("*.v")):
        if path == PROBE:
            continue
        for kind, name in DECLARATION.findall(path.read_text(encoding="utf-8", errors="ignore")):
            kinds.setdefault(name, set()).add(" ".join(kind.split()))
    return kinds


@lru_cache(maxsize=1)
def receipt() -> dict[str, list[tuple[str, ...]]]:
    results = theorem_results(
        PROBE.read_text(encoding="utf-8"), RECEIPT_TEXT.read_text(encoding="utf-8")
    )
    by_name: dict[str, list[tuple[str, ...]]] = {}
    for query, axioms in results.items():
        name = query.removeprefix("Print Assumptions ").rstrip(".").rsplit(".", 1)[-1]
        by_name.setdefault(name, []).append(
            tuple(axiom.split(":", 1)[0].strip() for axiom in axioms)
        )
    return by_name


def cited_identifiers(text: str) -> set[str]:
    return {span for span in re.findall(r"`([^`\n]+)`", text) if IDENTIFIER.match(span)}


def stdlib_list(text: str) -> set[str]:
    section = text.split("## Standard-library axioms", 1)[1]
    return set(re.findall(r"^- `(\w+)`$", section, flags=re.MULTILINE))


def test_every_cited_identifier_is_declared_in_coq():
    known = declarations()
    missing = sorted(name for name in cited_identifiers(doc_text()) if name not in known)
    assert not missing, missing


def test_cited_coq_files_exist():
    files = {span for span in re.findall(r"`([\w.]+\.v)`", doc_text())}
    present = {path.name for root in SOURCE_ROOTS for path in root.rglob("*.v")}
    assert files <= present, sorted(files - present)


def test_cited_theorems_match_the_assumption_receipt():
    text = doc_text()
    listed = stdlib_list(text)
    known = declarations()
    found = receipt()
    not_closed = set()
    for name in sorted(cited_identifiers(text)):
        if not known.get(name, set()) & THEOREM_KINDS:
            continue
        assert name in found, f"{name} is not in the assumption receipt"
        results = found[name]
        if any(axioms for axioms in results):
            not_closed.add(name)
            for axioms in results:
                assert set(axioms) <= STDLIB_AXIOMS, (name, axioms)
    assert listed == not_closed, (
        sorted(listed - not_closed), sorted(not_closed - listed)
    )


def test_document_is_ground_truth_not_a_log():
    text = doc_text()
    forbidden = re.compile(
        r"\b(round|rounds|item|items|freeze|frozen|was|were|previously|no longer|"
        r"now|predicted|prediction|predictions|we|our)\b|\bPart \d|—|–",
        re.IGNORECASE,
    )
    hits = [match.group(0) for match in forbidden.finditer(text)]
    assert not hits, hits
