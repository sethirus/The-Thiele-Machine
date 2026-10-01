"""docs/RESULTS.md states the settled results, and its citations are checked.

Every identifier the document cites in a code span must be declared in
coq/. Every cited theorem must appear in the assumption receipt, closed
under the global context unless the document's "Standard-library axioms"
list names it; a listed theorem may use only the standard-library axioms
named there. The two result tables are checked against the Coq statements
they summarize.
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
PROBE = COQ / "AssumptionsProbeAll.v"
RECEIPT_TEXT = ROOT / "artifacts" / "print_assumptions_all_proofs.txt"
GENERALIZATION = COQ / "kernel" / "foundation" / "EventGeneralization.v"
GENERALIZATION_TARGETS = COQ / "kernel" / "foundation" / "EventGeneralizationTargets.v"
GENERIC_AUDIT = COQ / "kernel" / "nfi" / "EventGenericAudit.v"

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
GENERIC_ROW = re.compile(
    r"^\| `(\w+)` \| `(\w+)` \| (discharged|Landauer premise kept) \|$", re.MULTILINE
)
SPECIFIC_ROW = re.compile(
    r"^\| `(\w+)` \| `(\w+)` \| (proved|refuted) \| `(\w+)` \|$", re.MULTILINE
)


def doc_text() -> str:
    return DOC.read_text(encoding="utf-8")


@lru_cache(maxsize=1)
def declarations() -> dict[str, set[str]]:
    kinds: dict[str, set[str]] = {}
    for path in COQ.rglob("*.v"):
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


def theorem_statement(source: str, name: str) -> str:
    match = re.search(
        rf"^Theorem\s+{re.escape(name)}\s*:\s*(.*?)\.\s*(?:Proof\.|$)",
        source,
        flags=re.MULTILINE | re.DOTALL,
    )
    assert match is not None, f"missing theorem: {name}"
    return " ".join(match.group(1).split())


def test_every_cited_identifier_is_declared_in_coq():
    known = declarations()
    missing = sorted(name for name in cited_identifiers(doc_text()) if name not in known)
    assert not missing, missing


def test_cited_coq_files_exist():
    files = {span for span in re.findall(r"`([\w.]+\.v)`", doc_text())}
    present = {path.name for path in COQ.rglob("*.v")}
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


def test_event_generic_table_names_closed_specializations():
    rows = GENERIC_ROW.findall(doc_text())
    assert len(rows) == 49
    assert sum(status == "Landauer premise kept" for _, _, status in rows) == 4
    audit = GENERIC_AUDIT.read_text(encoding="utf-8")
    witnesses = [witness for _, witness, _ in rows]
    assert len(set(witnesses)) == 49
    for source, witness, _ in rows:
        assert source in declarations(), source
        assert re.search(rf"^(?:Theorem|Lemma|Definition)\s+{witness}\b", audit, re.MULTILINE), witness


def test_certification_table_matches_event_generic_wrappers():
    rows = SPECIFIC_ROW.findall(doc_text())
    assert len(rows) == 55
    assert sum(status == "proved" for _, _, status, _ in rows) == 19
    assert sum(status == "refuted" for _, _, status, _ in rows) == 36
    wrappers = GENERALIZATION.read_text(encoding="utf-8")
    targets = GENERALIZATION_TARGETS.read_text(encoding="utf-8")
    assert len({wrapper for *_, wrapper in rows}) == 55
    for source, target, status, wrapper in rows:
        assert source in declarations(), source
        assert re.search(rf"^Definition\s+{target}\s*:\s*Prop", targets, re.MULTILINE), target
        expected = target if status == "proved" else f"~ {target}"
        assert theorem_statement(wrappers, wrapper) == expected, wrapper


def test_document_is_ground_truth_not_a_log():
    text = doc_text()
    forbidden = re.compile(
        r"\b(round|rounds|item|items|freeze|frozen|was|were|previously|no longer|"
        r"now|predicted|prediction|predictions|we|our)\b|\bPart \d|—|–",
        re.IGNORECASE,
    )
    hits = [match.group(0) for match in forbidden.finditer(text)]
    assert not hits, hits
