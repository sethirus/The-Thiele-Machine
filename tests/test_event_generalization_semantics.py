"""Post-freeze acceptance checks for Part 1, Item 1.2 outcomes."""

from __future__ import annotations

import csv
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
TARGETS = ROOT / "research/rounds/2026-09-30-part1-item1.2-round1-targets.tsv"
EVIDENCE = ROOT / "research/rounds/2026-09-30-part1-item1.2-round1-evidence.tsv"
RESULTS = ROOT / "research/rounds/2026-09-30-part1-item1.2-round1-results.md"
PROOF_SOURCE = ROOT / "coq/kernel/foundation/EventGeneralization.v"


def read_tsv(path: Path) -> list[dict[str, str]]:
    with path.open(newline="") as handle:
        return list(csv.DictReader(handle, delimiter="\t"))


def theorem_statement(source: str, name: str) -> str:
    match = re.search(
        rf"^Theorem\s+{re.escape(name)}\s*:\s*(.*?)\.[ \t]*(?:\(\*.*\*\))?[ \t]*$",
        source,
        flags=re.MULTILINE | re.DOTALL,
    )
    assert match is not None, f"missing theorem declaration: {name}"
    return " ".join(match.group(1).split())


def test_every_frozen_target_has_one_exact_outcome() -> None:
    assert EVIDENCE.exists(), f"missing outcome evidence: {EVIDENCE}"
    assert PROOF_SOURCE.exists(), f"missing result proofs: {PROOF_SOURCE}"
    assert RESULTS.exists(), f"missing result report: {RESULTS}"

    targets = read_tsv(TARGETS)
    evidence = read_tsv(EVIDENCE)
    assert [row["logical_identity"] for row in evidence] == [
        row["logical_identity"] for row in targets
    ]
    assert len(evidence) == 55
    assert set(evidence[0]) == {
        "logical_identity",
        "target_name",
        "predicted_outcome",
        "outcome",
        "result_name",
        "assumptions",
        "definitional",
        "built_in",
        "vacuity",
        "swap",
        "adversarial",
        "wrong_prediction",
        "note",
    }

    source = PROOF_SOURCE.read_text()
    result_names: set[str] = set()
    for frozen, observed in zip(targets, evidence, strict=True):
        identity = frozen["logical_identity"]
        assert observed["target_name"] == frozen["target_name"], identity
        assert observed["predicted_outcome"] == frozen["predicted_outcome"], identity
        assert observed["outcome"] in {"PROVED", "REFUTED", "BLOCKED"}, identity
        assert observed["wrong_prediction"] == (
            "no" if observed["outcome"] == observed["predicted_outcome"] else "yes"
        ), identity
        for field in ("definitional", "built_in", "vacuity", "swap", "adversarial", "note"):
            assert observed[field].strip(), (identity, field)

        if observed["outcome"] == "BLOCKED":
            assert observed["result_name"] == "", identity
            assert observed["assumptions"] == "n/a", identity
            assert all(f"strategy {number}" in observed["note"].lower() for number in (1, 2, 3)), identity
            continue

        result_name = observed["result_name"]
        assert result_name and result_name not in result_names, identity
        result_names.add(result_name)
        assert observed["assumptions"] == "closed", identity
        expected = observed["target_name"]
        if observed["outcome"] == "REFUTED":
            expected = f"~ {expected}"
        assert theorem_statement(source, result_name) == expected, identity

    report = RESULTS.read_text()
    for outcome in ("PROVED", "REFUTED", "BLOCKED"):
        count = sum(row["outcome"] == outcome for row in evidence)
        assert f"- {outcome}: {count}" in report


def test_result_source_is_registered_for_guarded_compilation() -> None:
    project = (ROOT / "coq/_CoqProject").read_text().splitlines()
    assert "kernel/foundation/EventGeneralization.v" in project
