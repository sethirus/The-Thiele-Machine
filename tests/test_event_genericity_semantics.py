"""Post-freeze acceptance test for Item 1.1 semantic evidence."""

from __future__ import annotations

import csv
import hashlib
import importlib.util
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
PREDICTIONS = ROOT / "research/rounds/2026-09-30-part1-item1.1-round2-predictions.tsv"
EVIDENCE = ROOT / "research/rounds/2026-09-30-part1-item1.1-round2-evidence.tsv"
AUDIT_SOURCE = "coq/kernel/nfi/EventGenericAudit.v"
MODULE_PATH = ROOT / "scripts" / "event_genericity_inventory.py"
SPEC = importlib.util.spec_from_file_location("event_genericity_inventory", MODULE_PATH)
assert SPEC is not None and SPEC.loader is not None
inventory = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = inventory
SPEC.loader.exec_module(inventory)


def read_tsv(path: Path) -> list[dict[str, str]]:
    with path.open(newline="") as handle:
        return list(csv.DictReader(handle, delimiter="\t"))


def statement_sha256(source: Path, line: int) -> str:
    lines = source.read_text().splitlines()
    statement: list[str] = []
    for item in lines[line - 1 :]:
        before_proof = item.split("Proof.", 1)[0].split("Admitted.", 1)[0]
        statement.append(before_proof.rstrip())
        if "Proof." in item or "Admitted." in item:
            break
    else:
        raise AssertionError(f"proof boundary not found at {source}:{line}")
    payload = "\n".join(statement).rstrip() + "\n"
    return hashlib.sha256(payload.encode()).hexdigest()


def test_every_frozen_identity_has_exact_statement_evidence() -> None:
    assert EVIDENCE.exists(), f"missing post-freeze semantic evidence: {EVIDENCE}"
    predictions = read_tsv(PREDICTIONS)
    evidence = read_tsv(EVIDENCE)
    assert [row["logical_identity"] for row in evidence] == [
        row["logical_identity"] for row in predictions
    ]

    declarations = inventory.proof_declarations(ROOT)
    proof_sources = inventory.proof_declarations(ROOT)
    expected_columns = {
        "logical_identity",
        "statement_sha256",
        "observed_class",
        "evidence_status",
        "coq_witness",
        "audit_note",
    }
    assert set(evidence[0]) == expected_columns

    seen_witnesses: set[str] = set()
    for predicted, observed in zip(predictions, evidence, strict=True):
        identity = predicted["logical_identity"]
        declaration = declarations[identity]
        assert observed["observed_class"] == predicted["predicted_class"], identity
        assert observed["statement_sha256"] == statement_sha256(
            ROOT / declaration.source, declaration.line
        ), identity
        assert observed["audit_note"].strip(), identity

        needs_coq_witness = (
            predicted["predicted_class"] == "G"
            or declaration.addressability != "addressable"
        )
        witness = observed["coq_witness"]
        if needs_coq_witness:
            assert witness and witness not in seen_witnesses, identity
            seen_witnesses.add(witness)
            assert witness in proof_sources, (identity, witness)
            assert proof_sources[witness].source == AUDIT_SOURCE, (identity, witness)
        else:
            assert witness == "", identity

        if predicted["predicted_class"] == "G":
            assert observed["evidence_status"] in {"CLOSED", "PARTIAL"}, identity
        else:
            assert observed["evidence_status"] == "STATEMENT_AUDIT", identity

    assert sum(row["observed_class"] == "G" for row in evidence) == 49
    assert len(seen_witnesses) == 52


def test_semantic_audit_source_is_registered_for_guarded_compilation() -> None:
    project = (ROOT / "coq" / "_CoqProject").read_text().splitlines()
    assert "kernel/nfi/EventGenericAudit.v" in project
