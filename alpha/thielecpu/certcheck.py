# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

"""Deterministic certificate checkers for LASSERT instructions."""

from __future__ import annotations

from collections import deque
from dataclasses import dataclass
import hashlib
from pathlib import Path
from typing import Dict, Iterable, Iterator, List, Sequence

from .cnf import CanonicalCNF, canonicalise_cnf


class CertificateError(ValueError):
    """Raised when a certificate fails verification."""


@dataclass(frozen=True)
class LassertCertificate:
    """Metadata describing a validated LASSERT certificate."""

    cnf: CanonicalCNF
    proof_type: str
    proof_sha256: str
    status: str  # "SAT" or "UNSAT"


def _parse_lrat_lines(text: str) -> Iterator[str]:
    for raw_line in text.splitlines():
        line = raw_line.strip()
        if not line or line.startswith("c"):
            continue
        yield line


def _unit_conflict(clauses: Sequence[Sequence[int]], assumptions: Iterable[int]) -> bool:
    assignments: Dict[int, bool] = {}
    queue: deque[int] = deque()
    for lit in assumptions:
        queue.append(int(lit))
    # Seed with existing unit clauses
    for clause in clauses:
        if len(clause) == 1:
            queue.append(clause[0])
    while queue:
        lit = queue.pop()
        var = abs(lit)
        value = lit > 0
        existing = assignments.get(var)
        if existing is not None:
            if existing != value:
                return True
            continue
        assignments[var] = value
        for clause in clauses:
            satisfied = False
            undecided: List[int] = []
            for entry in clause:
                entry_var = abs(entry)
                assignment = assignments.get(entry_var)
                if assignment is None:
                    undecided.append(entry)
                elif assignment == (entry > 0):
                    satisfied = True
                    break
            if satisfied:
                continue
            pruned = [lit for lit in undecided if assignments.get(abs(lit)) is None]
            if not pruned:
                return True
            if len(pruned) == 1:
                queue.append(pruned[0])
    return False


def _verify_rup_clause(clause: Sequence[int], database: Dict[int, Sequence[int]]) -> bool:
    if _unit_conflict(list(database.values()), (-lit for lit in clause)):
        return True
    return False


def check_lrat(cnf_text: str, proof_text: str) -> bool:
    """Verify the LRAT proof ``proof_text`` against ``cnf_text``."""

    canonical = canonicalise_cnf(cnf_text)
    clause_db: Dict[int, Sequence[int]] = {
        idx + 1: clause for idx, clause in enumerate(canonical.clauses)
    }
    derived_empty = False

    for line in _parse_lrat_lines(proof_text):
        parts = line.split()
        if not parts:
            continue
        if parts[0] == "d":
            deletions = [int(token) for token in parts[1:] if token != "0"]
            for did in deletions:
                clause_db.pop(abs(did), None)
            continue
        try:
            clause_id = int(parts[0])
        except ValueError as exc:
            raise CertificateError(f"invalid LRAT line: {line!r}") from exc
        clause_literals: List[int] = []
        idx = 1
        while idx < len(parts) and parts[idx] != "0":
            clause_literals.append(int(parts[idx]))
            idx += 1
        if idx >= len(parts):
            hints: List[int] = []
            deletions: List[int] = []
        else:
            idx += 1  # skip the zero
            hints = []
            while idx < len(parts) and parts[idx] != "0":
                hints.append(int(parts[idx]))
                idx += 1
            if idx < len(parts):
                idx += 1
            deletions = []
            while idx < len(parts) and parts[idx] != "0":
                deletions.append(int(parts[idx]))
                idx += 1
        if clause_literals:
            dedup = {lit for lit in clause_literals if lit != 0}
            clause_tuple = tuple(
                sorted(dedup, key=lambda lit: (abs(lit), lit > 0))
            )
        else:
            clause_tuple = tuple()
        if not _verify_rup_clause(clause_tuple, clause_db):
            return False
        clause_db[clause_id] = clause_tuple
        if len(clause_tuple) == 0:
            derived_empty = True
        for did in deletions:
            clause_db.pop(abs(did), None)
    return derived_empty


def _parse_assignment(text: str) -> Dict[int, bool]:
    assignments: Dict[int, bool] = {}
    for token in text.replace("\n", " ").split():
        if token == "0":
            continue
        if "=" in token:
            name, value = token.split("=", 1)
            if not name:
                raise CertificateError(f"invalid assignment token: {token!r}")
            try:
                var = int(name.lstrip("vV"))
            except ValueError as exc:
                raise CertificateError(f"invalid variable in model: {token!r}") from exc
            value_bool = value.lower() not in {"0", "false", "f"}
        else:
            try:
                literal = int(token)
            except ValueError as exc:
                raise CertificateError(f"invalid literal in model: {token!r}") from exc
            if literal == 0:
                continue
            var = abs(literal)
            value_bool = literal > 0
        assignments[var] = value_bool
    return assignments


def check_model(cnf_text: str, assignment_text: str) -> bool:
    canonical = canonicalise_cnf(cnf_text)
    assignments = _parse_assignment(assignment_text)
    if len(assignments) < canonical.num_vars:
        return False
    for clause in canonical.clauses:
        satisfied = False
        for lit in clause:
            value = assignments.get(abs(lit))
            if value is None:
                return False
            if value == (lit > 0):
                satisfied = True
                break
        if not satisfied:
            return False
    return True


def load_text(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def verify_certificate(
    *,
    cnf_path: Path,
    proof_type: str,
    proof_path: Path | None = None,
    model_path: Path | None = None,
) -> LassertCertificate:
    cnf_text = load_text(cnf_path)
    canonical = canonicalise_cnf(cnf_text)
    if proof_type.upper() == "LRAT":
        if proof_path is None:
            raise CertificateError("LRAT proof requires proof_path")
        proof_text = load_text(proof_path)
        if not check_lrat(canonical.text, proof_text):
            raise CertificateError("LRAT proof verification failed")
        proof_sha = hashlib.sha256(proof_text.encode("utf-8")).hexdigest()
        status = "UNSAT"
    elif proof_type.upper() == "MODEL":
        if model_path is None:
            raise CertificateError("MODEL proof requires model_path")
        model_text = load_text(model_path)
        if not check_model(canonical.text, model_text):
            raise CertificateError("model does not satisfy CNF")
        proof_sha = hashlib.sha256(model_text.encode("utf-8")).hexdigest()
        status = "SAT"
    else:
        raise CertificateError(f"unsupported proof type: {proof_type}")
    return LassertCertificate(
        cnf=canonical,
        proof_type=proof_type.upper(),
        proof_sha256=proof_sha,
        status=status,
    )


__all__ = [
    "CertificateError",
    "LassertCertificate",
    "check_lrat",
    "check_model",
    "verify_certificate",
]
