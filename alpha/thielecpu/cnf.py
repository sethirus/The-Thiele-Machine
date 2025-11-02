# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

"""Canonical DIMACS CNF parsing and normalisation utilities."""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
from typing import List, Sequence


@dataclass(frozen=True)
class CanonicalCNF:
    """Canonical representation of a DIMACS CNF formula."""

    clauses: Sequence[tuple[int, ...]]
    num_vars: int
    text: str

    @property
    def num_clauses(self) -> int:
        return len(self.clauses)

    @property
    def sha256(self) -> str:
        return hashlib.sha256(self.text.encode("utf-8")).hexdigest()


def parse_dimacs_cnf(text: str) -> List[List[int]]:
    """Parse ``text`` into a list of clauses (lists of ints)."""

    clauses: List[List[int]] = []
    current: List[int] = []
    header_seen = False
    num_vars = None
    num_clauses = None

    for raw_line in text.splitlines():
        line = raw_line.strip()
        if not line or line.startswith("c"):
            continue
        if line.startswith("p"):
            parts = line.split()
            if len(parts) != 4 or parts[1].lower() != "cnf":
                raise ValueError(f"invalid DIMACS header: {line!r}")
            try:
                num_vars = int(parts[2])
                num_clauses = int(parts[3])
            except ValueError as exc:
                raise ValueError(f"invalid DIMACS header counts: {line!r}") from exc
            header_seen = True
            continue
        for token in line.split():
            try:
                literal = int(token)
            except ValueError as exc:
                raise ValueError(f"invalid literal token: {token!r}") from exc
            if literal == 0:
                if not current:
                    raise ValueError("empty clause encountered without literals")
                clauses.append(current)
                current = []
            else:
                current.append(literal)
    if current:
        raise ValueError("unterminated clause at end of CNF")
    if not header_seen:
        raise ValueError("DIMACS CNF is missing a 'p cnf' header")
    if num_clauses is not None and num_clauses != len(clauses):
        raise ValueError(
            f"DIMACS header declares {num_clauses} clauses but parsed {len(clauses)}"
        )
    return clauses


def canonicalise_cnf(text: str) -> CanonicalCNF:
    """Return the canonicalised CNF representation for ``text``."""

    clauses = parse_dimacs_cnf(text)
    var_ids = sorted({abs(lit) for clause in clauses for lit in clause})
    mapping = {var: idx + 1 for idx, var in enumerate(var_ids)}

    canonical_clauses: set[tuple[int, ...]] = set()
    for clause in clauses:
        dedup = {lit for lit in clause if lit != 0}
        if not dedup:
            canonical_clause: tuple[int, ...] = tuple()
        else:
            normalised: List[int] = []
            for lit in dedup:
                sign = -1 if lit < 0 else 1
                normalised.append(sign * mapping[abs(lit)])
            canonical_clause = tuple(
                sorted(normalised, key=lambda lit: (abs(lit), lit > 0))
            )
        canonical_clauses.add(canonical_clause)

    ordered = sorted(canonical_clauses)
    lines = [f"p cnf {len(mapping)} {len(ordered)}"]
    for clause in ordered:
        if not clause:
            lines.append("0")
        else:
            body = " ".join(str(lit) for lit in clause)
            lines.append(f"{body} 0")
    canonical_text = "\n".join(lines) + "\n"
    return CanonicalCNF(clauses=ordered, num_vars=len(mapping), text=canonical_text)


__all__ = ["CanonicalCNF", "canonicalise_cnf", "parse_dimacs_cnf"]
