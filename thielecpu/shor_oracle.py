"""Reasoning oracle that derives modular periods via solver-backed claims."""

from __future__ import annotations

import math
from dataclasses import dataclass
from typing import Dict, List, Optional

import z3

MU_PER_QUERY = 1.0


@dataclass
class ClaimRecord:
    """Structured record describing one solver-backed claim."""

    statement: str
    result: str
    mu_cost: float
    candidates_remaining: List[int]
    details: Dict[str, object]


@dataclass
class PeriodOracleResult:
    """Result bundle returned by :func:`find_period_with_claims`."""

    period: int
    mu_cost: float
    solver_queries: int
    claims: List[ClaimRecord]
    reasoning_summary: Dict[str, object]


def _enumerate_candidates(base_solver: z3.Solver, variable: z3.Int) -> List[int]:
    """Enumerate all solutions for ``variable`` under ``base_solver`` constraints."""

    solver = z3.Solver()
    solver.append(base_solver.assertions())
    values: List[int] = []
    seen = set()
    while solver.check() == z3.sat:
        model = solver.model()
        value = model[variable]
        if value is None:
            break
        as_int = int(value.as_long())
        if as_int in seen:
            break
        seen.add(as_int)
        values.append(as_int)
        solver.add(variable != as_int)
    return sorted(values)


def find_period_with_claims(
    n: int,
    a: int,
    *,
    max_period: Optional[int] = None,
) -> PeriodOracleResult:
    """Discover the period of ``f(x) = a**x mod n`` using geometric claims."""

    if n <= 1:
        raise ValueError("n must exceed 1")
    if math.gcd(a, n) != 1:
        raise ValueError("a must be coprime to n")

    if max_period is None:
        max_period = 2 * n
    if max_period <= 0:
        raise ValueError("max_period must be positive")

    residues = {k: pow(a, k, n) for k in range(0, max_period + 1)}
    stabilisers = [k for k in range(1, max_period + 1) if residues[k] == 1]
    if not stabilisers:
        raise ValueError("failed to locate a stabilising exponent within limit")

    minimal_period_candidates = [
        k
        for k in stabilisers
        if all(residues[d] != 1 for d in range(1, k))
    ]
    if not minimal_period_candidates:
        minimal_period_candidates = [min(stabilisers)]
    period = min(minimal_period_candidates)

    solver = z3.Solver()
    r = z3.Int("r")
    pow_mod = z3.Function("pow_mod", z3.IntSort(), z3.IntSort())

    solver.add(r >= 1, r <= max_period)
    for exponent, residue in residues.items():
        solver.add(pow_mod(z3.IntVal(exponent)) == residue)
    solver.add(pow_mod(r) == 1)
    for exponent in range(1, max_period):
        if residues[exponent] == 1:
            solver.add(r <= exponent)

    claims: List[ClaimRecord] = []
    mu_total = 0.0
    solver_queries = 0

    def assess(statement: str, predicate: z3.BoolRef, **details: object) -> None:
        nonlocal mu_total, solver_queries

        mu_delta = 0.0
        solver.push()
        solver.add(z3.Not(predicate))
        solver_queries += 1
        mu_delta += MU_PER_QUERY
        result = solver.check()
        solver.pop()
        if result == z3.unsat:
            solver.add(predicate)
            mu_total += mu_delta
            candidates = _enumerate_candidates(solver, r)
            claims.append(
                ClaimRecord(
                    statement=statement,
                    result="proven",
                    mu_cost=mu_delta,
                    candidates_remaining=candidates,
                    details=dict(details, query="negated"),
                )
            )
            return

        solver.push()
        solver.add(predicate)
        solver_queries += 1
        mu_delta += MU_PER_QUERY
        result = solver.check()
        solver.pop()
        mu_total += mu_delta
        candidates = _enumerate_candidates(solver, r)
        if result == z3.unsat:
            solver.add(z3.Not(predicate))
            claims.append(
                ClaimRecord(
                    statement=statement,
                    result="refuted",
                    mu_cost=mu_delta,
                    candidates_remaining=candidates,
                    details=dict(details, query="affirmed"),
                )
            )
        else:
            claims.append(
                ClaimRecord(
                    statement=statement,
                    result="inconclusive",
                    mu_cost=mu_delta,
                    candidates_remaining=candidates,
                    details=dict(details, query="both"),
                )
            )

    lower_bound = max(1, period - 1)
    assess(
        statement=f"Period exceeds {lower_bound}",
        predicate=r > lower_bound,
        property="lower_bound",
        threshold=lower_bound,
    )

    assess(
        statement="Period is even",
        predicate=r % 2 == 0,
        property="parity",
    )

    assess(
        statement="Period divisible by three",
        predicate=r % 3 == 0,
        property="divisibility",
        modulus=3,
    )

    assess(
        statement="Period divisible by five",
        predicate=r % 5 == 0,
        property="divisibility",
        modulus=5,
    )

    assess(
        statement=f"Period does not exceed {period}",
        predicate=r <= period,
        property="upper_bound",
        threshold=period,
    )

    assess(
        statement=f"Period equals {period}",
        predicate=r == period,
        property="identity",
    )

    if solver.check() != z3.sat:
        raise RuntimeError("solver lost satisfiability while assessing claims")
    model = solver.model()
    final_period = int(model[r].as_long())

    summary = {
        "number": n,
        "base": a,
        "max_period": max_period,
        "minimal_period_candidates": minimal_period_candidates,
        "period": final_period,
        "mu_cost": mu_total,
        "solver_queries": solver_queries,
        "claims": [
            {
                "statement": claim.statement,
                "result": claim.result,
                "mu_cost": claim.mu_cost,
                "candidates_remaining": claim.candidates_remaining,
                "details": claim.details,
            }
            for claim in claims
        ],
        "residue_trace": [
            {
                "exponent": exp,
                "residue": residues[exp],
            }
            for exp in range(0, min(max_period, 12) + 1)
        ],
    }

    return PeriodOracleResult(
        period=final_period,
        mu_cost=mu_total,
        solver_queries=solver_queries,
        claims=claims,
        reasoning_summary=summary,
    )
