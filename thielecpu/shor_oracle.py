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

    print(f"  • Computing {max_period + 1} modular exponentiation residues...")
    import time
    start_time = time.time()
    
    # Try to import psutil for memory monitoring
    try:
        import psutil
        process = psutil.Process()
        initial_memory = process.memory_info().rss / 1024 / 1024  # MB
        memory_monitoring = True
    except ImportError:
        memory_monitoring = False
        print("  • Memory monitoring unavailable (install psutil for memory stats)")
    
    residues = {}
    for k in range(0, max_period + 1):
        residues[k] = pow(a, k, n)
        if k % 100000 == 0 and k > 0:  # Progress every 100k computations
            elapsed = time.time() - start_time
            rate = k / elapsed if elapsed > 0 else 0
            if memory_monitoring:
                current_memory = process.memory_info().rss / 1024 / 1024
                memory_used = current_memory - initial_memory
                print(f"    - Computed {k}/{max_period + 1} residues ({k/(max_period + 1)*100:.1f}%) - {rate:.0f} ops/sec - Memory: +{memory_used:.1f} MB")
            else:
                print(f"    - Computed {k}/{max_period + 1} residues ({k/(max_period + 1)*100:.1f}%) - {rate:.0f} ops/sec")
    elapsed = time.time() - start_time
    if memory_monitoring:
        final_memory = process.memory_info().rss / 1024 / 1024
        total_memory_used = final_memory - initial_memory
        print(f"  ✓ Residues computed in {elapsed:.2f}s ({len(residues)} total) - Peak memory usage: {total_memory_used:.1f} MB")
    else:
        print(f"  ✓ Residues computed in {elapsed:.2f}s ({len(residues)} total)")

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

    print(f"  • Setting up Z3 solver with {len(residues)} constraints...")
    solver = z3.Solver()
    r = z3.Int("r")
    pow_mod = z3.Function("pow_mod", z3.IntSort(), z3.IntSort())

    solver.add(r >= 1, r <= max_period)
    constraint_count = 0
    for exponent, residue in residues.items():
        solver.add(pow_mod(z3.IntVal(exponent)) == residue)
        constraint_count += 1
        if constraint_count % 100000 == 0:
            if memory_monitoring:
                current_memory = process.memory_info().rss / 1024 / 1024
                memory_used = current_memory - initial_memory
                print(f"    - Added {constraint_count}/{len(residues)} constraints - Memory: +{memory_used:.1f} MB")
            else:
                print(f"    - Added {constraint_count}/{len(residues)} constraints")
    solver.add(pow_mod(r) == 1)
    for exponent in range(1, max_period):
        if residues[exponent] == 1:
            solver.add(r <= exponent)
    print(f"  ✓ Z3 solver initialized with {constraint_count} constraints")

    claims: List[ClaimRecord] = []
    mu_total = 0.0
    solver_queries = 0

    def assess(statement: str, predicate: z3.BoolRef, **details: object) -> None:
        nonlocal mu_total, solver_queries

        print(f"    • Assessing claim: {statement}")
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
            print(f"      ✓ Proven (μ-cost: {mu_delta:.2f}, candidates: {len(candidates)})")
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
            print(f"      ✗ Refuted (μ-cost: {mu_delta:.2f}, candidates: {len(candidates)})")
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
            print(f"      ? Inconclusive (μ-cost: {mu_delta:.2f}, candidates: {len(candidates)})")

    print(f"  • Assessing geometric claims to constrain period...")
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

    print(f"  ✓ Claims assessment complete ({len(claims)} claims, μ-total: {mu_total:.2f}, queries: {solver_queries})")
    print("  • Extracting final period from solver model...")
    if solver.check() != z3.sat:
        raise RuntimeError("solver lost satisfiability while assessing claims")
    model = solver.model()
    final_period = int(model[r].as_long())
    print(f"  ✓ Final period extracted: r = {final_period}")

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
