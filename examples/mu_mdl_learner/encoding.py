"""Period-k claim as a SAT-mode LASSERT program.

Formula: for length N and period k, the 2*(N-k) CNF clauses encoding
x_i <-> x_{i+k}. Cert: the stream itself as the satisfying assignment.
Countermodel: bit 0 high, rest low (falsifies the first clause for any
k in [1, N-1]). LASSERT verifies model ^ ~countermodel.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import List, Tuple

from .streams import Stream


DEFAULT_LASSERT_DELTA: int = 0
MEM_SIZE: int = 128
_FBASE: int = 0x10
_CBASE: int = 0x50


@dataclass(frozen=True)
class PeriodAssertProgram:
    n: int
    k: int
    program: list           # dict-form list, ready for vm_run
    hw_flen: int
    nvars: int
    nclauses: int
    expected_mu_delta: int  # exact µ added by the LASSERT step


def _dimacs_underscore_formula(nvars: int, nclauses: int, clauses: List[List[int]]) -> str:
    parts = [f"p_cnf_{nvars}_{nclauses}"]
    for cl in clauses:
        parts.append("_".join(str(lit) for lit in cl + [0]))
    return "__".join(parts)


def _dimacs_assignment(bits_by_var: List[int], nvars: int) -> str:
    toks = ["v"]
    for v in range(1, nvars + 1):
        bit = int(bits_by_var[v - 1])
        toks.append(str(v if bit == 1 else -v))
    toks.append("0")
    return "_".join(toks)


def _period_k_clauses(n: int, k: int) -> List[List[int]]:
    if not (1 <= k < n):
        raise ValueError(f"need 1 <= k < n; got n={n}, k={k}")
    clauses: List[List[int]] = []
    for i in range(n - k):
        v_i = i + 1
        v_j = i + k + 1
        clauses.append([-v_i, v_j])
        clauses.append([v_i, -v_j])
    return clauses


def _countermodel_bits(n: int) -> List[int]:
    out = [0] * n
    out[0] = 1
    return out


def build_period_k_program(
    stream: Stream,
    k: int,
    declared_delta: int = DEFAULT_LASSERT_DELTA,
) -> PeriodAssertProgram:
    """Dict-form VM program asserting `stream is period-k`."""
    n = len(stream)
    clauses = _period_k_clauses(n, k)
    nvars = n
    nclauses = len(clauses)
    hw_flen = 3 * nclauses

    formula_end = _FBASE + 3 + hw_flen
    cert_end = _CBASE + 2 * nvars + 1
    if formula_end > _CBASE:
        raise ValueError(
            f"formula overflows cert region: formula ends at {formula_end}, "
            f"cert starts at {_CBASE} (n={n}, k={k}, hw_flen={hw_flen}). "
            "Reduce n."
        )
    if cert_end > MEM_SIZE:
        raise ValueError(
            f"cert overflows MEM_SIZE: cert ends at {cert_end}, "
            f"MEM_SIZE={MEM_SIZE} (n={n}, nvars={nvars})"
        )

    formula = _dimacs_underscore_formula(nvars, nclauses, clauses)
    model = _dimacs_assignment([int(b) for b in stream], nvars)
    counter = _dimacs_assignment(_countermodel_bits(n), nvars)

    program = [
        {
            "op": "lassert",
            "module": 0,
            "formula": formula,
            "cert_type": "sat",
            "cert": model,
            "countermodel": counter,
            "cost": declared_delta,
        },
        {"op": "halt", "cost": 0},
    ]

    expected_mu_delta = hw_flen * 8 + (declared_delta + 1)

    return PeriodAssertProgram(
        n=n,
        k=k,
        program=program,
        hw_flen=hw_flen,
        nvars=nvars,
        nclauses=nclauses,
        expected_mu_delta=expected_mu_delta,
    )


def run_period_claim(
    stream: Stream,
    k: int,
    declared_delta: int = DEFAULT_LASSERT_DELTA,
) -> Tuple[bool, int, "object", PeriodAssertProgram]:
    """Run the period-k claim and return (verified, mu_paid, final_state, prog)."""
    from thielecpu.vm import VMState, vm_run

    prog = build_period_k_program(stream, k, declared_delta=declared_delta)
    s0 = VMState.default()
    sf = vm_run(s0, prog.program, max_steps=200)
    verified = (not sf.vm_err)
    return verified, sf.vm_mu, sf, prog
