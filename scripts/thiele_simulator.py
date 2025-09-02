"""On-the-fly SAT solving dialogue with a ``CnfProvider``.

This is a very small simulator demonstrating how a solver can explore a
CNF instance without ever materialising the entire clause database.  The
solver begins from the output bits of the multiplier and recursively
requests clauses for any variables it encounters, mirroring the
partition-aware "sighted" behaviour described in the user instructions.

The implementation uses ``python-sat``'s Minisat22 backend for the
actual solving, but the key idea is the incremental clause discovery.
"""

from __future__ import annotations

from typing import Dict, List, Set

try:
    from pysat.solvers import Minisat22
    PYSAT_AVAILABLE = True
except ImportError as e:
    print(f"Warning: PySAT not available: {e}")
    print("The Thiele Simulator will not function without PySAT.")
    print("Please install PySAT with: pip install python-sat")
    PYSAT_AVAILABLE = False
    Minisat22 = None

from .multiplier_cnf_provider import CnfProvider


class ThieleSimulator:
    """Incrementally explore clauses provided by ``CnfProvider``."""

    def __init__(self, provider: CnfProvider):
        if not PYSAT_AVAILABLE:
            raise ImportError("PySAT is required for ThieleSimulator but is not available. "
                            "Please install with: pip install python-sat")
        self.provider = provider
        self.solver = Minisat22()
        self._seen_clauses: Set[tuple] = set()
        self._var_processed: Dict[int, int] = {}

    def _add_var(self, var: int) -> None:
        stack: List[int] = [var]
        while stack:
            v = stack.pop()
            clauses = self.provider.clauses_for_var(v)
            start = self._var_processed.get(v, 0)
            if start >= len(clauses):
                continue
            for clause in clauses[start:]:
                key = tuple(sorted(clause, key=abs))
                if key in self._seen_clauses:
                    continue
                self._seen_clauses.add(key)
                self.solver.add_clause(clause)

                for lit in clause:
                    stack.append(abs(lit))
            self._var_processed[v] = len(clauses)

    # ------------------------------------------------------------------
    def solve(self, assumptions: List[int] | None = None):
        for i in range(self.provider.output_count()):
            v = self.provider.output_var(i)
            self._add_var(v)

        if not self.solver.solve(assumptions=assumptions or []):
            return None
        model = self.solver.get_model()
        p = CnfProvider.decode_bits(self.provider.p_bits, model)
        q = CnfProvider.decode_bits(self.provider.q_bits, model)
        return p, q


__all__ = ["ThieleSimulator"]

