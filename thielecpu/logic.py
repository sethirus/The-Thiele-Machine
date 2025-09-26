"""Z3-backed logic bridge producing deterministic certificates."""

from __future__ import annotations

from pathlib import Path
from z3 import Solver, parse_smt2_string, sat

try:
    from .certs import CertStore
    from .isa import CSR
    from .state import State
except ImportError:
    # Handle running as script
    import sys
    import os
    sys.path.insert(0, os.path.dirname(__file__))
    from certs import CertStore
    from isa import CSR
    from state import State


def lassert(state: State, module: int, formula: str, outdir: Path) -> str:
    """Solve ``formula`` for ``module`` and emit cert artifacts."""

    del module
    store = CertStore(outdir)
    cid = store.next_id()
    store.write_text(cid, "assert.smt2", formula)

    solver = Solver()
    solver.set(proof=True)
    solver.add(*parse_smt2_string(formula))
    result = solver.check()
    if result == sat:
        body = solver.model().sexpr().encode()
        store.write_bytes(cid, "witness", body)
        state.csr[CSR.STATUS] = 1
    else:
        # For unsat, use unsat core or simple note
        if solver.unsat_core():
            core_str = b" & ".join(str(decl).encode() for decl in solver.unsat_core())
            body = b"unsat: " + core_str
        else:
            body = b"unsat"
        store.write_bytes(cid, "proof", body)
        state.csr[CSR.STATUS] = 0
    digest = store.save_hash(cid, body)
    state.csr[CSR.CERT_ADDR] = str(store.hash_path(cid))
    return digest


def ljoin(state: State, cert1: str, cert2: str, outdir: Path) -> str:
    """Join two certificate hashes and write a combined certificate."""

    store = CertStore(outdir)
    cid = store.next_id()
    combined = (cert1 + cert2).encode()
    store.write_bytes(cid, "join", combined)
    digest = store.save_hash(cid, combined)
    state.csr[CSR.CERT_ADDR] = str(store.hash_path(cid))
    if cert1 != cert2:
        state.csr[CSR.ERR] = 1
    return digest


__all__ = ["lassert", "ljoin"]
