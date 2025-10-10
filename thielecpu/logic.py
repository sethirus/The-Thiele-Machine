# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

"""Z3-backed logic bridge producing deterministic certificates."""

from __future__ import annotations

from pathlib import Path
from z3 import Solver, parse_smt2_string, sat
import os

try:
    from .certs import CertStore
    from .isa import CSR
    from .state import State
    from ._types import ModuleId
except ImportError:
    # Handle running as script
    import sys
    import os
    sys.path.insert(0, os.path.dirname(__file__))
    from certs import CertStore
    from isa import CSR
    from state import State
    from _types import ModuleId


def lassert(state: State, module: int, formula: str, outdir: Path) -> str:
    """Add ``formula`` as axiom to ``module`` and check satisfiability of all module axioms."""

    module_id = ModuleId(module)

    # Add the formula as an axiom to the module
    state.add_axiom(module_id, formula)

    # Get all axioms for this module
    module_axioms = state.get_module_axioms(module_id)

    # Check if certificate generation is enabled (default: disabled)
    certs_enabled = os.environ.get('THIELE_CERTS', '').lower() in ('1', 'true', 'yes')
    no_certs = not certs_enabled

    if not no_certs:
        store = CertStore(outdir)
        cid = store.next_id()
        store.write_text(cid, "assert.smt2", formula)

    # Check satisfiability of all axioms in the module
    combined_formula = "\n".join(module_axioms)

    print(f"LASSERT: Checking satisfiability for module {module_id}...")
    print(f"LASSERT: Formula has {len(combined_formula.split())} tokens")

    solver = Solver()
    # solver.set(proof=True)  # Disabled to avoid hang on unsat proof generation
    solver.add(*parse_smt2_string(combined_formula))

    print("LASSERT: Running Z3 satisfiability check...")
    import time
    start_time = time.time()
    print(f"LASSERT: Check started at {start_time:.2f}")

    # Show progress indicator during potentially long-running check
    import time
    import threading

    def show_progress():
        dots = 0
        while not progress_done.is_set():
            dots = (dots + 1) % 4
            print(f"LASSERT: Checking...{'.' * dots}", end='\r', flush=True)
            time.sleep(1)

    progress_done = threading.Event()
    progress_thread = threading.Thread(target=show_progress, daemon=True)
    progress_thread.start()

    try:
        result = solver.check()
    finally:
        progress_done.set()
        end_time = time.time()
        elapsed = end_time - start_time
        print(f"LASSERT: Check complete in {elapsed:.2f}s" + " " * 20)  # Clear the progress line

    if result == sat:
        print("LASSERT: Formula is satisfiable")
        body = solver.model().sexpr().encode()
        if not no_certs:
            store.write_bytes(cid, "witness", body)
        state.csr[CSR.STATUS] = 1
    else:
        print("LASSERT: Formula is unsatisfiable")
        # For unsat, use unsat core or simple note
        if solver.unsat_core():
            core_str = b" & ".join(str(decl).encode() for decl in solver.unsat_core())
            body = b"unsat: " + core_str
        else:
            body = b"unsat"
        if not no_certs:
            store.write_bytes(cid, "proof", body)
        state.csr[CSR.STATUS] = 0

    if no_certs:
        # Generate a dummy digest when certs are disabled
        import hashlib
        digest = hashlib.sha256(body).hexdigest()
        state.csr[CSR.CERT_ADDR] = f"nocert_{digest[:16]}"
    else:
        digest = store.save_hash(cid, body)
        state.csr[CSR.CERT_ADDR] = str(store.hash_path(cid))
    return digest


def ljoin(state: State, cert1: str, cert2: str, outdir: Path) -> str:
    """Join two certificate hashes and write a combined certificate."""

    # Check if certificate generation is enabled (default: disabled)
    certs_enabled = os.environ.get('THIELE_CERTS', '').lower() in ('1', 'true', 'yes')
    no_certs = not certs_enabled

    combined = (cert1 + cert2).encode()

    if no_certs:
        # Generate dummy digest when certs are disabled
        import hashlib
        digest = hashlib.sha256(combined).hexdigest()
        state.csr[CSR.CERT_ADDR] = f"nocert_join_{digest[:16]}"
    else:
        store = CertStore(outdir)
        cid = store.next_id()
        store.write_bytes(cid, "join", combined)
        digest = store.save_hash(cid, combined)
        state.csr[CSR.CERT_ADDR] = str(store.hash_path(cid))

    if cert1 != cert2:
        state.csr[CSR.ERR] = 1
    return digest


__all__ = ["lassert", "ljoin"]
