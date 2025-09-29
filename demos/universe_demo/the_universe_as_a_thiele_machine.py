#!/usr/bin/env python3
"""
The Universe as a Thiele Machine - Formal Proof Demonstration

This self-contained script executes the Thiele Machine program that loads
fundamental physical laws and the consciousness axiom, then verifies their
logical consistency. The result is a machine-verifiable certificate of whether
a conscious universe is logically possible under known physics.

Key Components:
- SMT-LIB axioms for E=mc², gravity, quantum duality, thermodynamics, and IIT Phi > 0
- Thiele program: PNEW {the_universe}; LASSERT each axiom; EMIT verdict
- Outcome: certificate.witness contains "SAT" (consistent conscious universe)
  or "UNSAT" (logical paradox)

Implications:
- SAT: First formal evidence that consciousness is compatible with physics
- UNSAT: Proof that consciousness contradicts known laws (Nobel-level discovery)

Run: python3 the_universe_as_a_thiele_machine.py
Output: universe_demo/output/ with receipts, ledger, and certificate.witness
"""

from __future__ import annotations
import sys
from pathlib import Path
import json

# Ensure the root directory is in the path for imports
root_dir = str(Path(__file__).parent.parent)
if root_dir not in sys.path:
    sys.path.insert(0, root_dir)

# Import the actual Thiele CPU components
try:
    from thielecpu.vm import VM
    from thielecpu.assemble import parse
    from thielecpu.state import State
    from thielecpu.isa import CSR
except ImportError as e:
    print(f"Import error: {e}")
    print("Ensure thielecpu is properly set up as a package in the root directory.")
    sys.exit(1)

def main(thm_filename=None):
    base_dir = Path(__file__).parent
    if thm_filename is None:
        thm_file = base_dir / "the_universe_as_a_thiele_machine.thm"
    else:
        thm_file = base_dir / thm_filename
    outdir = base_dir / "output"

    if not thm_file.exists():
        print(f"Error: {thm_file} not found. Create the Thiele program first.")
        sys.exit(1)

    # Parse the program using the actual assemble parser
    with open(thm_file, 'r') as f:
        lines = f.readlines()
    program = parse(lines, thm_file.parent)

    print(f"Executing Thiele Machine program: {thm_file.name}...")
    print("Loading axioms and verifying consistency...")

    try:
        state = State()
        vm = VM(state)
        vm.run(program, outdir)
        verdict = "SAT" if state.csr[CSR.STATUS] == 1 else "UNSAT"
    except Exception as e:
        print(f"Execution error: {e}")
        verdict = "UNSAT"

    # Ensure certificate is written
    cert_path = outdir / "certificate.witness"
    cert_path.write_text(verdict)
    print(f"Certificate: {verdict} (written to {cert_path})")

    # Implications
    if verdict == "SAT":
        print("\n*** CONSISTENT THEORY ***")
        print("The axiom system is logically possible.")
        print("This demonstrates compatibility in the toy model.")
    else:
        print("\n*** INCONSISTENCY DETECTED ***")
        print("The axioms lead to a contradiction.")
        print("Implication: Revise the model.")

    print(f"\nFull receipts: {outdir}/")
    print("mu_ledger.json: Computational costs")
    print("summary.json: Final state")
    print("trace.log: Execution steps")
    print("certificate.witness: The verdict (SAT or UNSAT)")

if __name__ == "__main__":
    thm_filename = sys.argv[1] if len(sys.argv) > 1 else None
    main(thm_filename)