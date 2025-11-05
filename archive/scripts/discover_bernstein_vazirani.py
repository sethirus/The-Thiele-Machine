# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

#!/usr/bin/env python3
"""
Thiele Machine: Bernstein-Vazirani Problem Solver

This script demonstrates the Thiele Machine's ability to solve the Bernstein-Vazirani problem efficiently.
The oracle f(x) = s · x mod 2 for secret s in Z_2^n is modeled symbolically using Z3 BitVec.
Queries are made to basis vectors e_i, yielding f(e_i) = s_i, solving the linear system.
Phases: (1) Model system and query via linear algebra axioms, (2) Extract witness s,
(3) Verify correctness, (4) Report results.
Artifacts generated: bernstein_vazirani.smt2, witness.txt, proof.txt, receipt.json.
"""

import os
import time
import json
import hashlib

try:
    import z3
    from thielecpu.vm import VM
    from thielecpu.state import State
except ImportError as e:
    print(f"Import error: {e}")
    print("Ensure z3-solver and thielecpu are installed.")
    exit(1)

# --- Constants ---
N = 4  # bit length, small for demo
SECRET = 0b1010  # concrete secret for simulation, s = [0,1,0,1] for bits 0 to 3

# --- Oracle Function ---
def dot_mod2(a, b):
    """Compute dot product mod 2 for integers a, b."""
    return sum(((a >> i) & 1) * ((b >> i) & 1) for i in range(N)) % 2

def compute_f_symbolic(s, x):
    """Symbolic computation of f(x) = s · x mod 2 using Z3 BitVec."""
    f = z3.BitVecVal(0, 1)
    for i in range(N):
        s_i = z3.Extract(i, i, s)
        x_i = z3.Extract(i, i, x)
        f ^= s_i & x_i
    return f

# --- Phase 1: Model the system and query for s via linear algebra axioms ---
def phase1_model_system():
    vm = VM(State())
    vm.execute_python("self.state.log('PNEW: Phase 1 - Modeling Bernstein-Vazirani system')")
    s = z3.BitVec('s', N)
    solver = z3.Solver()
    # Query basis vectors e_i (x = 1 << i), get f(e_i) = s_i
    for i in range(N):
        x_val = 1 << i
        f_val = dot_mod2(SECRET, x_val)  # concrete oracle response
        x_bv = z3.BitVecVal(x_val, N)
        f_computed = compute_f_symbolic(s, x_bv)
        solver.add(f_computed == z3.BitVecVal(f_val, 1))
        vm.execute_python(f"self.state.log('LASSERT: Query e_{i}, f(e_{i}) = {f_val}')")
    vm.execute_python("self.state.log('LDEDUCE: Added linear constraints for basis queries')")
    if solver.check() == z3.sat:
        model = solver.model()
        s_found = model[s].as_long()
        vm.execute_python(f"self.state.log('LDEDUCE: SMT satisfiable, s extracted as {s_found:0{N}b}')")
        with open('results/bernstein_vazirani.smt2', 'w') as f:
            f.write(solver.to_smt2())
        return True, s_found
    else:
        vm.execute_python("self.state.log('LASSERT: SMT unsatisfiable (unexpected)')")
        return False, None

# --- Phase 2: Extract the witness s ---
def phase2_extract_witness(s_found):
    vm = VM(State())
    vm.execute_python("self.state.log('PNEW: Phase 2 - Extracting witness s')")
    vm.execute_python(f"self.state.log('LDEDUCE: Witness s = {s_found:0{N}b}')")
    with open('results/witness.txt', 'w') as f:
        f.write(f"Witness s: {s_found}\n")
        f.write(f"Binary: {s_found:0{N}b}\n")
    return s_found

# --- Phase 3: Verify correctness ---
def phase3_verify_correctness(s_found):
    vm = VM(State())
    vm.execute_python("self.state.log('PNEW: Phase 3 - Verifying correctness')")
    correct = True
    for x in range(1 << N):
        expected = dot_mod2(SECRET, x)
        actual = dot_mod2(s_found, x)
        if expected != actual:
            correct = False
            break
    if correct:
        vm.execute_python("self.state.log('LDEDUCE: Verification passed, s matches oracle')")
    else:
        vm.execute_python("self.state.log('LASSERT: Verification failed')")
    with open('results/proof.txt', 'w') as f:
        f.write("Proof of Correctness:\n")
        f.write(f"Secret s: {SECRET:0{N}b}\n")
        f.write(f"Extracted s: {s_found:0{N}b}\n")
        f.write("Verified by checking f(x) for all x in {0,1}^n.\n")
        f.write("Correctness: " + ("Yes" if correct else "No") + "\n")
    return correct

# --- Phase 4: Report results ---
def phase4_report_results(s_found, correct):
    vm = VM(State())
    vm.execute_python("self.state.log('PNEW: Phase 4 - Reporting results')")
    vm.execute_python(f"self.state.log('LDEDUCE: Results: s={s_found:0{N}b}, correct={correct}')")
    # Generate receipt
    artifacts = ['results/bernstein_vazirani.smt2', 'results/witness.txt', 'results/proof.txt']
    receipt = {
        "experiment": "Bernstein-Vazirani Problem Solver",
        "timestamp": time.time(),
        "parameters": {
            "n": N,
            "secret": SECRET
        },
        "results": {
            "s_found": s_found,
            "correct": correct
        },
        "artifacts": {}
    }
    for art in artifacts:
        if os.path.exists(art):
            with open(art, 'rb') as f:
                h = hashlib.sha256(f.read()).hexdigest()
            receipt["artifacts"][art] = h
    with open('results/receipt.json', 'w') as f:
        json.dump(receipt, f, indent=2)

# --- Main ---
def main():
    os.system('cls' if os.name == "nt" else "clear")
    print("=" * 80)
    print("  Thiele Machine: Bernstein-Vazirani Problem Solver")
    print("=" * 80)

    # Phase 1: Model system
    success, s_found = phase1_model_system()
    if not success:
        print("Phase 1: Modeling failed.")
        return
    print("Phase 1: System modeled, queries added.")

    # Phase 2: Extract witness
    s_found = phase2_extract_witness(s_found)
    print("Phase 2: Witness extracted.")

    # Phase 3: Verify
    correct = phase3_verify_correctness(s_found)
    if not correct:
        print("Phase 3: Verification failed.")
        return
    print("Phase 3: Correctness verified.")

    # Phase 4: Report
    phase4_report_results(s_found, correct)
    print("Phase 4: Results reported.")

    # Print artifacts
    all_artifacts = ['results/bernstein_vazirani.smt2', 'results/witness.txt', 'results/proof.txt', 'results/receipt.json']
    print("\n" + "="*80)
    print("ARTIFACT CONTENTS:")
    for art in all_artifacts:
        print(f"\n=== {os.path.basename(art)} ===")
        with open(art, 'r') as f:
            print(f.read())
    print("="*80)

    print("Artifacts generated: bernstein_vazirani.smt2, witness.txt, proof.txt, receipt.json")
    print("Receipt saved to results/receipt.json with SHA-256 hashes.")
    print("=" * 80)
    print("Analysis complete. Bernstein-Vazirani problem solved efficiently.")
    print("=" * 80)

if __name__ == "__main__":
    main()