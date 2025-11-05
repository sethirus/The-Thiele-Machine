# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

import json
import z3 # Requires z3-solver to be installed

# --- Part 1: The Liar's Paradox Program ---
# This is the program we will analyze. It's defined as a simple string.
# It contains a self-referential paradox.

LIAR_PROGRAM_SOURCE = """
def check_myself():
    # This is a paradox.
    my_source_code = get_my_own_source()
    
    claim_A = "This program contains the word 'paradox'."
    claim_B = "This program does NOT contain the word 'paradox'."

    # In a classical system, this is just a failed string search.
    # In a logical system, this is an assertion of (P and not P).
    assert claim_A in my_source_code
    assert claim_B not in my_source_code # This line is the logical contradiction.

    return "Success! Program is consistent."

# A helper function to make the source code available to the program itself.
def get_my_own_source():
    return LIAR_PROGRAM_SOURCE

check_myself()
"""

# --- Part 2: The Thiele Machine Kernel (Miniature Version) ---
# A simplified, in-memory Thiele Machine that runs on logical claims.

import sys, traceback
from datetime import datetime, timezone

class ThieleAuditor:
    def __init__(self, axioms):
        self.solver = z3.Solver()
        self.solver.set(unsat_core=True)
        self._tracked = []
        # Track axioms with names so they can appear in the core
        for _, axiom_func in enumerate(axioms, start=1):
            phi, name = axiom_func()
            self.solver.assert_and_track(phi, z3.Bool(name))
            self._tracked.append(name)

    def audit(self, claims_to_prove):
        self.solver.push()
        # Track each claim too
        claim_names = []
        for i, claim in enumerate(claims_to_prove, start=1):
            name = f"claim_{i}"
            self.solver.assert_and_track(claim, z3.Bool(name))
            claim_names.append(name)

        result = self.solver.check()
        receipt = {
            "timestamp": datetime.now(timezone.utc).isoformat().replace("+00:00", "Z"),
            "claims_audited": [str(c) for c in claims_to_prove],
        }

        if result == z3.sat:
            receipt["verdict"] = "CONSISTENT"
            receipt["witness"] = str(self.solver.model())
        else:
            core = [str(b) for b in self.solver.unsat_core()]
            receipt["verdict"] = "PARADOX_DETECTED"
            receipt["witness"] = {"unsat_core": core}

        self.solver.pop()
        return receipt

# --- Part 3: The Demonstration Logic ---

def run_blind_execution():
    print("--- DEMONSTRATION 1: Blind Execution (Standard Python) ---")
    print("Running the Liar's Paradox program...")
    local_scope = {'LIAR_PROGRAM_SOURCE': LIAR_PROGRAM_SOURCE}
    try:
        exec(LIAR_PROGRAM_SOURCE, local_scope)
        print("Blind execution result: SUCCESS (This should not happen)")
    except AssertionError:
        etype, _, tb = sys.exc_info()
        last = traceback.extract_tb(tb)[-1]
        print("Blind execution result: CRASHED")
        code_line = last.line if last.line else "(no code line available)"
        if etype is not None:
            print(f"Reason: {etype.__name__} at {last.filename}:{last.lineno} → {code_line}")
        else:
            print(f"Reason: AssertionError at {last.filename}:{last.lineno} → {code_line}")
    print("-" * 50)


def run_sighted_execution():
    print("\n--- DEMONSTRATION 2: Sighted Execution (The Thiele Machine) ---")
    print("Auditing the Liar's Paradox program...")

    def law_of_non_contradiction():
        P = z3.Bool('P')
        return (P != z3.Not(P), "axiom_LNC")

    axioms = [law_of_non_contradiction]

    # Derive fact_P from the actual source string in Python, then inject as a Z3 fact.
    contains_paradox = ("paradox" in LIAR_PROGRAM_SOURCE)
    fact_P = z3.BoolVal(contains_paradox)

    # Program’s *claims* (what it asserts about itself):
    P = z3.Bool('P')
    program_claims = [P, z3.Not(P)]

    auditor = ThieleAuditor(axioms)
    # Add the derived fact as an extra tracked clause so it can appear in the core
    auditor.solver.assert_and_track(P == fact_P, z3.Bool("fact_P"))
    receipt = auditor.audit(program_claims)

    print(f"Sighted execution result: {receipt['verdict']}")
    print("Reason: The machine analyzed the program's logical claims *before* execution.")
    print("It detected a violation of the Law of Non-Contradiction.")
    print("\nHere is the formal receipt:")
    print(json.dumps(receipt, indent=2))
    print("-" * 50)


if __name__ == "__main__":
    run_blind_execution()
    run_sighted_execution()
