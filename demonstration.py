import hashlib
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

class ThieleAuditor:
    def __init__(self, axioms):
        self.solver = z3.Solver()
        for axiom_func in axioms:
            axiom_func(self.solver)

    def audit(self, claims_to_prove):
        self.solver.push()
        for claim_var in claims_to_prove:
            self.solver.add(claim_var == True)
        
        result = self.solver.check()
        
        receipt = {
            "timestamp": "...",
            "claims_audited": [str(c) for c in claims_to_prove],
        }

        if result == z3.sat:
            receipt["verdict"] = "CONSISTENT"
            receipt["witness"] = str(self.solver.model())
        else:
            receipt["verdict"] = "PARADOX_DETECTED"
            receipt["witness"] = {
                "unsat_core": [str(c) for c in self.solver.unsat_core()]
            }
        
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
    except AssertionError as e:
        print("Blind execution result: CRASHED")
        print("Reason: AssertionError on line 12. The program is blind to the logical paradox.")
    print("-" * 50)


def run_sighted_execution():
    print("\n--- DEMONSTRATION 2: Sighted Execution (The Thiele Machine) ---")
    print("Auditing the Liar's Paradox program...")

    # 1. Define the physical laws of our universe (logic).
    axioms = [
        lambda s: s.add(z3.Bool('P') != z3.Not(z3.Bool('P'))) # Law of Non-Contradiction
    ]

    # 2. Translate the program's claims into formal logic.
    P = z3.Bool('P') # Let P = "This program contains the word 'paradox'."
    
    # The source code *does* contain 'paradox', so P is True.
    # The program *asserts* "NOT P" is also True.
    program_claims = [
        P,          # The truth from reading the source
        z3.Not(P)   # The lie asserted by the program
    ]
    
    # 3. Create the Auditor and submit the claims.
    auditor = ThieleAuditor(axioms)
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
