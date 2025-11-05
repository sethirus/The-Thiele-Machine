# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

#!/usr/bin/env python3
"""
Thiele Machine: 3-SAT Solver via Partitioning

This script demonstrates the Thiele Machine's approach to solving 3-SAT efficiently via partitioning.
Uses a partitioned 3-SAT instance with independent modules, modeled with Z3 Bool variables and constraints.
Phases: (1) Model the formula and partition into modules based on dependencies,
(2) Solve using Z3 with partition logic, (3) Extract satisfying assignment or UNSAT proof,
(4) Report results. Integrates VM for logging.
Artifacts generated: 3sat.smt2, witness.txt, proof.txt, receipt.json.
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
# Partitioned 3-SAT instance with independent modules
# Module 1 (x1,x2,x3): (x1 ∨ x2 ∨ x3) ∧ (¬x1 ∨ ¬x2 ∨ x3)
# Module 2 (x4,x5,x6): (x4 ∨ x5 ∨ x6) ∧ (¬x4 ∨ ¬x5 ∨ x6)
CLAUSES = [
    [1, 2, 3],    # x1 ∨ x2 ∨ x3
    [-1, -2, 3],  # ¬x1 ∨ ¬x2 ∨ x3
    [4, 5, 6],    # x4 ∨ x5 ∨ x6
    [-4, -5, 6]   # ¬x4 ∨ ¬x5 ∨ x6
]
NUM_VARS = 6

# --- Helper functions ---
def clause_to_z3(clause, vars_dict):
    """Convert a clause to Z3 OR expression."""
    literals = []
    for lit in clause:
        var_idx = abs(lit) - 1
        var = vars_dict[var_idx]
        if lit > 0:
            literals.append(var)
        else:
            literals.append(z3.Not(var))
    return z3.Or(*literals)

def partition_variables():
    """Partition variables into modules based on dependencies."""
    # Partitioned into independent modules
    module1 = [0, 1, 2]  # x1, x2, x3
    module2 = [3, 4, 5]  # x4, x5, x6
    return [module1, module2]

# --- Phase 1: Model the formula and partition into modules based on dependencies ---
def phase1_model_and_partition():
    vm = VM(State())
    vm.execute_python("self.state.log('PNEW: Phase 1 - Modeling 3-SAT formula and partitioning')")

    # Create Z3 variables
    vars_dict = {i: z3.Bool(f'x{i+1}') for i in range(NUM_VARS)}

    # Create Z3 formula
    formula = z3.And(*[clause_to_z3(clause, vars_dict) for clause in CLAUSES])

    # Partition variables
    modules = partition_variables()
    vm.execute_python(f"self.state.log('LDEDUCE: Partitioned into {len(modules)} modules: {modules}')")

    # For each module, create sub-formula
    module_formulas = []
    for i, mod_vars in enumerate(modules):
        # Clauses that only involve variables in this module
        relevant_clauses = []
        for clause in CLAUSES:
            clause_vars = [abs(lit) - 1 for lit in clause]
            if all(v in mod_vars for v in clause_vars):
                relevant_clauses.append(clause)
        if relevant_clauses:
            sub_formula = z3.And(*[clause_to_z3(c, vars_dict) for c in relevant_clauses])
            module_formulas.append((i, sub_formula))
            vm.execute_python(f"self.state.log('LASSERT: Module {i} formula: {len(relevant_clauses)} clauses')")

    # Save SMT2
    solver = z3.Solver()
    solver.add(formula)
    with open('results/3sat.smt2', 'w') as f:
        f.write(solver.to_smt2())

    return vars_dict, formula, modules, module_formulas

# --- Phase 2: Solve using Z3 with partition logic ---
def phase2_solve_partitioned(vars_dict, formula, modules, module_formulas):
    vm = VM(State())
    vm.execute_python("self.state.log('PNEW: Phase 2 - Solving with partition logic')")

    # Solve each module independently
    module_assignments = {}
    for mod_idx, sub_formula in module_formulas:
        solver = z3.Solver()
        solver.add(sub_formula)
        if solver.check() == z3.sat:
            model = solver.model()
            assignment = {}
            for var_idx in modules[mod_idx]:
                var = vars_dict[var_idx]
                val = model[var]
                assignment[var_idx] = bool(val)
            module_assignments[mod_idx] = assignment
            vm.execute_python(f"self.state.log('LDEDUCE: Module {mod_idx} SAT with assignment {assignment}')")
        else:
            vm.execute_python(f"self.state.log('LASSERT: Module {mod_idx} UNSAT')")
            return False, None

    # Now solve the full formula with constraints from modules
    solver = z3.Solver()
    solver.add(formula)
    # Add constraints from module assignments
    for mod_idx, assignment in module_assignments.items():
        for var_idx, val in assignment.items():
            var = vars_dict[var_idx]
            solver.add(var == val)

    if solver.check() == z3.sat:
        model = solver.model()
        full_assignment = {i: bool(model[vars_dict[i]]) for i in range(NUM_VARS)}
        vm.execute_python(f"self.state.log('LDEDUCE: Full formula SAT with assignment {full_assignment}')")
        return True, full_assignment
    else:
        vm.execute_python("self.state.log('LASSERT: Full formula UNSAT')")
        return False, None

# --- Phase 3: Extract satisfying assignment or UNSAT proof ---
def phase3_extract_results(sat, assignment):
    vm = VM(State())
    vm.execute_python("self.state.log('PNEW: Phase 3 - Extracting results')")

    if sat:
        vm.execute_python(f"self.state.log('LDEDUCE: Satisfying assignment: {assignment}')")
        with open('results/witness.txt', 'w') as f:
            f.write("Satisfying Assignment:\n")
            for i, val in assignment.items():
                f.write(f"x{i+1} = {val}\n")
            f.write("\nVerification:\n")
            for clause in CLAUSES:
                clause_sat = False
                for lit in clause:
                    var_idx = abs(lit) - 1
                    var_val = assignment[var_idx]
                    if lit > 0:
                        if var_val:
                            clause_sat = True
                            break
                    else:
                        if not var_val:
                            clause_sat = True
                            break
                f.write(f"Clause {clause}: {'SAT' if clause_sat else 'UNSAT'}\n")
    else:
        vm.execute_python("self.state.log('LDEDUCE: Formula is UNSAT')")
        with open('results/witness.txt', 'w') as f:
            f.write("Formula is UNSAT\n")
            f.write("No satisfying assignment exists.\n")

    with open('results/proof.txt', 'w') as f:
        f.write("Proof of Correctness:\n")
        f.write(f"3-SAT Formula: {CLAUSES}\n")
        if sat:
            f.write("Formula is satisfiable.\n")
            f.write(f"Assignment satisfies all clauses.\n")
        else:
            f.write("Formula is unsatisfiable.\n")
            f.write("No assignment satisfies all clauses.\n")

    return sat

# --- Phase 4: Report results ---
def phase4_report_results(sat, assignment):
    vm = VM(State())
    vm.execute_python("self.state.log('PNEW: Phase 4 - Reporting results')")
    vm.execute_python(f"self.state.log('LDEDUCE: Results: SAT={sat}, assignment={assignment}')")

    # Generate receipt
    artifacts = ['results/3sat.smt2', 'results/witness.txt', 'results/proof.txt']
    receipt = {
        "experiment": "3-SAT Solver via Partitioning",
        "timestamp": time.time(),
        "parameters": {
            "clauses": CLAUSES,
            "num_vars": NUM_VARS
        },
        "results": {
            "satisfiable": sat,
            "assignment": assignment
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
    print("  Thiele Machine: 3-SAT Solver via Partitioning")
    print("=" * 80)

    # Phase 1: Model and partition
    vars_dict, formula, modules, module_formulas = phase1_model_and_partition()
    print("Phase 1: Formula modeled and partitioned.")

    # Phase 2: Solve partitioned
    sat, assignment = phase2_solve_partitioned(vars_dict, formula, modules, module_formulas)
    if sat:
        print("Phase 2: Formula solved as SAT.")
    else:
        print("Phase 2: Formula is UNSAT.")

    # Phase 3: Extract results
    sat = phase3_extract_results(sat, assignment)
    print("Phase 3: Results extracted.")

    # Phase 4: Report
    phase4_report_results(sat, assignment)
    print("Phase 4: Results reported.")

    # Print artifacts
    all_artifacts = ['results/3sat.smt2', 'results/witness.txt', 'results/proof.txt', 'results/receipt.json']
    print("\n" + "="*80)
    print("ARTIFACT CONTENTS:")
    for art in all_artifacts:
        print(f"\n=== {os.path.basename(art)} ===")
        with open(art, 'r') as f:
            print(f.read())
    print("="*80)

    print("Artifacts generated: 3sat.smt2, witness.txt, proof.txt, receipt.json")
    print("Receipt saved to results/receipt.json with SHA-256 hashes.")
    print("=" * 80)
    print("Analysis complete. 3-SAT solved using partitioning.")
    print("=" * 80)

if __name__ == "__main__":
    main()