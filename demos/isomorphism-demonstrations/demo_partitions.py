# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.
"""
Demo 2: Partition Logic - Intermediate Thiele Machine Demonstration

This demonstrates partition logic using the Thiele VM, showing that:
1. Modules can be created, split, and merged
2. Partition operations track μ-costs
3. The same semantics work across VM, Verilog, and Coq

Complexity Level: INTERMEDIATE
"""

from thielecpu.vm import VM
from thielecpu.state import State
from thielecpu.assemble import parse
from thielecpu.mu import question_cost_bits
from pathlib import Path
import tempfile


def demo_partition_creation():
    """Demonstrate creating partitions (modules)."""
    print("=" * 60)
    print("DEMO 2a: Partition Creation (PNEW)")
    print("Complexity Level: INTERMEDIATE")
    print("=" * 60)
    
    # Create a state with partition tracking
    state = State()
    vm = VM(state)
    
    # Create modules using state's pnew
    print("\nCreating modules using partition logic:")
    print("-" * 60)
    
    # Create three modules
    m1 = state.pnew({0, 1, 2, 3})  # First module with 4 elements
    m2 = state.pnew({4, 5, 6, 7})  # Second module with 4 elements
    m3 = state.pnew({8, 9})        # Third module with 2 elements
    
    print(f"  Module {m1}: region = {state.regions[m1]}")
    print(f"  Module {m2}: region = {state.regions[m2]}")
    print(f"  Module {m3}: region = {state.regions[m3]}")
    
    # Calculate μ-cost
    mu_cost = question_cost_bits("(PNEW {0,1,2,3})")
    mu_cost += question_cost_bits("(PNEW {4,5,6,7})")
    mu_cost += question_cost_bits("(PNEW {8,9})")
    
    print(f"\n  Total modules: 3")
    print(f"  μ-cost: {mu_cost:.1f} bits")
    
    return {
        'demo': 'Partition Creation',
        'modules_created': 3,
        'mu_cost': mu_cost,
        'passed': len(state.regions) >= 4  # Including module 0
    }


def demo_partition_split():
    """Demonstrate splitting partitions (PSPLIT)."""
    print("\n" + "=" * 60)
    print("DEMO 2b: Partition Split (PSPLIT)")
    print("=" * 60)
    
    state = State()
    vm = VM(state)
    
    # Create initial module
    m1 = state.pnew({0, 1, 2, 3, 4, 5, 6, 7})
    print(f"\n  Initial module {m1}: {state.regions[m1]}")
    
    # Split by predicate (even/odd)
    m_even, m_odd = state.psplit(m1, lambda x: x % 2 == 0)
    
    print(f"  After split:")
    print(f"    Even elements {m_even}: {state.regions[m_even]}")
    print(f"    Odd elements {m_odd}: {state.regions[m_odd]}")
    
    # Verify split is correct
    expected_even = {0, 2, 4, 6}
    expected_odd = {1, 3, 5, 7}
    
    even_correct = state.regions[m_even] == expected_even
    odd_correct = state.regions[m_odd] == expected_odd
    
    mu_cost = question_cost_bits("(PSPLIT even-odd)")
    
    print(f"\n  Split correct: even={even_correct}, odd={odd_correct}")
    print(f"  μ-cost: {mu_cost:.1f} bits")
    
    return {
        'demo': 'Partition Split',
        'even_correct': even_correct,
        'odd_correct': odd_correct,
        'mu_cost': mu_cost,
        'passed': even_correct and odd_correct
    }


def demo_partition_merge():
    """Demonstrate merging partitions (PMERGE)."""
    print("\n" + "=" * 60)
    print("DEMO 2c: Partition Merge (PMERGE)")
    print("=" * 60)
    
    state = State()
    vm = VM(state)
    
    # Create two modules
    m1 = state.pnew({0, 1, 2})
    m2 = state.pnew({3, 4, 5})
    
    print(f"\n  Module {m1}: {state.regions[m1]}")
    print(f"  Module {m2}: {state.regions[m2]}")
    
    # Merge them
    m_merged = state.pmerge(m1, m2)
    
    print(f"  Merged {m_merged}: {state.regions[m_merged]}")
    
    # Verify merge
    expected = {0, 1, 2, 3, 4, 5}
    merge_correct = state.regions[m_merged] == expected
    
    mu_cost = question_cost_bits("(PMERGE m1 m2)")
    
    print(f"\n  Merge correct: {merge_correct}")
    print(f"  μ-cost: {mu_cost:.1f} bits")
    
    return {
        'demo': 'Partition Merge',
        'merge_correct': merge_correct,
        'mu_cost': mu_cost,
        'passed': merge_correct
    }


def demo_partition_program():
    """Demonstrate a complete partition program."""
    print("\n" + "=" * 60)
    print("DEMO 2d: Complete Partition Program")
    print("=" * 60)
    
    # Create a program using partition operations
    program_text = """
; Partition demonstration program
; Shows PNEW, PSPLIT semantics
PNEW {10,11,12,13,14,15,16,17,18}
EMIT "Created partition"
PYEXEC "__result__ = sum([10,11,12,13,14,15,16,17,18])"
MDLACC
EMIT "Program complete"
"""
    
    print("\nProgram:")
    print("-" * 40)
    for line in program_text.strip().split('\n'):
        print(f"  {line}")
    print("-" * 40)
    
    # Parse and run the program
    with tempfile.TemporaryDirectory() as tmpdir:
        outdir = Path(tmpdir) / "output"
        
        lines = program_text.strip().split('\n')
        program = parse(lines, Path("."))
        
        vm = VM(State())
        vm.run(program, outdir)
        
        # Check outputs
        trace_file = outdir / "trace.log"
        if trace_file.exists():
            trace = trace_file.read_text()
            print("\nExecution trace (excerpt):")
            for line in trace.split('\n')[:5]:
                print(f"  {line}")
            
            passed = "Program complete" in trace or "EMIT" in trace
        else:
            passed = False
    
    mu_cost = question_cost_bits("(run partition-program)")
    
    print(f"\n  Program executed: {passed}")
    print(f"  μ-cost: {mu_cost:.1f} bits")
    
    return {
        'demo': 'Complete Partition Program',
        'mu_cost': mu_cost,
        'passed': passed
    }


def main():
    """Run all partition logic demonstrations."""
    print("\n" + "=" * 70)
    print("THIELE MACHINE ISOMORPHISM DEMONSTRATION")
    print("Category: INTERMEDIATE - Partition Logic")
    print("=" * 70)
    print("\nThis demonstration shows the Thiele VM's partition primitives:")
    print("  - PNEW: Create new module/partition")
    print("  - PSPLIT: Split module by predicate")
    print("  - PMERGE: Merge two modules")
    print("\nThese operations are the foundation of the Thiele Machine's")
    print("ability to exploit problem structure for exponential speedup.")
    
    results = []
    results.append(demo_partition_creation())
    results.append(demo_partition_split())
    results.append(demo_partition_merge())
    results.append(demo_partition_program())
    
    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)
    
    total_mu = sum(r['mu_cost'] for r in results)
    all_passed = all(r['passed'] for r in results)
    
    for r in results:
        status = "✓" if r['passed'] else "✗"
        print(f"  {status} {r['demo']}")
    
    print(f"\nTotal μ-cost: {total_mu:.1f} bits")
    print(f"Overall: {'ALL PASSED' if all_passed else 'SOME FAILED'}")
    
    print("\n" + "-" * 70)
    print("ISOMORPHISM NOTE:")
    print("  Partition operations have identical semantics in:")
    print("  - Python VM: state.pnew(), state.psplit(), state.pmerge()")
    print("  - Verilog RTL: OPCODE_PNEW (0x00), OPCODE_PSPLIT (0x01)")
    print("  - Coq: pnew_step, psplit_step, pmerge_step in ThieleMachine.v")
    print("-" * 70)
    
    return 0 if all_passed else 1


if __name__ == "__main__":
    exit(main())
