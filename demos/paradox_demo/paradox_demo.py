# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

#!/usr/bin/env python3
"""
Paradox Demonstration for the Thiele Machine

This script demonstrates the PDISCOVER instruction finding logical paradoxes
through partition discovery.
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))

from thielecpu.assemble import parse
from thielecpu.vm import VM
from thielecpu.state import State
from pathlib import Path
import json

def main():
    print("Thiele Machine: Paradox Demonstration")
    print("=" * 40)

    # Create Thiele assembly program for paradox demonstration
    thm_content = '''
; Paradox demonstration program for the Thiele Machine
; This program creates a module and uses PDISCOVER to find partitions that create paradoxes

; Create a module with regions {1,2,3,4,5}
PNEW {1,2,3,4,5}

; Use PDISCOVER with both contradictory axiom files
; PDISCOVER will try partitions and assign different axioms to different parts
PDISCOVER 2 paradox_module_a.smt2 paradox_module_b.smt2

; Accumulate MDL cost
MDLACC

; Emit result
EMIT "Paradox demonstration completed"
'''

    print("Running paradox demonstration...")
    print("This will test PDISCOVER's ability to find partitions where")
    print("contradictory axioms (x=1 vs x=2) create unsatisfiable combinations.")
    print()

    try:
        # Parse and run the program using the Thiele VM
        program = parse(thm_content.splitlines(), Path("."))
        vm = VM(State())

        # Run the program
        vm.run(program, Path("paradox_output"))

        # Read results
        summary_path = Path("paradox_output/summary.json")
        if summary_path.exists():
            summary = json.loads(summary_path.read_text(encoding='utf-8'))
            mu_operational = summary.get('mu_operational', 0)
            mu_information = summary.get('mu_information', 0)
            mu_total = summary.get('mu_total', 0)
            print("\nResults:")
            print(f"Operational Cost: {mu_operational} μ-bits")
            print(f"Information Cost: {mu_information} μ-bits")
            print(f"Total Cost: {mu_total} μ-bits")
        else:
            print("No summary found")

        # Check trace for PDISCOVER results
        trace_path = Path("paradox_output/trace.log")
        if trace_path.exists():
            trace_content = trace_path.read_text(encoding='utf-8')
            print("\nPDISCOVER Results:")
            for line in trace_content.split('\n'):
                if "PDISCOVER" in line:
                    print(f"  {line}")
        else:
            print("No trace found")

        print()
        print("Paradox Demonstration Complete!")
        print("If successful, PDISCOVER found a partition where contradictory")
        print("axioms create an unsatisfiable logical system.")

    except Exception as e:
        print(f"Error running paradox demonstration: {e}")
        import traceback
        traceback.print_exc()

if __name__ == "__main__":
    main()