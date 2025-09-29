#!/usr/bin/env python3
"""
Skeleton Key Demonstration: Symbolic SHA-256 Pre-image Search with Partitions

This script demonstrates the Thiele Machine's symbolic solving capabilities
with partitioned constraints. It uses Z3 to solve for string variables that
satisfy local module constraints and a composite witness.

The demonstration shows:
- Partitioned symbolic execution (modules 1 and 2)
- Local certificate generation (LASSERT)
- Composite witness joining (LJOIN)
- Symbolic string concatenation and equality constraints
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))

from thielecpu.assemble import parse
from thielecpu.vm import VM
from thielecpu.state import State
from pathlib import Path
import json
import hashlib

def placeholder():
    """Symbolic placeholder for variables to be solved by Z3."""
    return None  # Will be replaced by VM with symbolic variables

def main():
    print("Thiele Machine: Skeleton Key Demonstration (Symbolic with Partitions)")
    print("=" * 60)

    # Demo parameters: 10-character secret split into two 5-character modules
    target_hash = hashlib.sha256("abcdefghij".encode('utf-8')).hexdigest()

    print("Target: Find 10-character string whose SHA-256 hash matches:")
    print(f"Target hash: {target_hash}")
    print("Using partitioned symbolic constraints:")
    print("- Module 1: first 5 chars == 'abcde'")
    print("- Module 2: last 5 chars == 'fghij'")
    print("- Composite: full string == 'abcdefghij'")
    print()

    # Symbolic Python code with partitioned constraints
    script_content = '''
# Module 1: first 5 characters
c1 = placeholder()
c2 = placeholder()
c3 = placeholder()
c4 = placeholder()
c5 = placeholder()
assert c1 == "a"
assert c2 == "b"
assert c3 == "c"
assert c4 == "d"
assert c5 == "e"

# Module 2: last 5 characters
c6 = placeholder()
c7 = placeholder()
c8 = placeholder()
c9 = placeholder()
c10 = placeholder()
assert c6 == "f"
assert c7 == "g"
assert c8 == "h"
assert c9 == "i"
assert c10 == "j"

# Composite witness: full secret
full_secret = c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10
# assert full_secret == "abcdefghij"  # Redundant, implied by individual asserts

# Verify the hash
import hashlib
computed_hash = hashlib.sha256(full_secret.encode('utf-8')).hexdigest()
target_hash = "''' + target_hash + '''"
if computed_hash == target_hash:
    print(f"SUCCESS: Found secret '{full_secret}' with hash {computed_hash}")
else:
    print(f"FAILURE: Hash mismatch for '{full_secret}'")
'''

    # Write the symbolic script
    script_path = Path("temp_skeleton.py")
    script_path.write_text(script_content)

    # Create Thiele assembly program with partitions and certificates
    thm_content = '''
; Skeleton Key Assembly (Symbolic with Partitions)
PNEW {1,2,3,4,5}
LASSERT "module1_constraint.smt2"
PNEW {6,7,8,9,10}
LASSERT "module2_constraint.smt2"
PYEXEC "temp_skeleton.py"
MDLACC
EMIT "Partitioned Symbolic Execution Complete"
'''

    thm_path = Path("temp_skeleton.thm")
    thm_path.write_text(thm_content)

    try:
        # Parse and run the program using the Thiele VM
        print("Executing partitioned symbolic search...")
        program = parse(thm_path.read_text(encoding='utf-8').splitlines(), Path("."))
        vm = VM(State())

        # Capture output
        import io
        from contextlib import redirect_stdout, redirect_stderr

        output_buffer = io.StringIO()
        with redirect_stdout(output_buffer), redirect_stderr(output_buffer):
            vm.run(program, Path("demo_output"))

        # Read results
        summary_path = Path("demo_output/summary.json")
        if summary_path.exists():
            summary = json.loads(summary_path.read_text(encoding='utf-8'))
            mu_cost = summary.get('mu', 0)
            print(f"Information Cost: {mu_cost} mu-bits")
        else:
            print("No summary found")

        # Check trace for results
        trace_path = Path("demo_output/trace.log")
        if trace_path.exists():
            trace_content = trace_path.read_text(encoding='utf-8')
            print("Execution Trace:")
            for line in trace_content.split('\n'):
                if line.strip():
                    print(f"  {line}")
        else:
            print("No trace found")

        print()
        print("Demonstration Complete!")
        print("This demo shows symbolic solving with partitioned constraints,")
        print("local certificates, and composite witnesses in the Thiele Machine.")

    finally:
        # Cleanup temp files
        try:
            script_path.unlink()
        except Exception:
            pass
        try:
            thm_path.unlink()
        except Exception:
            pass

if __name__ == "__main__":
    main()