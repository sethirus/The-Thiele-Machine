# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

#!/usr/bin/env python3
"""
Skeleton Key Demonstration: Reproducible SHA-256 Pre-image Search Demo

This script performs a reproducible demonstration of searching a small password
space for a string whose SHA-256 hash matches a known target. For reliability in
a demo environment we choose a short secret that is guaranteed to be in the
search space so the brute-force run terminates quickly.

This replaces an earlier symbolic-placeholder approach with a concrete,
self-contained brute-force search (no placeholders), and keeps the Thiele VM
invocation so the run generates the usual `demo_output` artifacts.
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

def main():
    print("Thiele Machine: Skeleton Key Demonstration (brute-force)")
    print("=" * 50)

    # Demo parameters (kept small so the demo finishes quickly)
    alphabet = 'abcdefghijklmnopqrstuvwxyz0123456789'
    length = 4  # search for 4-character secrets
    search_space = len(alphabet) ** length

    # Choose a secret that is known and inside the search space so the demo
    # always finds a result quickly. In a real experiment this would be unknown.
    secret_to_find = 'a0b1'  # must be in alphabet^length
    target_hash = hashlib.sha256(secret_to_find.encode('utf-8')).hexdigest()

    print(f"Target: Find string s of length {length} over alphabet size {len(alphabet)}")
    print(f"Target hash (SHA-256): {target_hash}")
    print(f"Search space: {len(alphabet)}^{length} = {search_space} possibilities")
    print(f"Classical probability of random guess: 1 in {search_space}")
    print()

    # Create the concrete Python script content that performs a brute-force
    # search (no symbolic placeholders required). The script will print a line
    # starting with 'FOUND:' when it discovers the target.
    script_content = f'''
import hashlib

alphabet = "{alphabet}"
length = {length}
target_hash = "{target_hash}"

found = False
for combo in itertools.product(alphabet, repeat=length):
    s = ''.join(combo)
    h = hashlib.sha256(s.encode('utf-8')).hexdigest()
    if h == target_hash:
        print(f"FOUND: Secret = '{{s}}', Hash = {{h}}")
        found = True
        break

if not found:
    print("NOTFOUND")
'''

    # Write the script to a temporary file
    script_path = Path("temp_skeleton.py")
    script_path.write_text(script_content)

    # Create Thiele assembly program (unchanged semantics)
    thm_content = '''
 ; Skeleton Key Assembly (brute-force)
 PNEW {1}
 PYEXEC "temp_skeleton.py"
 MDLACC
 EMIT "Skeleton Key Found"
 '''

    thm_path = Path("temp_skeleton.thm")
    thm_path.write_text(thm_content)

    try:
        # Parse and run the program using the Thiele VM
        print("Searching for pre-image (brute-force)...")
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

        # Check for found secret in trace
        trace_path = Path("demo_output/trace.log")
        if trace_path.exists():
            trace_content = trace_path.read_text(encoding='utf-8')
            for line in trace_content.split('\n'):
                if "FOUND:" in line:
                    # Extract the FOUND line
                    found_line = line.split("FOUND:")[1].strip()
                    print(found_line)
                    break
            else:
                print("Secret not found in trace")
        else:
            print("No trace found")

        print()
        print("Demonstration Complete!")
        print("This demo shows a reproducible brute-force search for an embedded")
        print("secret within a small search space. It does not imply a cryptanalytic")
        print("break of SHA-256 or general pre-image resistance.")

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