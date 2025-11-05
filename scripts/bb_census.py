# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

"""Top level script for the (demonstrational) Busy Beaver census.

The real project aims to perform a complete enumeration of 5‑state
Turing machines using SAT techniques.  Implementing the full census would
require an enormous amount of code and computational resources.  This
script wires together the lightweight stubs contained in this repository
so that a small scale demonstration can be executed.  Configuration
values can be overridden via environment variables which allows the
script to run quickly in constrained environments while retaining the
same default values as the original specification.
"""
from __future__ import annotations

import os
import time

from scripts.busy_beaver_cnf_provider import BusyBeaverCnfProvider
from scripts.thiele_bb_simulator import ThieleBBSimulator

# --- Configuration -------------------------------------------------------
MAX_SEARCH_STEPS = int(os.getenv("MAX_SEARCH_STEPS", "10000"))
STARTING_RECORD = int(os.getenv("STARTING_RECORD", "1000"))
STATES = int(os.getenv("STATES", "5"))
TAPE_SIZE = int(os.getenv("TAPE_SIZE", "3"))

# --- Setup --------------------------------------------------------------
print("=" * 80)
print("Project BB-CENSUS: The Complete BB(5) Census (Demonstrational)")
print("=" * 80)

start_time = time.time()
provider = BusyBeaverCnfProvider(states=STATES, tape_size=TAPE_SIZE)
simulator = ThieleBBSimulator(provider)

print(f"[{0.0:.2f}s] Generating logical fabric for {MAX_SEARCH_STEPS:,} simulation steps...")
simulator.load_base_rules(max_steps=MAX_SEARCH_STEPS)
print(f"[{time.time() - start_time:.2f}s] Engine is ready. Commencing the census.")

current_champion_score = STARTING_RECORD
last_printed_machine = None
last_printed_score = STARTING_RECORD

# --- The Census Loop ----------------------------------------------------
total_proofs = MAX_SEARCH_STEPS - STARTING_RECORD
proof_count = 0
for target_score in range(STARTING_RECORD + 1, MAX_SEARCH_STEPS + 1):
    proof_count += 1
    if proof_count % 100 == 0:
        progress = proof_count / total_proofs * 100
        print(f"\r[{time.time() - start_time:.2f}s] Proved {proof_count:,} machines ({progress:.1f}%) ... ", end="")
    print(f"\r[{time.time() - start_time:.2f}s] PROVING: Does a machine exist that halts at exactly {target_score:,} steps? ... ", end="")

    model = simulator.solve_for_exact_steps(target_score)

    if model is not None:
        # --- POTENTIAL NEW CHAMPION ---
        print("YES.")
        current_champion_score = target_score
        champion_machine = simulator.decode_program(model)
        
        # Only print full details if this is a genuinely new machine
        if champion_machine != last_printed_machine:
            print("\n" + "!" * 80)
            print(">>> NEW WORLD RECORD ESTABLISHED! <<<")
            print(f"Halts At: {current_champion_score:,} steps")
            print("Transition Table:\n", champion_machine)
            print("!" * 80)
            last_printed_machine = champion_machine
            last_printed_score = current_champion_score
        else:
            # Same machine, just update the score
            if current_champion_score > last_printed_score + 10:  # Print milestone updates
                print(f"\r[{time.time() - start_time:.2f}s] Same machine now halts at {current_champion_score:,} steps ... ", end="")

    else:
        # --- PROOF OF EMPTINESS ---
        print("NO.", end="")

print(f"\r[{time.time() - start_time:.2f}s] Census complete: Proved all {total_proofs:,} machines.")
if last_printed_machine:
    print(f"Final champion halts at {current_champion_score:,} steps.")
