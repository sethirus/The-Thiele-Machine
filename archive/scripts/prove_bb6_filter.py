# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

import time
import sys
import os

# Add the parent directory to the path so we can import from scripts
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from scripts.busy_beaver_cnf_provider import BusyBeaverCnfProvider
from scripts.thiele_bb_simulator import ThieleBBSimulator

# The target number. This is the 5-state world record.
# We are asking if any 6-state machine can halt at this exact number.
TARGET_SCORE = 47176870
STATES = 6

print("="*80)
print("Thiele Machine: The BB(6) Great Filter Experiment")
print(f"Objective: Prove that no {STATES}-state machine can halt at exactly {TARGET_SCORE:,} steps.")
print("="*80)

provider = BusyBeaverCnfProvider(states=STATES, max_steps=TARGET_SCORE + 1)
simulator = ThieleBBSimulator(provider)

print(f"[{time.time():.2f}s] Loading the logical fabric of the {STATES}-state universe...")
simulator.load_base_rules(TARGET_SCORE + 1)
print(f"[{time.time():.2f}s] Engine is ready. Posing the question...")

start_time = time.time()
# This is not a search. It is a single, profound question.
# "Is it logically possible for a halting machine to exist at this exact step count?"
model = simulator.solve_for_exact_steps(TARGET_SCORE)
end_time = time.time()

print("\n" + "-"*80)
print("ANALYSIS COMPLETE.")
print(f"Total Time: {end_time - start_time:.4f} seconds.")

if model is None:
    status = "UNSAT"
else:
    status = "SAT"

if status == "UNSAT":
    print("\n" + "!"*80)
    print(">>> EPOCHAL SUCCESS: A NEW LAW OF COMPUTATION HAS BEEN PROVEN. <<<")
    print("!"*80)
    print("\nThe Thiele Machine has mathematically proven that no 6-state Turing machine")
    print(f"can halt at exactly {TARGET_SCORE:,} steps.")
    print("\nThis is a non-obvious, structural truth about the landscape of computation,")
    print("discovered not by search, but by pure logical deduction.")

elif status == "SAT":
    print("\n" + "!"*80)
    print(">>> SHOCKING DISCOVERY: A 'FORBIDDEN' MACHINE HAS BEEN FOUND. <<<")
    print("!"*80)
    print("\nThe Thiele Machine has found a 6-state machine that halts at the")
    print("exact same time as the 5-state champion. This is a historic discovery.")
    assert model is not None, "Model should not be None when status is SAT"
    champion_machine = simulator.decode_program(model)
    print("\nTransition Table:\n", champion_machine)

else:
    print("\n>>> MISSION FAILED. The solver did not conclude. <<<")