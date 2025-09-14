import time
from scripts.thiele_leviathan_simulator import ThieleLeviathanSimulator

# Simple test: Prove that no 2-state machine can halt at step 100
# (This is a toy example to demonstrate the SAT solving)

TARGET_SCORE = 100
STATES = 2

print("="*60)
print("Thiele Machine: Mini Proof Demonstration")
print(f"Objective: Prove that no {STATES}-state machine can halt at exactly {TARGET_SCORE} steps.")
print("="*60)

start_time = time.time()
print(f"[{time.time() - start_time:.3f}s] Initializing mini Thiele Engine...")
simulator = ThieleLeviathanSimulator(states=STATES)

print(f"[{time.time() - start_time:.3f}s] Posing the question...")
status = simulator.prove_unreachability(TARGET_SCORE)

end_time = time.time()

print(f"[{time.time() - start_time:.3f}s] MINI ANALYSIS COMPLETE.")
print(f"Total time: {end_time - start_time:.4f} seconds.")

if status == "UNSAT":
    print("\n" + "!"*60)
    print(">>> SUCCESS: The method works! <<<")
    print("!"*60)
    print(f"\nProven: No {STATES}-state machine can halt at exactly {TARGET_SCORE} steps.")
    print("This demonstrates the backwards-chaining SAT proof method.")

else:
    print("\n>>> Unexpected result. <<<")