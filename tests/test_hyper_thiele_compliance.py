print("Starting script...", flush=True)
from thielecpu.vm import VM
from thielecpu.state import State
from thielecpu.assemble import parse
from pathlib import Path
import json
import sys

# Ensure we can import thielecpu
sys.path.insert(0, str(Path(__file__).parent))

# Define a Hyper-Thiele program
program_source = """
; Hyper-Thiele Demonstration
; This program invokes the Oracle to solve the Halting Problem for a specific instance.

; 1. Define the undecidable instance (simulated)
PYEXEC "M_undecidable = 'while True: pass'"

; 2. Invoke the Oracle
ORACLE_HALTS "M_undecidable"

; 3. Check the result (stored in _oracle_result by VM)
PYEXEC "print(f'Oracle Verdict: {_oracle_result}')"

; 4. Emit the result
EMIT "Oracle Verdict: "
"""

# Parse
print("Parsing Hyper-Thiele program...")
program = parse(program_source.splitlines(), Path("."))

# Run
print("Executing in Thiele VM...")
vm = VM(State())
outdir = Path("results/hyper_thiele_demo")
vm.run(program, outdir)

# Verify
print("\n--- Verification ---")
summary = json.loads((outdir / "summary.json").read_text())
mu_op = summary["mu_operational"]
print(f"Total Operational Mu: {mu_op}")

if mu_op >= 1000000:
    print("SUCCESS: Oracle cost charged correctly (>= 1,000,000).")
else:
    print("FAILURE: Oracle cost NOT charged.")
    sys.exit(1)

receipts = json.loads((outdir / "step_receipts.json").read_text())
oracle_step = next(r for r in receipts if r["instruction"]["op"] == "ORACLE_HALTS")
print(f"Oracle Step Receipt Found: {oracle_step['instruction']['payload']}")

print("\nHyper-Thiele Execution Verified.")
