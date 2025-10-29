# Integration instructions — instrument the VM to emit per-step ledger logs

Goal
- Produce reliable, scientifically meaningful tests by (A) getting real per-step µ ledger output from a VM implementation that matches the Coq definitions and (B) re-running experiments with increased sampling. This document gives a concrete, reproducible plan and commands to implement the instrumentation.

Why this approach
- The Coq files [`coq/kernel/MuLedgerConservation.v`](coq/kernel/MuLedgerConservation.v:21) and [`coq/kernel/VMStep.v`](coq/kernel/VMStep.v:61) specify the semantics and costs. To test Landauer/EIN/CWD numerically we must run a faithful reference VM (or an extracted VM) that emits the ledger entries used in the proofs.
- Practical path: create a small reference VM in Python matching the Coq `vm_instruction`, `vm_apply`, and `run_vm` behaviour, instrument it to log (step, vm_mu, delta) per step, and pipe the logs through the existing adapter/verifiers.

High-level steps
1. Implement a Python reference VM that mirrors Coq definitions
   - File to create: [`experiments/vm_reference.py`](experiments/vm_reference.py:1)
   - Implement data types: VMState, vm_instruction (subset sufficient for experiments), instruction_cost, vm_apply, run_vm, ledger_entries, bounded_run.
   - Keep semantics identical to Coq where possible (advance pc, vm_mu update via instruction_cost).

2. Add logging in the reference VM
   - Output per-step lines (CSV or JSON) with keys: step, vm_mu, delta.
   - Example line (CSV): `1,2,2`
   - Example line (JSON): `{"step":1,"vm_mu":2,"delta":2}`

3. Convert logs to verifier CSVs
   - Use the adapter:
     - Normalize logs: [`scripts/instrumentation_adapter.py`](scripts/instrumentation_adapter.py:1)
     - Produce ledger CSVs (step,vm_mu,delta).

4. Produce Landauer/EIN/CWD summaries from ledger CSVs
   - Landauer: use [`experiments/use_ledger_landauer.py`](experiments/use_ledger_landauer.py:1).
   - Einstein: adapt `experiments/run_einstein.py` to accept ledger-driven runs or compute MSD from many reference runs.
   - CWD: run `experiments/run_cwd.py` with the reference VM when routing policies are used.

5. Re-run verifiers
   - Landauer: `python3 verifier/check_landauer.py`
   - Einstein: `python3 verifier/check_einstein.py`
   - CWD: implement `verifier/check_cwd.py` (similar pattern) and run.

Concrete commands (example workflow)
- Create a small reference trace (toy):
  python3 experiments/vm_reference.py --seed 0 --fuel 10 --trace tests/sample_trace.json --out logs/run0.log
- Normalize:
  python3 scripts/instrumentation_adapter.py --input logs/run0.log --output logs/run0.csv
- Produce Landauer summary:
  python3 experiments/use_ledger_landauer.py --ledger logs/run0.csv --T 1.0 --seed 0 --trial 0 --out results/landauer_from_ledger
- Run verifier:
  python3 verifier/check_landauer.py

Scaling guidance for meaningful statistics
- Einstein: set n_walkers ≥ 10_000 or steps ≥ 5_000 (or many repeated trials) to reduce estimator variance.
- Landauer/CWD: run hundreds of independent trials (seeds) for each condition to estimate mean_diff with tight confidence intervals.
- Use bootstrap or confidence-interval estimation in verifiers.

Implementation notes / pitfalls
- Keep instruction_cost units consistent with the verifier expectation (ledger entries interpreted as "bits" or numeric deltas; convert using log2 if needed). The verifier expects "sum_mu_bits" to be the ledger sum in bits — ensure the reference VM uses the same unit as `instruction_cost`.
- If the Coq `instruction_cost` is not in bits, add a conversion step in `use_ledger_landauer.py`.
- Prefer deterministic RNG seeds and save raw logs for audit.
- If you eventually want a fully verified pipeline, consider extracting the Coq `run_vm` to OCaml via `coq-of-ocaml`/extraction and instrument that; the Python reference is faster to iterate.

Files to add (suggested)
- [`experiments/vm_reference.py`](experiments/vm_reference.py:1) — reference interpreter + logging
- [`logs/`...] — runtime logs per run
- Use existing:
  - [`scripts/instrumentation_adapter.py`](scripts/instrumentation_adapter.py:1)
  - [`experiments/use_ledger_landauer.py`](experiments/use_ledger_landauer.py:1)
  - [`verifier/check_*.py`](verifier/check_landauer.py:1, verifier/check_einstein.py:1)

Next automated actions I will perform (if you confirm)
- Create a minimal [`experiments/vm_reference.py`](experiments/vm_reference.py:1) that implements a small instruction set, emits per-step logs, and can be used as a drop-in for experiments.
- Run a short batch of experiments using that reference VM, normalize logs, and produce verifier outputs with increased sampling (Einstein: n_walkers=10k, steps=5k for a smoke run).

Confirm "proceed" to have me implement `experiments/vm_reference.py` and run a scaled smoke experiment, or reply "modify" to change the plan.