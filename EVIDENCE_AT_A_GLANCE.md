Thiele Machine — Declaration + Evidence (One Page)

Claim
-----
The Thiele Machine (a formally specified model) strictly contains the
Turing Machine: there exists a family of instances for which Thiele
programs solve the task with polynomial information cost while blind
Turing-style search incurs exponential classical-time cost — under the
explicit axioms listed in `coq/AXIOM_INVENTORY.md`.

Key evidence
------------
- Mechanised proof: `coq/thielemachine/coqproofs/Separation.v` (Coq buildable via `coq/verify_subsumption.sh`)
- Runtime receipts: `thielecpu/vm.py` emits trusted step receipts; example receipts in `artifacts/`.
- Receipt verification: `scripts/challenge.py verify receipts` successfully validates the sample runs.
- Empirical data: `experiments/lab_notebook_template.csv` and generated plots are produced by `experiments/run_analysis.py`.
- Hardware alignment: Verilog in `thielecpu/hardware/` with test harnesses in `thielecpu/hardware/test_hardware.py`.

Minimal verification checklist (1-2 hours)
-----------------------------------------
1. Re-run canonical pipeline: `python3 demonstrate_isomorphism.py`.
2. Verify receipts and mechanised replay:
  - Signature/schema checks: `python scripts/challenge.py verify receipts`
  - Mechanised Coq replay: `./scripts/verify_truth.sh examples/tsirelson_step_receipts.json`
3. Build Coq: `cd coq && ./verify_subsumption.sh` (may take longer).
4. Run analysis: `python3 experiments/run_analysis.py` and inspect `experiments/plot_*.png`.

Risk & assumptions (top of the stack)
------------------------------------
- The separation depends on explicit axioms; see `coq/AXIOM_INVENTORY.md`.
- Empirical scaling conclusions require careful statistical analysis and
  independent replication on matched hardware.

Contact
-------
For replication support and data requests contact: thethielemachine@gmail.com
