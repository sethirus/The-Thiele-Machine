# Repository Instructions

## Environment bootstrap
1. Before editing any files, install Coq and the supporting tooling in the
   container environment:
   ```bash
   sudo apt-get update
   sudo apt-get install -y coq coqide
   ```
   (The `coq` package ships `coq_makefile`; installing it up front prevents the
   build failures noted by the last audit.)
2. After installing Coq, install the Python dependencies so every orchestrator
   and demo can execute:
   ```bash
   pip install -e .
   ```
   This editable install provides the full scientific stack (NumPy, SciPy,
   Astropy/Healpy, python-sat, Z3, etc.) required by the automation scripts and
   demos.

## Operation Unification workflow
- Maintain `docs/operation_unification_progress.md` as the single source of
  truth for granular status updates. Update it whenever scope or findings
  change so the log reflects the current plan of record.
- Respect the reopened milestone ordering:
  1. **Milestone 1 – Coq Gauntlet (✅ complete)**
  2. **Milestone 2 – Formal VM Bridge (🚧 active)**
  3. **Milestone 3 – Simulation Proof (🔒 blocked on Milestone 2)**
  Do not begin a later milestone until the log records completion of the active
  one and its acceptance criteria are satisfied.
- While Milestone 2 is in progress, every change must preserve or improve the
  fidelity of the VM state encoding and its bridge to the kernel tape. Treat the
  Python VM data structures as the ground truth for the Coq records.
- Capture successful build transcripts in `audit_logs/agent_coq_verification.log`
  once the Coq project compiles cleanly. When tooling is unavailable, record the
  limitation explicitly in the progress log.
- Before modifying public documentation (README, fact-check ledgers, etc.), make
  sure the progress log reflects the current evidence so no document overstates
  results.

Adhere to these rules before modifying any other project documentation or
formal artefacts.
