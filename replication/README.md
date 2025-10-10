Thiele Machine Replication Kit

Usage
-----

1. Build the container (from repo root)

   docker build -t thiele-replication:latest -f replication/Dockerfile .


2. Run the container (it will execute the canonical pipeline):

   docker run --rm -v "$PWD":/workspace thiele-replication:latest

What it does
------------
- Runs `python3 demonstrate_isomorphism.py` (canonical thesis run) to generate receipts and artifacts. The container can also be invoked manually to run `python attempt.py` for the broader universal orchestrator and extra experiments; see `replicate.sh` for the default behavior.
- Runs `python scripts/challenge.py verify receipts` to verify the receipts.
- Runs `python3 experiments/run_analysis.py` to compute basic scaling fits and
  generate plots.

Notes
-----
- For full Coq verification, install the Coq Platform inside the container or
  use the repository's dedicated verification environment; the Dockerfile
  includes the Python environment and tools for the runtime and analysis only.
