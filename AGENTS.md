# Repository Instructions

1. Before editing any files, install Coq in the container environment:
   ```bash
   sudo apt-get update
   sudo apt-get install -y coq
   ```
2. After installing Coq, install the Python dependencies so every orchestrator
   and demo can execute:
   ```bash
   pip install -e .
   ```
   This editable install provides the full scientific stack (NumPy, SciPy,
   Astropy/Healpy, python-sat, Z3, etc.) required by `demonstrate_isomorphism.py`,
   `attempt.py`, `scripts/challenge.py`, and the demo suite.
3. Focus active development on the modular subsumption proof. Use the
   lightweight `coqc` invocations against the `coq/modular_proofs` directory to
   validate changes quickly instead of running the full build.
4. Document meaningful progress toward mechanising that the Thiele machine
   subsumes the Turing machine without admits, keeping status reports in sync
   with the modular plan.
