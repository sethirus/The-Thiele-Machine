# Repository Instructions

1. Before editing any files, install Coq in the container environment:
   ```bash
   sudo apt-get update
   sudo apt-get install -y coq
   ```
2. Focus active development on the modular subsumption proof. Use the lightweight
   `coqc` invocations against the `coq/modular_proofs` directory to validate
   changes quickly instead of running the full build.
3. Document meaningful progress toward mechanising that the Thiele machine
   subsumes the Turing machine without admits, keeping status reports in sync
   with the modular plan.
