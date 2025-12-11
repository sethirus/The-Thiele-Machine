# Agent workflow for The Thiele Machine

This repository now has Coq and Yosys toolchains installed in the build image. Keep the following rules in mind when iterating:

## Proof, RTL, and VM work
- Keep Coq proofs admit-free. If you must introduce or retain an axiom, document why it is unavoidable and update `coq/ADMIT_REPORT.txt` and `coq/AXIOM_INVENTORY.md` in the same change.
- Prefer turning axioms into lemmas with proofs; avoid `Admitted.` in new code.
- When altering the Verilog/RTL or VM generation flow, ensure it remains isomorphic to the proven Coq model. Regenerate both Coq artifacts and the Verilog outputs as needed.
- Use test-driven development: add or update Coq tests before modifying proofs; for hardware changes, add yosys/iverilog checks where applicable.
- If you land in an environment that does not already have the toolchain, install the Coq compiler along with Verilog/yosys utilities (`sudo apt-get update && sudo apt-get install -y coq yosys iverilog`) before running the required builds. If the package names differ, prefer the distro packages for `coq`, `coqide`, `yosys`, and `iverilog` so the end-to-end VM/RTL pipeline stays reproducible.
- Keep the Coq→Verilog→VM chain healthy: after updating proofs, regenerate RTL artifacts (via the existing `scripts/synth.ys` or Makefile targets) and re-run the Python VM regression suite to ensure the extracted behavior matches the proven model.
- Favor TDD when refining the Python VM: add unit tests in `tests/` mirroring the Coq obligations before modifying VM code so coverage tracks proof intent.

## Documentation hygiene
- Remove or archive stale or inaccurate Markdown documents. Keep only current, accurate guidance in active locations.
- When archiving, move files into the `archive/` tree with a brief note in the commit message explaining why.

## Required commands before committing
- Run `make -C coq core` after touching files under `coq/`.
- Run the specific `.vo` targets or RTL builds you altered, plus `make -C coq bridge-timed BRIDGE_TIMEOUT=900` when working on bridge proofs.
- For RTL/VM changes, run yosys synthesis checks relevant to the modified modules (e.g., `yosys -s scripts/synth.ys`).

## Progress reporting
- Keep commit messages explicit about which admits or documents were removed/added.
- Capture any recurring failure signatures or proof obligations in the PR description to aid future contributors.
