# Axiom and admit inventory for the Thiele Machine development

_Updated after the full November 2025 tree-wide audit._

## Summary
- **Total Admitted**: 6 (four test placeholders in `thielemachine/verification/ThieleUniversalBridge_Axiom_Tests.v`
  plus two debugging admits in `thielemachine/coqproofs/debug_no_rule.v`, both outside `_CoqProject`).
- **Total Axioms**: 6, concentrated in the universal-bridge work-in-progress.
  - Five axioms in `thielemachine/verification/ThieleUniversalBridge.v` document the still-unproved checkpoint
    lemmas used during symbolic execution of the archived trace.
  - One staging axiom in `thielemachine/verification/modular/Bridge_LengthPreservation.v` mirrors the
    register-bound claim in the legacy modularised refactor; the modular files are not part of `_CoqProject`.
- **Kernel and optional studies**: 0 admits and 0 axioms. The `make -C coq core` and `make -C coq optional`
  builds completed cleanly under the apt-installed Coq 8.18.0 toolchain.
- **Bridge build status**: `make -C coq bridge-timed BRIDGE_TIMEOUT=300` timed out while replaying the archived
  `ThieleUniversalBridge.v` trace; the axioms above remain in place until that replay is mechanised.

## File-by-file notes
- `thielemachine/verification/ThieleUniversalBridge.v` – five axioms capture the remaining FindRule guard and
  checkpoint obligations while the archived trace replay continues to time out during `make bridge-timed`.
- `thielemachine/verification/modular/Bridge_LengthPreservation.v` – retains a single axiom matching the
  register-bound claim for the legacy modular refactor; the rest of the modular bridge skeleton is definitionally
  complete but still excluded from `_CoqProject`.
- `thielemachine/verification/ThieleUniversalBridge_Axiom_Tests.v` – four admitted stubs in the test harness
  that exercises the axiomatized lemmas above; not in `_CoqProject`.
- `thielemachine/coqproofs/debug_no_rule.v` – two preserved admits for the experimental no-rule reproduction;
  excluded from `_CoqProject`.
- All other Coq sources (kernel, modular proofs, thielemachine core, optional studies) are free of axioms and
  admits as of this audit.

## Next steps
- Keep this file and `coq/ADMIT_REPORT.txt` in sync after any change to the axioms or admits until the reporting
  scripts are repaired.
- When the bridge replay proofs land, remove the axioms in `ThieleUniversalBridge.v` and retire the staging
  axiom in the modular refactor; update the build documentation accordingly.
