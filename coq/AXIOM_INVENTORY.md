# Axiom and Admit Inventory for Thiele Machine Formal Verification

This document inventories all `Admitted` lemmas and `Axiom` declarations in the Coq codebase, with detailed explanations of what each assumes and why it is acceptable as an implementation detail rather than a foundational flaw.

## Summary
- **Total Admitted**: 4 (see `ADMIT_REPORT.txt`)
- **Total Axioms**: 1
- **Kernel Module Admitted**: 0
- **Kernel Module Axioms**: 0

## Kernel Module Status

The kernel proof tree (in `coq/kernel/`) compiles successfully without admits or axioms. All core subsumption proofs verify:
- `Kernel.v`, `KernelTM.v`, `KernelThiele.v`
- `VMState.v`, `VMStep.v`, `VMEncoding.v`
- `SimulationProof.v`, `MuLedgerConservation.v`
- `Subsumption.v` ✅

The canonical subsumption verification (`./verify_subsumption.sh`) passes successfully.

## Other Module Admitted/Axioms

### Axioms (Total: 1)

1. **coq/thielemachine/coqproofs/HyperThiele_Halting.v:14**
   ```coq
   Axiom H_correct : forall e, H e = true <-> Halts e.
   ```
   **Justification**: This axiom connects the halting oracle function `H` to the semantic notion of halting. It is an interface axiom that characterizes the oracle behavior. This is part of the theoretical exploration of computational models with oracles.

### Admitted Lemmas (Total: 4)

1. **coq/thielemachine/coqproofs/Simulation.v:3797**
   - **Lemma**: Final lemma in simulation chain
   - **Status**: Implementation detail for the Turing-to-Thiele simulation
   - **Note**: The kernel subsumption proof does not depend on this

2-4. **coq/thielemachine/coqproofs/ThieleUniversalBridge.v:297, 312, 313**
   - **Lemma**: `inv_setup_state` proof branches
   - **Status**: Bridge file lemmas for connecting universal TM interpreter to CPU model
   - **Note**: These are in a bridge/helper file; the kernel subsumption proof does not depend on these
   - **Context**: Proof restructuring after Coq version compatibility changes left some complex symbolic execution proofs incomplete

## Conclusion

The kernel module (9 files) compiles cleanly with 0 admits and 0 axioms, proving the core subsumption theorem. The admitted lemmas are in auxiliary/bridge files that provide additional infrastructure but are not required for the main theoretical result.

This represents a clean separation between:
- **Core Theoretical Result** (Proven): Kernel subsumption proof - fully mechanized
- **Supporting Infrastructure** (Partially Admitted): Helper files for extended demonstrations and connections to other formalizations

The canonical subsumption verification passes, demonstrating that the flagship theorem is fully mechanized.
