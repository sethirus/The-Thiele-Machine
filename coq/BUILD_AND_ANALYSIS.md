# Coq Build Verification Notes

## Environment Preparation
- Installed `coq` (8.18.0) and its toolchain via `apt-get` to provide the kernel proof dependencies.

## Build Command
- Executed `make -C coq kernel/MuLedgerConservation.vo` to compile the ledger conservation development.

## Outcome
- Compilation completed without errors, confirming that `vm_step_respects_mu_ledger`, the new prefix lemma (`bounded_prefix_mu_balance`), the bounded-decomposition lemmas, and the `gestalt_matches_isomorphism` bridge integrate cleanly with the existing kernel proofs.
- The build step rechecked the supporting files (`VMState.v`, `VMStep.v`, `Kernel.v`, `KernelThiele.v`, `VMEncoding.v`, `SimulationProof.v`) before finishing successfully.

## Notes
- The `_CoqProject` loadpath now points at the archived `ThieleUniversal` catalogue so the previous `UTM_Rules` warning no longer appears on subsequent builds.
- No additional Coq admits or axioms were introduced during the build.

## Core rebuild after toolchain refresh (2025-11-09)
- Reinstalled the Coq toolchain from Ubuntu packages (`coq` 8.18.0 via `apt-get`) to ensure the development uses the audited compiler stack.
- Ran the full core pipeline with `make -C coq core`; every kernel, modular proof, and thielemachine module in `_CoqProject` completed without errors.
- Verified that the run did not surface new admits or axioms beyond the existing inventory; the build finished cleanly after recompiling the archived helper files listed in `_CoqProject`.

## Optional manifold bridge check (2025-11-25)
- Compiled the new `thiele_manifold/ThieleManifoldBridge.v` study with `make -C coq thiele_manifold/ThieleManifoldBridge.vo` after installing Coq via `apt-get install -y coq`.
- The build confirms the abstract manifold now has a concrete base witness tied to `ThieleProc` receipts and still enjoys the positive μ-cost projection property captured in `ThieleManifold.v`.

## Irreversibility lower bound rebuild (current)
- Refreshed the toolchain with `apt-get update` followed by `apt-get install -y coq` to ensure Coq 8.18.0 is available for local builds.
- Recompiled the core suite (`make -C coq core`) after adding the public-facing irreversibility alias (`vm_irreversible_bits_lower_bound`) to `kernel/MuLedgerConservation.v`.
- Rebuilt the manifold bridge (`make -C coq thiele_manifold/ThieleManifoldBridge.vo`) to surface the closed-form gap (`thiele_level_mu_gap`) alongside the faithful-implementation transport.
- Compiled the new optional physics stubs (`make -C coq physics/DiscreteModel.vo thiele_manifold/PhysicsIsomorphism.vo`) to document the reversible lattice-gas case study and the physics-is-computation conjecture scaffold.
- All targeted builds completed without errors, confirming the strengthened µ/entropy linkage and the optional physics scaffolding integrate cleanly with the existing proofs.
- Re-ran the optional physics suite (`make -C coq physics/DiscreteModel.vo thielemachine/coqproofs/PhysicsEmbedding.vo thiele_manifold/PhysicsIsomorphism.vo`) after adding the concrete conservation/irreversibility transport lemmas for the lattice-gas embedding; the build remained clean.
- Added a dissipative physics witness and recompiled the optional stack (`make -C coq physics/DiscreteModel.vo physics/DissipativeModel.vo thielemachine/coqproofs/PhysicsEmbedding.vo thielemachine/coqproofs/DissipativeEmbedding.vo thiele_manifold/PhysicsIsomorphism.vo`) to confirm the reversible and irreversible case studies both integrate with the faithful-implementation ledger bounds.

## Wave propagation evidence (current)
- Compiled the extended optional suite with the new wave model and embedding (`make -C coq physics/WaveModel.vo thielemachine/coqproofs/WaveEmbedding.vo thiele_manifold/PhysicsIsomorphism.vo`) after refreshing `_CoqProject` and `Makefile.local`.
- Verified the reversible wave invariants (energy, momentum-like) transport cleanly through the VM/faithful-implementation lemmas and leave µ unchanged, providing a third case study alongside the lattice gas and dissipative lattice.

## Hardware/VM cost alignment (current)
- Installed the Coq + RTL toolchain locally (`apt-get update && apt-get install -y coq yosys`) to exercise both the proof stack and the Verilog-facing helpers.
- Rebuilt the optional bridge glue (`make -C coq thiele_manifold/ThieleManifoldBridge.vo thielemachine/coqproofs/HardwareVMHarness.vo`) to surface the faithful-implementation µ-equality (`faithful_impl_mu_conservation`, `faithful_impl_cost_delta`) and the RTL wrapper (`rtl_mu_conservation`) that tie decoded hardware executions back to the VM ledger.
