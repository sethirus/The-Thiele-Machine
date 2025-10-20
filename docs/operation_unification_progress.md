# Operation Unification Progress Log

This document tracks granular progress toward Operation Unification.
Only one milestone is tackled at a time; later milestones remain blocked
until earlier ones are completed and validated.

## Milestone 1 – Coq Gauntlet (✅ Completed 2025-10-29)

### Final Status
- `_CoqProject` now enumerates only the live libraries (kernel, thielemachine, modular proofs, sandboxes, catnet, shor primitives, etc.), purging all archived `thieleuniversal` remnants.
- Regenerated `Makefile` artefacts build cleanly under Coq 8.18.0; `make -C coq clean && make -C coq` succeeds end-to-end.
- `coq/verify_subsumption.sh` orchestrates the canonical clean+build workflow and fails fast when the Coq toolchain is missing.
- The passing build transcript is captured in `audit_logs/agent_coq_verification.log` for reproducibility.

### Acceptance Evidence
- Command transcript: see `audit_logs/agent_coq_verification.log`.
- Verification command: `make -C coq clean && make -C coq` (executed after installing the Coq toolchain).

### Retrospective Notes
- Installing the distro Coq packages (`coq`, `coq_makefile`, etc.) is now a documented prerequisite before invoking the verification script.
- The curated project layout introduces no additional plugin dependencies or custom compiler flags.

## Milestone 2 – Formal VM Bridge (🚧 In Progress)

### Current Status
- The Coq `VMState`/`VMStep` scaffolding exists but only constrains `pc` and `μ`
  when relating to the kernel, leaving the partition graph, CSRs, and error
  latch unconstrained.
- No canonical encoding maps the rich VM state onto the kernel tape, so the
  bridge cannot yet explain graph edits, solver outputs, or CSR updates.
- Documentation that previously claimed completion has been rolled back to
  reflect the open work.
- Introduced `Kernel.VMEncoding` with concrete encode/decode functions for every
  VM structure (module regions, axiom sets, CSR bundles, and whole VM states),
  establishing the canonical bit-level layout that the kernel tape must
  implement. Primitive components have inversion lemmas; list encoders and
  composite structures (`ModuleState`, graph entries, `PartitionGraph`, `CSRState`,
  and full `VMState`) now enjoy end-to-end decode correctness proofs, so the
  canonical tape image round-trips into the original VM snapshot.
- Current container image still lacks the Coq toolchain (`coq`, `coqdep`,
  `coq_makefile`, `coqc`), so the new lemmas have not been type-checked locally;
  provisioning remains a prerequisite for executable evidence.

### Immediate Tasks
1. **Rebuild `states_related`:** Express the relation in terms of the encoding so
   every VM field is represented on the kernel tape. Demonstrate helper lemmas
   that decode tape fragments into VM structures.
2. **Strengthen VM step semantics:** Ensure `Kernel.VMStep` exposes enough
   structure for the forthcoming compilation proof (explicit graph mutations,
   CSR arithmetic, solver oracle hooks).
3. **Design kernel tape layout lemmas:** Connect the canonical encoding to the
   low-level tape machinery (`state`, tape cursors, and helper primitives) so the
   simulation proof can operate on the compiled instruction sequences.

### Blockers / Risks
- Encoding the partition graph compactly may require auxiliary invariants about
  module identifiers and axiom sets.
- The tape layout must accommodate dynamically sized components while remaining
  amenable to kernel instruction sequences.

### Evidence To Capture
- Updated Coq modules that type-check with the richer encoding helpers and
  export round-trip lemmas for composite VM structures.
- Progress log entries summarising intermediate invariants or test lemmas.

## Milestone 3 – Simulation Proof (🔒 Blocked on Milestone 2)

### Prerequisites
- Canonical tape encoding with accompanying correctness lemmas.
- A `compile_instruction` function that emits kernel instruction sequences which
  realise the VM semantics under the encoding.

### Planned Tasks (once unblocked)
1. **One-step simulation:** Prove each VM opcode is simulated by the compiled
   kernel sequence while preserving the encoding relation.
2. **Trace-level refinement:** Lift the one-step result to execution traces and
   restate the final theorem over the new encoding.
3. **Documentation update:** Once the theorem is proven without axioms, update
   README/fact-check materials with precise citations.

### Evidence To Capture
- `coq/kernel/SimulationProof.v` (or successor) containing the refined proofs.
- `audit_logs/agent_coq_verification.log` entries showing end-to-end builds that
  include the strengthened bridge.
