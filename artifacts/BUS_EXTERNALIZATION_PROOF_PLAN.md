# Bus Externalization and Proof Plan (Coq-First, Extractable, Synthesizable)

Date: 2026-03-02
Scope: Move from native-method `mkModule1` interface to host-usable bus + external memory pipeline without hand-editing generated RTL.

## Ground Rules

- Source of truth is Coq/Kami (`coq/kami_hw/*.v`).
- Generated RTL (`thielecpu/hardware/rtl/thiele_cpu_kami.v`) is an artifact, not an edit target.
- Every interface change must pass: Coq compile, extraction, synthesis, and regression tests.
- No hardcoded behavior in wrappers that bypasses proven core semantics.

## Current State (Observed)

- `mkModule1` exposes native methods (`loadInstr`, `getPC`, `getMu`, etc.).
- Instruction and data memories are internal register banks (`imem`, `mem0..mem255`).
- No standard host protocol (AXI/APB/Wishbone) at generated top-level.

## Target End State

1. Host-visible control/status interface (AXI4-Lite or APB slave).
2. External memory path for instruction/data traffic (at least request/response memory interface).
3. Proven refinement: bus wrapper and memory wrapper preserve core VM semantics under abstraction.
4. Extraction pipeline emits synthesizable Verilog for the wrapped top module.

## Work Packages

### WP1: Stable Core/Wrapper Split

- Keep `ThieleCPUCore.v` as semantics core.
- Add a new wrapper module in Coq (example: `ThieleCPUBusTop.v`) that instantiates core and exposes bus-facing methods/signals.
- Wrapper owns protocol adaptation only; core owns ISA semantics and mu/error behavior.

Proof obligations:
- Wrapper step corresponds to zero or one core semantic step.
- Wrapper read/write CSR behavior equals projected core state fields.

### WP2: Memory Interface Externalization

- Introduce an abstract memory port interface in Coq/Kami:
  - instruction fetch request/response
  - data read request/response
  - data write request
- Replace direct internal large memory state in the *bus top* path with memory transactions.
- Keep internal-memory core path as reference configuration until proofs migrate.

Proof obligations:
- Memory adapter refinement: transaction-visible behavior equals previous internal-memory semantics for bounded traces.
- No mutation of VM state outside permitted memory/CSR transitions.

### WP3: Standard Host Bus Adapter

- Add protocol-specific adapter layer (AXI4-Lite first recommended for control plane).
- Map bus address space to control/status registers and doorbells:
  - program load window
  - run/step control
  - PC/mu/err/status counters
  - logic request/response mailbox

Proof obligations:
- Address decode correctness.
- Read-after-write consistency on mapped CSR space.
- Adapter does not forge core transitions (every state advance still flows through core step rule).

### WP4: Canonical Proof and Extraction Wiring

- Extend `CanonicalCPUProof.v` to use wrapped top as canonical hardware object.
- Update `KamiExtraction.v` extraction target from bare core to wrapped top module.
- Ensure build artifacts remain generated from Coq only.

Proof obligations:
- Existing abstraction theorems continue to hold (or are replaced with wrapper-aware versions).
- NoFI and mu monotonicity invariants preserved through wrapper layers.

### WP5: CI Gates (Must Pass)

- Coq: `make -C coq` and extraction targets.
- Extraction freshness checks.
- RTL synthesis gate.
- Bisim/cosim tests for VM vs RTL on wrapper path.
- New protocol tests:
  - bus read/write legality
  - program load + execution via bus
  - external memory fetch correctness

## Definition of Done (for this migration)

- Generated top-level RTL exposes standard protocol ports for host interaction.
- No direct manual edits in generated RTL required.
- Memory capacity not capped by internal reg-file-only architecture in deployed path.
- Coq proofs establish refinement from wrapped hardware interface back to VM semantics.
- Full extract -> compile -> synth pipeline green.

## Immediate Next Step

WP1 stage-1/2 is now in place:

- `coq/kami_hw/ThieleCPUBusTop.v` exists as the canonical wrapper seam.
- Canonical hardware proof root routes through this wrapper.
- A proof-visible MMIO register contract (address map + decode + R/W predicates) has been added in Coq while preserving behavior equivalence to the core path.
- A wrapper step model (`bus_step`) and core-preservation correspondence theorem are in place for stage-1/2 (`bus_step_preserves_abs_phase1`).

Next: implement protocol methods against this MMIO contract and prove wrapper-step/core-step correspondence for those methods.
