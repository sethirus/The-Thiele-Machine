# Verified Claims Ledger – Sovereign Witness Audit

## Methodology
- Provisioned the environment with `apt-get install -y coq yosys iverilog`
  followed by `pip install -e .`, recording the complete transcript in
  `audit_logs/agent_setup.log`.【F:audit_logs/agent_setup.log†L1-L748】
- Recompiled every kernel module and the VM bridge with explicit timing output
  (`coqc -q -time -Q kernel Kernel …`), producing
  `audit_logs/agent_coq_verification.log`.【F:audit_logs/agent_coq_verification.log†L1-L318】
- Regenerated Yosys synthesis logs and executed the dual-solver Verilog
  testbench, capturing results in
  `audit_logs/agent_hardware_verification.log`.【F:audit_logs/agent_hardware_verification.log†L780-L889】【F:audit_logs/agent_hardware_verification.log†L4238-L4275】
- Replayed the canonical software experiments (graph colouring, Shor on Thiele,
  six-act Bell thesis) to refresh every receipt and ledger, with output in
  `audit_logs/agent_software_reproduction.log`.【F:audit_logs/agent_software_reproduction.log†L1-L158】

## Verified Achievements

1. **Mechanical containment and VM simulation** – The kernel definitions share a
   common state and instruction vocabulary; the Thiele interpreter adds the
   μ-charging claim instruction.  `thiele_simulates_turing` and
   `turing_is_strictly_contained` witness strict containment, while
   `vm_is_instance_of_kernel` proves that error-free Python VM executions are
   simulated exactly by the kernel interpreter when instructions are compiled to
   `H_ClaimTapeIsZero`.【F:coq/kernel/Kernel.v†L4-L66】【F:coq/kernel/KernelTM.v†L6-L30】【F:coq/kernel/KernelThiele.v†L7-L26】【F:coq/kernel/Subsumption.v†L48-L118】【F:coq/kernel/ThieleCPUBridge.v†L8-L255】【F:audit_logs/agent_coq_verification.log†L279-L318】
2. **Autonomous hardware oracle** – `thiele_autonomous_solver.v` performs
   speculative colouring, μ-accounting, and chronological backtracking entirely
   in hardware.  The Verilog testbench confirms that both the scripted and
   autonomous controllers converge to the triadic cascade colouring while
   reporting identical μ-ledgers (1288 question bits, 934,848 Q16 information
   bits, μ-total 85,345,216 Q16).【F:hardware/synthesis_trap/thiele_autonomous_solver.v†L1-L200】【F:hardware/synthesis_trap/thiele_graph_solver_tb.v†L129-L179】【F:audit_logs/agent_hardware_verification.log†L887-L889】
3. **Unified μ-spec across software and hardware** – μ-spec v2.0 defines the
   question/information accounting and is implemented by the shared utilities and
   hardware solvers.  The sequential and autonomous controllers both enforce the
   same μ targets, and the software demos produce consistent μ-ledgers for graph
   colouring and Shor factorisation using the same specification.【F:spec/mu_spec_v2.md†L1-L95】【F:thielecpu/mu.py†L1-L85】【F:hardware/synthesis_trap/thiele_graph_solver_tb.v†L129-L179】【F:audit_logs/agent_software_reproduction.log†L1-L78】
4. **Deterministic experiment suite** – Re-running the demo scripts regenerates
   the cascade scaling table, the three-act Shor ledger, and the narrated Bell
   thesis run with fixed toolchain versions and seeded randomness, ensuring the
   published receipts remain reproducible.【F:audit_logs/agent_software_reproduction.log†L1-L158】

## Hardware Synthesis Summary

| Design | Wires | Cells | Notes |
| --- | --- | --- | --- |
| Classical brute-force solver | 179 wires / 228 cells | Baseline enumerator rebuilt via Yosys.【F:audit_logs/agent_hardware_verification.log†L790-L809】 |
| Thiele reasoning solver | 918 wires / 1,231 cells (plus embedded reasoning core) | Autonomous solver with integrated μ-ledger and parameterised `reasoning_core`.【F:audit_logs/agent_hardware_verification.log†L4238-L4260】 |

## Software Receipts
- **Graph colouring:** Triadic cascade Act III reports 1,302.3 μ-bits after the
  hardware-aligned question and information charges; larger cascades scale
  deterministically.【F:audit_logs/agent_software_reproduction.log†L1-L29】
- **Shor on Thiele:** Factorisation of 21 consumes exactly 7 μ-bits while
  replacing divisor trials with reasoning.【F:audit_logs/agent_software_reproduction.log†L33-L78】
- **Bell thesis run:** The six-act sovereign witness reproduces all SMT audits,
  receipts, and robustness proofs under the locked environment variables.【F:audit_logs/agent_software_reproduction.log†L80-L158】

## Conclusion
The repository now demonstrates a coherent, end-to-end thesis:

- The minimalist kernel strictly contains the classical interpreter and simulates
  the Python VM instruction stream.
- μ-spec v2.0 governs every software and hardware ledger.
- The autonomous hardware solver acts as an on-chip oracle whose outputs match
  the software demos bit-for-bit.

The authoritative summary of the system is this ledger together with the updated
`README.md`.  Historical documents remain for context and are marked as archival.
