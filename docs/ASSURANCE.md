# Assurance and scope

This repository separates checked mathematics, executable verification, trusted translation, and finite implementation tests. A result is described by the strongest category it actually satisfies; a generated file or a passing test is not treated as a proof merely because it is committed.

## Checked Coq results

The active Coq project is the source of truth for the formal corpus. The checked surface includes:

- the kernel instruction semantics, state invariants, cost accounting, and the selected computability and limitative results;
- the Kami CPU rules, reset facts, register schema, selected execution traces, fetch/update observations, normalization schedules, per-instruction retirement of every admitted instruction, and the explicitly stated hardware-boundary lemmas;
- the small machine in `minimal/EarnedCore.v` (earned commitments, checker soundness, no forging, the cost of a certified run) and its links into the kernel's records in `coq/kernel/foundation/EarnedCoreLinks.v`;
- the source-generation equality that identifies the canonical backend AST;
- the assumptions and dependency closure reported by the proof gates.

These theorems establish only the propositions stated by their types. In particular, the checked CPU results do not establish arbitrary-scheduler fairness, compiler semantic preservation, a refinement for counters wider than 32 bits, or a refinement for steps on which a CPU-only guard fires.

The unbounded self-interpreter, the Rice reduction and the guest recursion theorem are scoped to the stated four-register guest fragment and the unbounded sibling semantics. They do not claim interpretation of the full structural ISA, correctness of the word64 physical model, or correctness of the synthesized RTL. For the full VM, a recursion theorem asked for every map on programs is false (`vm_full_recursion_premise_refuted`).

## Executable verification

The repository runs source-level probes, dependency-enabled `coqchk`, native extraction checks, OCaml runner checks, RTL simulation, receipt consistency checks, and the Python test suite. These establish reproducibility and the behavior of the tested finite cases. They do not extrapolate finite traces to all states or all executions.

The probe sources used by the native proof reproduction live in [`tests/coq_probes/`](../tests/coq_probes/). Generated logs and compiled objects belong in the ignored reproduction directory or in a specifically named published evidence record; they are not source inputs.

## Translation and hardware boundaries

The extraction, OCaml printer, Bluespec compiler, and project text transformations are executed and replayed with recorded inputs and hashes. Their semantic preservation remains a trusted boundary unless a separate Coq theorem states otherwise. Byte identity proves provenance and repeatability, not circuit-level semantic equivalence.

RTL simulation covers the checked finite programs and encodings. Synthesis, place-and-route, timing, and bitstream results are claims only when the corresponding full workflow has produced evidence for the same source revision. No physical board has run the design.

## The CPU against the kernel

The CPU implements 47 of the 51 opcodes; the four Q<sub>1+AB</sub> forms of `CHSH_LASSERT` run in the kernel, the extracted runner, the Python VM and `kami_step`, and the CPU has no opcode for them. The CPU's data words and its ledger register are 32 bits wide, and the ledger wraps at 2^32; the kernel's words are 64 bits and its ledger is an unbounded natural number. Each refinement theorem assumes the counters it touches fit in 32 bits (`cpu_preconditions`). The CPU traps with a named error code on checks the kernel doesn't make: memory and control accesses outside the active module's range, a PDISCOVER whose declared cost is below its second operand, a ledger below the tensor total, and malformed rich-format fields. The refinement theorems cover only steps on which none of these fires. On partition capacity and range the two agree: PNEW, PSPLIT and PMERGE trap in both when the 64-slot module table has no free number or a range runs past data memory.

## Edge-by-edge implementation assurance

The implementation path is intentionally not summarized as one unconditional RTL bisimulation:

| Edge | Assurance | Boundary or domain |
| --- | --- | --- |
| One-file `ThieleMachineComplete.v` VM → kernel `vm_apply` | Tested | `tests/test_standalone_kernel_agreement.py` requires every definition reachable from the kernel's `vm_apply`, `instruction_cost`, `is_cert_setterb`, `VMState`, and `vm_instruction` to have identical text in the one-file copy, and the 51 instructions to agree. No Coq theorem relates the two state types. |
| Gallina `vm_apply` → Kami `kami_step` | Proved in Coq | `driven_step_wf` requires `WFDrivenPrecondition`; `driven_trace_commutes` requires `WFDrivenRun`. |
| Kami rules → actual priority-scheduler retirement | Proved for admitted `Retire`/`AdmittedRun` chains | `fsm_retirement_refinement` and `admitted_run_progress` cover reset-originating admitted chains; this is not an arbitrary-scheduler fairness theorem. |
| Kami model → extracted OCaml semantics | Coq-side theorem plus parity testing of the external binary | `ocaml_observable_nofi_and_monotone` concerns the extracted observable; the built binary and printer remain a tested boundary. |
| Kami → emitted Bluespec/Verilog | Trusted translation, checked by provenance and RTL tests | BSC/compiler and printer are named by `bsc_kami_compilation_trusted`; no generated-RTL semantic theorem is claimed here. |
| Verilog → synthesized netlist | Tool execution and synthesis-gate evidence | Valid only for the recorded RTL/tool/source identity. |
| RTL ↔ bitstream netlist ↔ VM, exact board top | Gate-level simulation, CI Full (`scripts/board_gls.py`) | The netlist the bitstream is built from (written back to Verilog and simulated with yosys's Xilinx cell models; block RAM through a pinned functional model checked against Xilinx UNISIM), the same board top as RTL, and the extracted VM run the same programs through the board pins: the program goes in over the serial line and the status report comes back on it. Gates are compared with RTL on the report bytes, the LEDs and every probed state field; RTL is compared with the VM on pc, μ, the error flag, the sixteen registers, the 128 data words, certification, the module table, the module counter, the morphism table, the witness counters and the logic accumulator. The RTL run also carries the formal property files as simulation checks and must reach every cover that is reachable from reset. Every program runs again with no reset press, the gates from their INIT values and the RTL from all zeros, and must end the same: the board wrapper holds the system in reset for its first sixteen CPU clock cycles after configuration. The programs are split over four shards, and a final job requires every shard and checks that all programs, comparisons and coverage targets are present. This is zero-delay simulation of the netlist before place and route, with behavioural models of the three Xilinx clock and buffer cells; it says nothing about timing or the analogue behaviour of the RAM. |
| Board wrapper and loader RTL → bitstream netlist | Formal equivalence conditional on the CPU interface, CI Full (`scripts/rtl_netlist_equiv.py`, `formal/loader-equivalence.txt`) | Board/loader equivalence, conditional on the CPU interface. For every finite execution from the specified power-on and reset state (a reset base case and an arbitrary inductive step, both mandatory), the board wrapper and loader in the bitstream netlist produce the same UART transmit line, the same four LEDs, the same CPU start and instruction-load enables, and the same connected instruction and address bus bits as their RTL, provided both sides receive the same seven CPU responses (pc, μ, the error, halted and certification flags, the error code, and instruction-load readiness). Equal responses are a condition of the result, not a proved property of the CPU. The CPU and its RAM are outside this comparison, and the clock cells are checked only for their types and divider ratio. |
| Extracted CPU and loader RTL → safety properties | SymbiYosys proof and cover tasks, CI Full (`formal/thiele.sby`, `formal/partition-induction.txt`) | Over every state reachable from reset. cpu_prove_pt: the module table stays within 64 slots, empty above the module counter, with every range inside the 128-word memory and the ranges pairwise disjoint; a partition trap goes to the trap vector and leaves the table unchanged; only PNEW, PSPLIT and PMERGE write it (321 mandatory induction obligations: reset, frame, bounds and trap, and every pair of slots; RAM reads are left arbitrary; the environment calls start only while the CPU is halted, which sys_prove proves of the loader). cpu_prove_ctrl (PDR): the error flag never clears except by reset and nothing executes after it is set, the morphism-table bounds hold, μ changes only when a charging rule fires, and halted clears only through start. sys_prove (k-induction with proved loader invariants; the depth bounds the induction search, not the executions covered): the loader starts the CPU only while it is halted, starts it at most once, loads nothing after the start, and sends one status report, only after a stop. cpu_cover and sys_cover: each property's trigger is reached by a real transition, within 16 cycles, from a state satisfying all the properties. μ never decreasing is not stated: the 32-bit register can wrap. |
| Netlist → routed design → bitstream | Tool execution for the same source revision | nextpnr-xilinx timing is a tool report, not vendor sign-off. Resource, timing and bitstream results do not transfer to a new source revision. |
| Python reference ↔ Coq/runner behavior | Finite parity/regression tests | Tests cover their recorded inputs; they are not a universal semantic proof. |

The 47/4 opcode inventory is an implementation inventory, not a proof that all 51 opcodes are present in the bitstream or that every finite hardware state represents an abstract VM state.

## Vocabulary used by the documents

- **Proved**: established by the checked Coq source and its required dependencies.
- **Tested**: exercised by an executable gate or finite regression suite.
- **Trusted**: relied upon at a translation or tool boundary without a corresponding semantic-preservation theorem in this repository.
- **Assumed**: supplied as a premise of a theorem or gate.
- **Outside scope**: deliberately not claimed by the model or gate.
Real limitations stay visible in the relevant theorem and document. The documentation does not describe the order in which a result was discovered, repaired, or deferred.
