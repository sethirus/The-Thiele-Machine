# B3 uniform self-interpreter: contract review, 2026-09-14

This is a local source and theorem-contract review. It is not an independent reviewer report. It is not Gate E closure.

## Objects

The host is one fixed list, `VMSelfProgram.U`, of 122 instructions, run by the unbounded sibling semantics `run_vm_u` / `vm_apply_u`. Every host instruction has cost zero.

The guest is the VM's own instruction set restricted to a stated fragment (`VMSelfGuest.GInstr`): HALT, LOAD_IMM, XFER, ADD, SUB, MUL, AND, OR, SHL, SHR, JUMP and JNEZ. Register fields range over 0..3; register values, immediates and jump targets are arbitrary naturals; cost fields range over 0..255. A guest program is `g_program p = map g_denote p`, an actual `list vm_instruction`. `g_step_is_vm_apply_u` proves the abstract step `g_next` equals `vm_apply_u` on the guest `VMState`. `g_run_is_run_vm_u` proves the same for whole runs: the guest run is `run_vm_u` on `g_program p`.

## Encoding and boundary relation

E(p, x) is data only. Each guest instruction becomes one word (`g_word_N`): opcode in bits 0..3, dst 4..5, rs1 6..7, rs2 8..9, cost 10..17, immediate from bit 18. Words are packed at a per-program width; `g_width_fits` proves the computable width fits every word. The input x is the initial guest registers, guest pc and guest ledger.

`VMSelfCorrect.hb` is the boundary state. The host is at address 0. R0..R3 hold the guest registers, R9 holds status 0, R11 the guest ledger, R12 the guest pc, R13 the width and R14 the code. R4..R8, R10 and R15 are arbitrary scratch. Every non-register field and the host's own `vm_mu` are the fixed parameters `amb` and `hmu`. The relation therefore states the host frame too.

## Proved contracts

| Obligation | Result |
| --- | --- |
| Fixed host, data-only guest | `U` is one list. Guest program and input occur only in R0..R3 and R11..R14. |
| Positive finite step simulation | `h_step`: from any boundary, a well-formed guest instruction at the guest pc takes exactly `h_steps i g` host steps to a boundary representing `g_next`. `h_steps_pos` proves the count is positive. |
| Every guest result is produced | `self_interpreter_complete`: a terminal guest run is reached by an actual host run ending at `U_END` with status 1 and the terminal registers, ledger and pc. |
| Every host result is a guest result | `self_interpreter_sound`: the only execution premise is that the actual host run reaches `U_END`. The proof is strong induction on host fuel. A block of positive length that returns to a boundary cannot already have passed `U_END`, because termination is stable. `self_interpreter_correct` states both directions. |
| Halting | Guest termination is the VM's own condition: no instruction at pc. Opcode 0 is the fetch sentinel for it. `instr_halt` advances pc in the VM semantics, so it is an ordinary guest opcode. |
| Malformed words | `self_interpreter_malformed`: for arbitrary packed data, a fetched word with low bits 13..15 ends the host run with status 2 and the guest state unchanged. Canonical encodings never reach status 2, by soundness. |
| Traps | The fragment contains no trapping instruction and never writes the error flag. The guest error flag is the ambient flag and is preserved. |
| Divergence | `self_interpreter_divergence`: the guest never terminates iff no host run reaches `U_END`. `self_interpreter_divergence_live` adds that every finite host prefix then has an available instruction (`U_pc_bound`). Exhausted fuel is never called divergence. |
| Ledger and scratch separation | The guest ledger is the guest `vm_mu`, held in R11 and advanced by the decoded cost. The host `vm_mu` stays `hmu` in every boundary and terminal state. No equality between host and guest charge is assumed or claimed. |
| Applicability | `cm2_compile` maps every CM2 program into the fragment. `cm2_compile_complete` and `cm2_compile_sound` prove halting correspondence with equal counters, for both explicit HALT and falloff. `self_mm2_halting_iff` composes the pinned MM2 bridge, the compiler and the host: `MM2_HALTING problem` holds iff the actual run of `U` on `self_mm2_input` reaches `U_END`. `self_host_synthetic_undecidability` transfers the upstream synthetic undecidability unchanged. |

## Scope limits

The guest fragment has four guest registers and no memory, graph, morphism, certification or port instructions. Guest structural fields are the ambient fields; the fragment never changes them and the host never changes them. This is a self-interpreter for the stated fragment. It is not a simulation of the full ISA's structural operations. The result concerns the unbounded sibling semantics. It says nothing about the word64 physical model or the RTL.

## Evidence

`self_interpreter/validate.py` runs six module builds, the Makefile integration target, the contract probe `self_interpreter/Contracts.v` and dependency-enabled `coqchk` over all six modules, each under a 900 s time limit and a 1.8 GB resident-memory ceiling. All checks exit 0 within the limits; `validation.json` records commands, times, peak memory and source hashes. The probe reports every listed result closed under the global context. `coqchk` reports no axioms, no unsafe (co)fixpoints and no assumed positivity.

One defect was found and fixed during development. The phase-closing tactic kept `Nat.add` opaque, so a fuel expression `2 * k + 3` never became a numeral and evaluation grew past 2.5 GB. Fuel is normalized before evaluation; the file now builds in about 4 s.
