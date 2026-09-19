# Existing-ISA interpreter investigation

Scope: unbounded self-interpreter and physical refinement; existing-ISA capabilities and obstructions.

## Established input obstruction

`VMEncodedInputAccess.v` proves that replacing `vm_logic_acc` commutes with every opcode and every finite-fuel run. The current `vm_encode_concrete` puts all program information in that field. Its external Coq decoder is a valid round trip, but does not provide executable input access.

`no_logic_acc_encoded_interpreter` rules out a fixed VM interpreter using this encoding that reproduces every program's final certification observations through an output observation invariant under replacement of the retained input accumulator. This includes conventional register/memory outputs. It does not rule out different encodings or an external decoder that computes an answer from the original program code.

## Existing unbounded access

Ordinary memory is indexed modulo 128 and register writes are truncated to 64 bits. This alone does not prove that the abstract VM has only finite computational state: witness counters and parts of the graph are unbounded.

`VMUnboundedCounterAccess.v` constructs these setting buckets:

| Setting | same | different |
| --- | --- | --- |
| 00 | u + 1 | v + 1 |
| 01 | 1 | 1 |
| 10 | 1 | 0 |
| 11 | 1 | 1 |

The actual base CHSH checker accepts exactly when `u = v`. Matching and differing trials at setting 00 increment the respective component. Their difference is therefore a signed counter with an executable equality test. All four bucket totals are positive; this does not exploit a missing-bucket arithmetic error.

The formal proof applies to the abstract natural counters. Physical counters require their own range assumptions. A failed CHSH guard latches error and branches to the trap PC; an interpreter using this primitive must explicitly account for that behavior. The `run_vm` evaluator does not terminate merely because the error flag is set.

## Executable counter-control milestone

`VMCounterBranch.v` now proves actual one-step increment/decrement, two-step equality branching, and repeated execution after a failed guard under the unchanged runner. The fixed 3841-instruction drain program uses a jump at the existing trap address 3840. For v<=u it halts in `4*(u-v)+2` steps with represented counter zero and charge `u-v+1`; it retains the error/CSR effects of failed guards. This program is for the abstract instruction-list runner, not the 128-word RTL instruction memory.

The full state equations and preservation lemmas are in `counter_branch_report.txt`. This discharges the reusable branch/drain dependency, not the sufficient-storage or interpreter milestones. The single global trap trampoline remains a composition constraint for multiple branch sites; a future dispatcher must be implemented internally.

## Two-counter candidate

`VMTwoCounterAccess.v` extends the layout with 01=(a+1,b+1). Actual trial macros update either difference independently, and the 1AB guard branches on a=b when u=v. Every extended guard rejects if u<>v for this layout, for any gamma parameters. The integrated 11-result probe and compiled-library check passed at the preceding checkpoint. `TWO_COUNTER_FINDINGS.md` records the exact scope.

An independent second test for arbitrary first value, or an internal save/restore protocol, is still missing. Draining the first destroys its represented value; the one-counter drain theorem also fixes the other buckets and is not already a general two-counter drain theorem. No architecture decision or whole-ISA impossibility follows from this candidate's limitation.

## Alternative layout and selector protocol investigation

`VMAlternativeCounterAccess.v` proves ten results for a diagonal layout. Its base guard accepts all counter values; the combined 1AB guard is a symmetric sum-of-squares condition. The two differences have independent trial updates, but this guard cannot distinguish which one is zero. The general guard characterization and concrete colliding zero-test examples are in `alternative_counter_report.txt`.

A rotated two-counter encoding has algebraic zero selectors for either coordinate and fixed-size arithmetic update blocks. Switching between the selectors requires a number of trials proportional to an unbounded hidden helper scale. No VM-controlled loop implementing that switch while preserving both logical counters has been found. `ALTERNATIVE_COUNTER_PROTOCOL.md` gives the formulas, exact external arithmetic checks, and this precise missing obligation. Those checks do not execute the VM or establish a universal simulation.

B2c therefore remains an implementation/research dependency. These candidate limitations neither authorize an ISA change nor prove that every unchanged-ISA encoding is impossible. The existing logic-accumulator impossibility theorem remains restricted to that encoding.

## Required next work

1. Establish enough independently controllable storage and tests to implement a general interpreter. One signed counter is insufficient evidence. Audit the other witness guards and graph access before asserting universality or impossibility.
2. Specify the executable input encoding, output decoding, simulation relation, and treatment of errors, accounting, and interpreter overhead.
3. Construct an actual instruction-list interpreter and prove simulation for unbounded halting. An external Gallina evaluator alone does not meet this target.
4. Define the corresponding unbounded program predicate and prove the needed representability/recurrence instance. Do not reuse bounded full-state outcome equality as though it were unbounded observational equivalence.

No universal interpreter, recurrence instance, or physical retirement theorem is claimed by these preliminary access results.

## Graph input audit checkpoint

`GRAPH_INPUT_ACCESS_AUDIT.md` records a newly checked sequential input route. The current `well_formed_graph` does not require unique module IDs. An initial list of duplicate module-ID-zero entries can encode tokens: a literal `TENSOR_GET` reads the first token, and `PSPLIT 0` removes that entry, exposing the next after newly allocated high-ID entries. Six executable Coq examples are preserved in `graph_input_stream_probe.v`. This initialization need not be reachable from the empty graph to be considered as an input encoding. It supplies neither writable unbounded storage nor a universal interpreter. The next exact obligation is a uniform `run_vm` reader macro, followed by sufficient reusable storage/control.
