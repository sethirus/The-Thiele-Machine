# Specialization repair target

The original `specialized_program_correct` starts `mm2_guest_program p` at
PC 0, where that encoding places `CM2_Halt`. The theorem is true but does not
specialize actual MM2 execution, whose entry is PC 1. This is an applicability
defect in the earlier B4 evidence, not a defect in the MM2 halting bridge or
output-zero undecidability theorem.

The corrected transformer will increment counter 0 `S a` times, then execute
a successful decrement-and-jump to the relocated guest's PC 1, restoring
counter 0 to `a` and preserving counter 1. The guest, including its PC-0 halt
sentinel, is relocated by `a+2`; all absolute targets are shifted accordingly.

Required result: for every program p, fixed input a, remaining input b, and
final guest configuration f, the original encoded guest started at (1,a,b)
halts at f iff the specialized program started at (0,0,b) halts at
`shift_config (a+2) f`. Additionally, every specialized terminal result must
be the shifted form of an original terminal result. Transfer both directions
to `interpreter_raw_produces` through the existing checked raw-host theorem.
No runtime host-language evaluator or assumed simulation is permitted.

This repair does not itself supply a general fixed-point theorem or close B4.

## Implemented and checked

The corrected transformer and all stated forward/converse contracts are in
`VMUnboundedCM2Specialization.v`. `specialization_repair/validation.json`
records source hashes, exact commands, raw exits, and durations. Compilation,
build integration, contract probes and dependency-enabled `coqchk` pass.
All three probed top-level terminal/host contracts are closed under the global
context; the checker reports no axioms or unsafe proof modes. Regressions
prove guest increment execution, jumps to zero and out-of-range addresses,
and zero-counter decrement fallthrough, universally in their remaining inputs.
The native reproduction runner includes this library and its contract probe.

Recovery archive before implementation:
`/tmp/thiele-before-specialization-repair-20260914.tar.gz`.
The old PC-0 claim is explicitly superseded, not treated as evidence of the
corrected PC-1 behavior. The separate output-zero undecidability development
was not changed by this repair.
