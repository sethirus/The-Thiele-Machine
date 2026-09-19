# Dispatch fetch and tensor/CSR checkpoint

This checkpoint advances C2 step 2. It does not close C1/C2 or E.

`ThieleCPUCore.dispatch_decoded` is a mechanical extraction of the step rule's
suffix after instruction fetch. `FetchFactoring.v` retains the complete old step
action and proves exact equality with the actual new rule by `reflexivity`.
Neither its arithmetic nor its write/guard order changed.

`ReadFreeObservation` proves that observation and evaluation of an action with
no register reads are independent of the old map. `DecodedReadFree` proves this
property for the actual suffix. `DispatchFetch` then proves that arbitrary
instruction memories agreeing at the PC's seven-bit fetch address yield identical
write observations, identical complete evaluator results, and equivalent actual
`SemAction` executions. These are arbitrary-state facts, not reset examples.

`HWBoundaryReads` checks all 138 typed field reads. `BoundaryDecoded` uses those
facts to reduce actual dispatch observations to `hwb_decoded` without normalizing
the entire old map. Its Bianchi predicate uses the actual wrapping 32-bit tensor
sum; it is not a natural-number conservation theorem.

`TensorDispatch` proves the full module-tensor write for TENSOR_SET and the full
register-file write for TENSOR_GET. The canonical ISA-v2 format-0 word has arbitrary
24 low operand/cost bits and zero unused extension lanes. The boundary and imem
are arbitrary. Both Bianchi branches are included: the affected storage is
preserved on rejection. Actual-write corollaries require successful
`eval_dispatch`; the existing evaluator/`SemAction` equivalence justifies that
premise. CSR status and heap base are preserved by every successful dispatch,
including other opcodes and fault branches.

These theorems do not establish dispatch enabledness, complete snapshot equality
to `kami_step`, tensor/mu charging correspondence, heap instruction correctness,
reachable invariants, FSM progress or retirement refinement. The hardware's
seven-bit address truncation is retained; the new heap tests include aliasing
cases as implementation behavior, not as nonaliasing C1 admission examples.

The nine new RTL tests cover canonical tensor/CHSH encoding, all 16 tensor modules,
cell overwrite/isolation, nonzero heap base, word/address wrap, CSR preservation,
and effective-address locality rejection. The locality test exposed a harness
assertion that wrongly disallowed error-induced halts; the failing log is retained.
CSR test initialization deposits arbitrary boundary values; it adds no hardware
host-loading method. The harness now reports real tensor and CSR registers.

The canonical assembler now accepts CHSH_LASSERT and the harness delegates tensor
operand packing to it. The generated Python software VM adapter and 51-opcode
tables were checked against regeneration; they already contained the software
storage support. No separate authoritative Python hardware step model exists.

Run `python3 artifacts/review_revision/c2_dispatch/validate.py` for guarded,
single-job full integration, assumptions probes, the exact-factoring probe and
dependency-enabled `coqchk`. Results and limits are in `validation.json`. The
checker uses no dependency-bypass flags. The named new observation/execution
results inherit `functional_extensionality_dep` and `Eq_rect_eq.eq_rect_eq`
through Kami semantics; no new axioms were declared. Individual assumptions
are printed in `contracts.log`. The exact syntactic factoring theorem is closed
under the global context. A broader imported-library axiom census is not an
individual theorem's dependency report.

Fresh extraction used the project make target `kami_hw/KamiExtraction.vo`, then
`scripts/kami_extract.sh --skip-coq` with BSC 2024.07 and SKIP_YOSYS=1. The skip flag
reused the newly extracted Target.ml, not historical OCaml. Exact downstream
command, exit, elapsed time and peak RSS are in `rtl-regeneration.json`. No new
synthesis or physical performance measurement is claimed. C3's manifests/replay
and canonical pipeline tests are recorded separately in `../c3_audit/`.

Final validation passed: full integration (390.777 s, peak 1137 MB), named
contracts (18.176 s), exact-factoring probe (86.272 s), and dependency-enabled
coqchk (471.204 s, peak 346 MB), all exit 0. No type-in-type, unsafe fixpoints
or assumed positivity were reported. The broader imported-library census lists
existing `CommonTactics.cheat` alongside equality/extensionality; none of the
named results in `contracts.log` lists `cheat` as an assumption. Final RTL
regressions: 154 passed; C3 canonical pipeline tests: 18 passed; reproduction
runner tests: 5 passed. A full make dry run schedules no Coq compilation.

The latest instruction stops at this checkpoint for handoff. No job remains
running. Continue with the outstanding C2 step-2 full-observation/`kami_step`
proofs, then the remaining FSM and E obligations in STATUS.md. No fresh
source-only final reproduction, immutable candidate, commit or release is claimed.
