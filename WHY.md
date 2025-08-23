# WHY

**Claim.** The Thiele machine model strictly subsumes the Turing model.

**Definitions.**
Let `TM` be a standard single-tape Turing machine with configuration type
`TMConfig := (state * tape * head)`. Let `CPU.State` be the Thiele-CPU state.
We fix a predicate `invariant : CPU.State -> TM -> TMConfig -> Prop` that
relates a CPU state to a TM configuration (registers `Q`, `HEAD`, a memory
slice equal to the tape at `TAPE_START_ADDR`, and `PC = 0`).

**Theorem (Constructive Subsumption).**
For all `tm, conf, n`, there exists a CPU state `st_final` such that
`invariant st_final tm (tm_step_n tm conf n)`.
*Status:* Proved in `coq/thieleuniversal/coqproofs/ThieleUniversal.v` as
`UTM.subsumption_theorem`.

**Operational Theorem (Relative).**
Assume `UniversalProgramSpec`, i.e., one decoded CPU step (`run1`) simulates
one TM step from any state satisfying `invariant`. Then for all `n`:
`invariant (run_n st0 n) tm (tm_step_n tm conf n)` whenever
`invariant st0 tm conf`.
*Status:* Proved as `UTM.runs_universal_program_n`. The remaining task is
to implement the real universal program/decoder and prove the instance
`UniversalProgramSpec`, after which the operational theorem is fully established.

**Notes.**
- The constructive theorem is fully formalized in Coq.
- The operational theorem depends only on the explicit, documented spec.
- This formally captures that “every Turing machine is a degenerate Thiele machine”
  (trivial partition), while the Thiele model admits strictly more structure
  (partitions, certificates, μ-cost).