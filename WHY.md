# WHY

**Claim.** The Thiele machine model strictly subsumes the Turing model.

**Definitions.**
Let `TM` be a standard single-tape Turing machine with configuration type
`TMConfig := (state * tape * head)`. Let `CPU.State` be the Thiele-CPU state.
We fix a predicate `invariant : CPU.State -> TM -> TMConfig -> Prop` that
relates a CPU state to a TM configuration (registers `Q`, `HEAD`, a memory
slice equal to the tape at `TAPE_START_ADDR`, and `PC = 0`).

**Theorem (Subsumption).** For all `tm` and `conf`, one step of a Thiele Machine
matches one step of the corresponding Turing Machine.
*Status:* Proved in `coq/thielemachine/coqproofs/Subsumption.v` as
`thiele_machine_subsumes_turing_machine`.

**Notes.**
- This formally captures that “every Turing machine is a degenerate Thiele machine”.
  (trivial partition), while the Thiele model admits strictly more structure
  (partitions, certificates, μ-cost).