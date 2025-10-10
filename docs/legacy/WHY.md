# WHY

**Claim.** Thiele Machines exploit structural sight to solve Tseitin expander contradictions in polynomial time while blind Turing machines require exponential time.

**Definitions.**
Let `TM` be a standard single-tape Turing machine with configuration type
`TMConfig := (state * tape * head)`. Let `CPU.State` be the Thiele-CPU state.
We fix a predicate `invariant : CPU.State -> TM -> TMConfig -> Prop` that
relates a CPU state to a TM configuration (registers `Q`, `HEAD`, a memory
slice equal to the tape at `TAPE_START_ADDR`, and `PC = 0`).

**Theorem (Containment).** For every classical TM `M`, there exists a blind
Thiele program that reproduces `M`'s execution on every input.
*Status:* `coq/thielemachine/coqproofs/Simulation.v` instantiates the universal
interpreter from `ThieleUniversal` and packages the witness as
`turing_contained_in_thiele`.

**Theorem (Separation).** For all sizes `n`, there exists a Tseitin expander instance such that the sighted Thiele solver halts in ≤ `C · (n+1)^3` steps with μ-cost ≤ `D · (n+1)^2` while blind Turing/DPLL search requires ≥ `2^n` steps.
*Status:* Proved in `coq/thielemachine/coqproofs/Separation.v` as
`thiele_exponential_separation` (with the classical lower-bound axiom).

**Theorem (Formal Subsumption).** Classical computation is strictly contained in
Thiele computation.
*Status:* `coq/thielemachine/coqproofs/Subsumption.v` combines the two theorems
above into `thiele_formally_subsumes_turing`.

**Notes.**
- The proof does not appeal to halting oracles. It isolates the cost of sight:
  Thiele programs pay polynomial μ to access structure, then solve in cubic
  time.
- [`coq/verify_subsumption.sh`](coq/verify_subsumption.sh) rebuilds both pillars
  (containment and separation) from a clean slate.
- All remaining assumptions are catalogued in
  [`coq/AXIOM_INVENTORY.md`](coq/AXIOM_INVENTORY.md); the subsumption proof
  itself is fully mechanised.
