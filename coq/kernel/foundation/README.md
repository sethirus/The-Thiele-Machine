# kernel/foundation

The definition over any order and the member predicate, substrates and
record-carrying machines, the record axis over any base, and the
counterexamples that show which premises do work.

## Substrates, recursion and undecidability

| File | Purpose |
|---|---|
| `Substrate.v` | The abstract computational substrate as a Coq typeclass: programs, runs, behavioral equivalence, representability, and a recursion theorem as a premise |
| `NatSubstrateInstance.v` | A substrate over `nat`-coded programs whose recursion theorem holds by construction (`nat_structural_shortcut_undecidable`, `nat_self_undecidable`) |
| `LRecursion.v` | The weak call-by-value lambda calculus L built from its reduction rules: Kleene's second recursion theorem (`second_recursion`), Rice's theorem (`L_rice`) and undecidable halting (`L_halting_undecidable`) |
| `Kernel.v`, `KernelTM.v` | A toy Turing-machine-shaped machine with a cost field, and its bounded executor (`tm_is_turing_complete`) |
| `ProperSubsumption.v` | Every Turing program of the toy machine runs as a Thiele program, and the toy Thiele step strictly extends it (`thiele_simulates_turing`, `thiele_strictly_extends_turing`) |

## Record-carrying machines and the record axis

| File | Purpose |
|---|---|
| `StructuralCore.v` | Record-carrying machines, adequacy, and core equivalence, stated over an arbitrary deterministic machine |
| `StructuralCoreCover.v` | The strong form: computational covers and record observations |
| `StructuralCoreAnyBase.v` | The record axis over any base: honest extensions of a deterministic, record-free machine |
| `StructuralRecordAxis.v` | The record axis over any base is a latch (`record_axis_is_latch_holds`, `record_pair_is_two_latches_holds`), and both premises do work (`toggle_not_latch`, `clock_record_not_driven`) |
| `RecordAxisDiscrimination.v` | Every base carries the axis (`latch_core_honest`); a reversible base with unbounded memory carries it reversibly (`history_latch_honest`); with finite memory a permanent write is not injective (`finite_reversible_cannot_write`) |
| `GrowingRecordCore.v`, `GrowingRecord.v` | Monotone multi-valued records decompose into threshold latches, and one latch does not suffice (`growing_record_decomposes_holds`, `one_latch_refuted`) |
| `ProbabilisticRecordCore.v`, `ProbabilisticRecord.v` | Finite-weight branching records: a deterministic latch does not handle branching, and the schedule does not determine the weights |
| `CrossBaseGranularityCore.v`, `CrossBaseGranularityTransCore.v`, `CrossBaseGranularity.v` | Weak base equivalence permitting stuttering, its equivalence laws, and its outcomes |
| `CrossBaseGranularityL.v`, `CrossBaseGranularityRAM.v` | L and the Cook and Reckhow RAM as bases; the record axis is a latch over each |

## Further files, by family

| Files | Purpose |
|---|---|
| `AxThiele.v` | The member predicate over any order: the toll, permanence and a run that makes a distinction (`ax_thiele`); a flat reading obeys the toll and is not a member (`flat_obeys_toll`, `flat_is_not_thiele`); the latch as the smallest member (`latch_is_thiele`, `latch_merges`, `no_one_state_member`); the history lift that makes every machine with a Boolean equality test on its states and a run that ends on a state other than its start the shadow of a member (`history_lift_is_thiele`, `history_lift_shadow`) |
| `Ax*.v` | The record over any order of values: the axis, its toll and floor, chains of thresholds, the shadow and its fibres, the price of collapsing a fibre, latches per point, and the entropy a priced move can remove (`ax_floor_iff_a2`, `chain_bits_exact`, `ax_fibre_collapse_exit`) |
| `Nec*.v` | Each premise is needed: for every headline result, a built counterexample with one premise dropped |
| `LatchConst.v` | The latch theorem admits a constant event, an honest record that tells nothing apart (`latch_constant_up`, `latch_distinguishes`) |
| `FiniteSums.v` | Sums over finite lists of indices and the Cauchy-Schwarz inequality |
| `StructuralClockSync.v` | What the latch theorem uses, and what separates a clock from a latch |

## Imports

`minimal/` (`Minimal`), and `nfi/` for the certification-system record.
