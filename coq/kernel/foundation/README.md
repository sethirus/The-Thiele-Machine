# kernel/foundation

Substrates and record-carrying machines, the record axis over any base, and
the links that make the small machine and the universal machine U instances of
these records.

## Substrates, recursion and undecidability

| File | Purpose |
|---|---|
| `Substrate.v` | The abstract computational substrate as a Coq typeclass: programs, runs, behavioral equivalence, representability, and a recursion theorem as a premise |
| `NatSubstrateInstance.v` | A substrate over `nat`-coded programs whose recursion theorem holds by construction (`nat_structural_shortcut_undecidable`, `nat_self_undecidable`) |
| `LRecursion.v` | The weak call-by-value lambda calculus L built from its reduction rules: Kleene's second recursion theorem (`second_recursion`), Rice's theorem (`L_rice`) and undecidable halting (`L_halting_undecidable`) |
| `MM2ComplementUndec.v` | The complement of two-counter halting is undecidable, composed from the vendored library's reductions (`MM2_HALTING_compl_undec`) |
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

## The small machine and U, as instances

| File | Purpose |
|---|---|
| `EarnedCoreLinks.v` | The small machine of `minimal/EarnedCore.v` as a certification system and a record-carrying machine: undecidable halting (`earned_core_halting_undecidable`), the floor, adequacy, honesty and the latch |
| `EarnedGenericLinks.v` | The generic and sorted-list machines and every Thiele-complete machine as certification systems (`thiele_complete_floor`, `complete_cs_window_blind`) |
| `UniversalThieleLinks.v` | The host of `minimal/UniversalThiele.v` and its guests as certification systems (`host_nfi`) |
| `UniversalBridge.v` | A run of an alternate Minsky machine program is a run of the host machine of `minimal/EarnedMulti.v` |
| `UniversalBlocks.v` | The building blocks of the universal interpreter, as host programs with host-level specifications |
| `UniversalLayout.v` | The fixed host program U, as one concrete list of host instructions |
| `UniversalPhases.v` | What U does for one guest instruction |
| `UniversalSim.v` | U simulates every guest program of the small machine, one guest step at a time |
| `UniversalRun.v` | Whole runs of U: simulation, halting, output, the earned flag, the exact ledger, and the Thiele completeness of the machine U runs on (`universal_thiele_complete`) |
| `UniversalInterpreterLinks.v` | The universal interpreter host as a certification system; its halting problem is undecidable (`interp_halting_undecidable`) |
| `CompilerCodes.v`, `CompilerChecker.v`, `CompilerInstrument.v`, `CompilerLifts.v`, `CompilerIcomp.v`, `CompilerRaBridge.v` | The compiler from mu-recursive algorithms to guest programs of the priced small machine: numbering of states and routines, the universal checker `cg_ueval`, instrumentation, lifts, and the bridge from recursive algorithms |
| `Presentation.v`, `CompilerGuest.v`, `CompilerGuestRun.v` | A presentation of a machine by four mu-recursive algorithms (`cg_presentation`), the guest program `cg_guest` compiled from it, and the runs of that guest |
| `UniversalPCodes.v`, `UniversalPBridge.v`, `UniversalPBlocks.v`, `UniversalPLayout.v`, `UniversalPPhases.v`, `UniversalPSim.v` | The priced counterpart of the universal interpreter: the fixed host program U_P on the machine of `minimal/EarnedMultiPriced.v`, built and verified block by block |
| `UniversalPRun.v` | Whole runs of U_P: simulation, halting, output, the earned flag, the exact ledger, and the Thiele completeness of the priced host (`pu_universal_thiele_complete`) |
| `PresentedUniversal.v` | One fixed machine U_P runs every computably presented Thiele machine, with the exact ledger up to a surcharge of at most 2 (`presented_universal`) |
| `PresentedDemo.v` | A computably presented demonstration machine run on U_P (`pu_demo_exact`) |
| `PricedHostLinks.v` | The priced interpreter host as a certification system; its halting problem is undecidable (`priced_interp_halting_undecidable`) |
| `RealizeNames.v`, `RealizePrograms.v`, `Realize.v`, `RealizePriced.v` | The machines of `minimal/` and the host programs U and U_P under extractable names, each proved equal to the original it stands for (the programs as literal lists, the pairing and instruction codes as copies, the prime stream as a computable search); these are the only definitions extracted to OCaml (`ocaml/RealizeExtract.v`) |
| `RealizeCompact.v` | Replacing the register storage of the host by a table at any step changes no register, version, fact, channel, latch, ledger or flag (`rlz_sched_sound`, `rlz_host_sched_sound`), so the extracted runs of U and U_P can be hundreds of millions of steps long |
| `SmallChshLinks.v` | The small machine with the CHSH property as a certification system: a certified run pays at least 3 and its committed tally obeys the Tsirelson bound (`small_chsh_certified_floor`) |

## Imports

The vendored undecidability library (`Undecidability`) and `minimal/`
(`Minimal`); `nfi/` for the certification-system record.
