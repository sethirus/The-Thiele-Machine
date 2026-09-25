# Technical Disclosure: The Thiele Machine

**Author:** Devon Thiele  
**First public disclosure:** August 15, 2025 (repository creation; development began January 2025)  
**Current date:** September 2026 (v3.2.2)\
**Repository:** https://github.com/sethirus/The-Thiele-Machine  
**License:** Apache 2.0 (software), CC-BY-SA-4.0 (monograph/documentation)  
**Purpose of this document:** Defensive publication. This document records the concepts, source dates, and public repository locations intended to establish a dated public record. Whether a particular disclosure qualifies as prior art under 35 U.S.C. § 102 or Article 54 EPC is a legal determination; this document is not a legal opinion. It is submitted for indexing to IP.com and similar prior-art databases.

---

## Summary

I built the Thiele Machine to put a structural argument about computation into a form people can inspect, run, and challenge. Certification is one worked witness. The subject is larger: what a computation preserves, what it establishes, and the laws governing the cost of those events. The concepts below are the concrete work I have done to make that argument answerable.

The established results include a universal accounting theorem for systems satisfying A2, pricing adequacy relative to certification-flip count, ledger uniqueness under a fixed schedule, and impossibility results for specified observations that lose relevant information. A conventional encoding can retain those distinctions; the results do not prove that all Turing-equivalent systems lack them.

Generic `CERTIFY` pays to set a flag without checking a proposition. Semantic truth requires a sound checker. Trace-fold initiality concerns evaluation of instruction lists; it does not supply a certification-preserving VM-state map into every A2 system. Hardware bridges carry representation preconditions and compiler trust boundaries.

The foundational and physical interpretations remain research questions. The full-ISA F1 physical premise pair is inconsistent with zero-cost jumps; it provides no physical instance.

The entries below mix four kinds of statement: a formal result, a description of the current VM, an engineering disclosure, and a possible variant. The word “variant” records a pattern that could be built under the listed conditions; it does not say that this repository implements every named target, proves a deployed implementation, or establishes patent validity.

---

## Concept 1: The µ-Ledger (Structural Cost Register)

**What it is.** Every Thiele Machine state carries a field `vm_mu : nat`, a natural number that starts at 0 and is monotonically non-decreasing. Every instruction carries an explicit `mu_delta` parameter encoding its cost. The machine's step function adds exactly `instruction_cost(i)` to `vm_mu` on every step, including error cases. No instruction anywhere decreases `vm_mu`.

**The cost schedule.** Instructions fall into two classes:
- *Ordinary compute* (ADD, LOAD, STORE, JUMP, PNEW, MORPH, etc.): cost = `mu_delta`, which may be 0.
- *Certification and revelation* (CERTIFY, MORPH_ASSERT, LASSERT, LJOIN, EMIT, REVEAL, READ_PORT, and the five CHSH_LASSERT-family opcodes): cost = `S(mu_delta)` = `mu_delta + 1` at minimum. Even with `mu_delta = 0`, these cost at least 1.

**EMIT, REVEAL, READ_PORT** additionally charge proportional to information content: `|payload|_bits + S(mu_delta)`.

**LASSERT** charges `flen × 8 + S(mu_delta)` where `flen` is declared in the instruction. Success requires it to match the encoded count in the formula’s in-memory header; a mismatch traps and still pays the declared charge.

**Why the positive floor is one.** One is the least positive natural number. The VM chooses an additive floor `S(δ)` for these instructions. A2 itself permits larger charges. The substitution results identify exact unit pricing relative to certification-flip count, not the entire instruction schedule. Formula-cost minimality in `MuCostDerivation.v` is relative to its stated formula-length constraints.

**Several event floors.** For a finite family of events, the least natural-valued schedule meeting every unit floor charges one if any event occurs and zero otherwise. Several events can share one charge. Independent state coordinates do not by themselves imply additive cost. `ObservationPolicy.v`, theorem `joint_floor_is_least`.

**Hardware.** In the synthesized RTL (`thielecpu/hardware/rtl/thiele_cpu_kami.v`), `vm_mu` is a 32-bit register incremented inline within the step rule. The cost field occupies bits [7:0] of the 32-bit instruction word.

**Variants disclosed.** The µ-ledger pattern can be instantiated on an instruction-set architecture where: (a) every instruction carries an explicit cost field, (b) a dedicated monotone accumulator tracks total cost, and (c) a mandatory-floor class of instructions is precluded from zero cost. x86, ARM, RISC-V, MIPS, GPU PTX, and FPGA soft-cores are possible target families, not implementations or proofs supplied by this repository. The formal result here uses natural-number costs and the schedule stated above; other cost domains require their own definitions and proofs.

---

## Concept 2: No Free Insight (Cost-Floor Law)

**Statement.** For any trace of the Thiele Machine that starts with neither certification channel active and ends with at least one active, the total `vm_mu` increase is at least 1. A separate quantitative result requires the trace-realized decision-tree witnesses and posterior-representative conditions described in Concept 10. Under those conditions:

Δµ ≥ ⌈log₂|Ω|⌉ − ⌈log₂|Ω'|⌉

**Proof structure.** The two concrete certification channels are:
1. `csr_cert_addr`: set to the ASCII checksum of a property string when MORPH_ASSERT succeeds on a non-empty property.
2. `vm_certified`: set to true by the CERTIFY opcode.

Both CERTIFY and MORPH_ASSERT are in the mandatory-floor class (cost ≥ 1). No other instruction touches either channel. This is verified by case analysis over all 51 opcodes. Therefore any trace that activates either channel paid at least 1. `AbstractNoFI.v`, `NoFreeInsight.v`.

**Abstract version.** The theorem holds for any abstract certification system satisfying: (a) a certification predicate, (b) a step function, (c) a cost function where every single-step uncertified→certified transition costs ≥ 1. The Thiele Machine is an instance. `coq/kernel/nfi/AbstractNoFI.v`, theorem `no_free_certification`. The substrate-agnostic version is `universal_nfi_any_substrate` in `coq/kernel/nfi/UniversalCertificationCost.v`.

**Variants disclosed.** No Free Insight can be instantiated in a computational system, hardware or software, that (a) distinguishes certified from uncertified structural claims in its state, and (b) charges a positive cost for the certification transition. Formal-verification co-processors, hardware security modules, trusted execution environments, and certificate-validated systems are possible application families; this repository does not prove their deployed behavior.

---

## Concept 3: µ-Initiality (Uniqueness of the Cost Measure)

**Statement.** Let M be any function on machine states satisfying: (a) M(init_state) = 0, and (b) M(vm_apply s i) = M(s) + instruction_cost(i) for all reachable states. Then M = vm_mu on all reachable states. This is uniqueness relative to the stated schedule and initial value, not uniqueness of every possible cost schedule. `MuInitiality.v`.

**What this means.** Given the cost assignment (S(δ) for cert-setters, |payload|+S(δ) for EMIT, etc.), µ is not just one valid accounting. It is the only valid accounting. Any system that assigns costs the same way must produce the same totals.

**Trace evaluation and state maps.** A target evaluation assigns a unique value to each reachable VM state exactly when traces with the same VM outcome have the same target outcome. Given representative traces, this condition together with certification agreement constructs a basepoint-preserving simulation whose step and certification laws hold on reachable states. The certification quotient supplies an instance; a target retaining full instruction history satisfies A2 and certification agreement but can fail descent. `TraceStateDescent.v`.

---

## Concept 4: The µ-Hierarchy Theorem

**Statement.** Pick any integer k ≥ 1: there is a certified trace costing exactly k. A trace whose certification level requires a charge of at least k cannot cost less than k. The ledger conservation theorem supplies that floor. This is a hierarchy of certification costs under the stated level definition; it does not place a decision problem in a new complexity class. `coq/kernel/mu_calculus/MuHierarchyTheorem.v`, theorem `mu_hierarchy_theorem`.

---

## Concept 5: The CERTIFY Opcode

**What it is.** A dedicated, unguarded instruction that sets `vm_certified = true` in machine state. It checks no proposition or certificate. Cost: `S(mu_delta) = mu_delta + 1 ≥ 1`. Once set, `vm_certified` is never cleared by any subsequent instruction. The CERTIFY opcode is the only instruction that sets this field.

**Hardware.** In the RTL, `certified` is a 1-bit register. The CERTIFY case in the step rule sets it unconditionally. The cost is charged to the `mu` register in the same cycle.

**Variants disclosed.** Any ISA extension, co-processor instruction, microcode operation, or hardware primitive that: (a) sets a persistent certification bit in processor state, (b) charges a mandatory positive cost to a monotone accumulator, and (c) is the sole instruction capable of setting that bit is a variant of this concept.

---

## Concept 6: The LASSERT Opcode (Logic Assertion with Dual Witness)

**What it is.** LASSERT reads a logical formula from memory (at the address in register `freg`), reads a certificate block from memory (at the address in register `creg`), and validates both using an on-chip Logic Engine FSM. The current VM implements the SAT path with a model and countermodel; the UNSAT path always fails. Parameters: `freg` (formula address register), `creg` (certificate address register), `kind` (boolean: SAT or UNSAT path), `flen` (declared formula-unit count), `cost` (mu_delta).

**Dual-witness requirement.** In the SAT path (`kind = true`): the certificate block must contain both a satisfying assignment and a falsifying assignment. LASSERT succeeds only if the declared `flen` matches the formula's in-memory header count, the first witness satisfies the formula, and the second witness falsifies it. Under checker soundness this proves that the encoded formula is satisfiable and not a tautology. It does not by itself prove that the falsifying assignment is a state in the current feasible set or that the formula expresses a sound decomposition; those are separate representation premises.

**Anti-gaming.** If the declared `flen` in the instruction encoding does not match the actual formula length read from the formula's in-memory header, the machine traps: PC jumps to `LASSERT_TRAP_PC = 0xF00`, `vm_err` is set, and the check does not succeed. The µ cost is still charged even on trap. This prevents declaring a small `flen` for a large formula. `StateSpaceCounting.v`, theorems `lassert_honest_cost` and `lassert_honest_mu_cost`.

**On-chip Logic Engine.** Formula verification is performed entirely on-chip by a finite-state machine (phases: idle, header, SAT scan, UNSAT scan, UNSAT conflict check) without calling any external solver. The FSM reads formula words and certificate bytes from `vm_mem` via register-indexed addressing.

**Variants disclosed.** Any hardware instruction or co-processor command that: (a) reads a logical formula from memory, (b) verifies a satisfying and a falsifying witness in hardware without external solver calls, (c) charges cost proportional to formula length to a monotone accumulator, and (d) traps on length-declaration mismatch is a variant of this concept.

---

## Concept 7: The Partition Graph as First-Class Machine State

**What it is.** The Thiele Machine state includes a field `vm_graph` that is a partition graph: a record of named modules (memory regions with attached axiom sets) and typed morphisms between them. This is not a data structure stored in memory. It is a separate top-level field of the machine state, alongside registers, memory, and program counter.

**Operations.** The ISA includes dedicated opcodes for partition graph manipulation: PNEW (allocate module), PSPLIT (split module into two), PMERGE (merge two modules), PDISCOVER (query structure), MORPH (create morphism), COMPOSE (compose morphisms), MORPH_ID (identity morphism), MORPH_DELETE (remove morphism), MORPH_ASSERT (check morphism existence and store a property-string checksum; the certificate string is not validated), MORPH_TENSOR (tensor morphisms), MORPH_GET (query morphism).

**Projection separation.** The cited constructions give states with equal selected observations and different structural data. No function of that observation recovers the omitted datum on all states in the theorem’s domain. This does not rule out a different representation that retains the graph. `NecessityOfMuLedger.v`, `PartitionSeparation.v`.

**Variants disclosed.** Any processor architecture, ISA extension, or hardware accelerator that maintains partition structure (module decomposition, morphism map, or typed relational structure between memory regions) as a distinct top-level field of architectural state, separate from the flat memory and register file is a variant of this concept.

---

## Concept 8: The CHSH_TRIAL Instruction and Witness Counters

**What it is.** A dedicated instruction that increments one of eight counters in `vm_witness` based on measurement settings (a,b) ∈ {(0,0),(0,1),(1,0),(1,1)} and outcome (same/different). The eight counters are: `wc_same_00`, `wc_diff_00`, `wc_same_01`, `wc_diff_01`, `wc_same_10`, `wc_diff_10`, `wc_same_11`, `wc_diff_11`. The CHSH score S = E₀₀ + E₀₁ + E₁₀ − E₁₁ where E_ab = (wc_same_ab − wc_diff_ab) / (wc_same_ab + wc_diff_ab).

**In hardware.** All eight counters are implemented as hardware registers in the RTL. The CHSH_TRIAL case in the step rule selects the appropriate counter via a nested match on the (a,b,outcome) tuple.

**Classical bound.** The checked finite theorem applies to a fixed deterministic local response table with all four setting buckets sampled; under those premises, `|S| ≤ 2`. It is not by itself a finite-sample theorem about every randomized experiment or a complete physical Bell-test claim. `CHSH.v`, `CHSHStatisticalBridge.v`.

**Tsirelson bound.** The checked algebraic result gives `|S| ≤ 2√2` for the repository’s `algebraically_coherent` rational correlator model, with an explicit near-tight witness. That is a theorem about the stated polynomial model, not by itself a theorem about every physical realization. `AlgebraicCoherence.v`.

**Slice-coherence biconditional** (the gate tests slice membership rather than truthfulness, and the name records that). The machine's internal column-contractivity conditions (the conditions under which the machine certifies its CHSH statistics as coherent with the zero-marginal slice) are exactly equivalent to the zero-marginal NPA polynomial realizability conditions. This is a biconditional with no project-local axioms; it uses standard classical-real and functional-extensionality assumptions: `coq/kernel/quantum/QuantumPartitionPSD.v`, corollary `column_contractive_iff_quantum_realizable`. The forward direction (`zero_marginal_npa_column_contractive_implies_psd`) lives in `coq/kernel/nfi/MuLedgerQuantumBridge.v`; the reverse direction (`npa_psd_implies_column_contractive`) is proved by vector specialization plus `quadratic_nonneg_discriminant` from `coq/kernel/quantum/ConstructivePSD.v`.

**Variants disclosed.** Any ISA instruction, microcode operation, or hardware counter array that: (a) records outcomes of two-party binary games by (settings, outcome) tuple, (b) maintains per-setting-pair same/different counts as architectural state, and (c) supports computation of CHSH-style correlation statistics from those counts is a variant of this concept.

---

## Concept 9: Cross-Layer Refinement and Conditional Full-State Transfer (Coq → OCaml → Verilog)

**What it is.** The Thiele Machine is specified once in Coq and instantiated in three forms: (1) the Coq kernel itself (`coq/kernel/foundation/VMState.v`, `VMStep.v`), (2) an OCaml runner extracted from Coq via Coq's standard extraction mechanism (`build/thiele_core.ml`), and (3) synthesizable Verilog RTL extracted from Coq through the Kami hardware description framework (`thielecpu/hardware/rtl/thiele_cpu_kami.v`).

**What is proven.** `coq/kami_hw/Abstraction.v` establishes that the hardware step relation refines the kernel step relation: `kami_refines_vm_step`. This is proven for all 47 synth-realised opcodes; the official partition (`rtl_coverage_partition` in `coq/kami_hw/RTLGapRegistry.v`) is 37 unconditional + 10 under the joint structural invariant `morph_table_wf ∧ coupling_wf ∧ coupling_desc_safe` + 0 gaps = 47. Each component of the joint invariant is preserved by every `kami_step` (`morph_table_wf_kami_step_preserved`, `coupling_desc_safe_kami_step_preserved`, `coupling_wf_kami_step_preserved`); the latter takes `coupling_desc_safe` as a side hypothesis, which is why the conjunction is the actual inductive invariant. Zero structural gaps: `coq/kami_hw/RTLGapRegistry.v`, theorem `rtl_gap_count`.

**Full-state trace scope.** `driven_trace_commutes` in `GraphReconstructionBridge.v` requires `WFDrivenRun fuel trace ks`, which checks the instructions actually visited under program-counter fetches and fuel. The regression suite demonstrates a nonempty valid run and rejects a visited invalid partition allocation. The theorem relates the Coq hardware model and VM; emitted RTL also depends on the documented backend trust boundary. Opcode coverage counts alone do not establish full-state equivalence for arbitrary programs.

**Variants disclosed.** Any pipeline that: (a) derives multiple independent executable artifacts (software interpreter, RTL, bytecode VM) from a single formal specification, (b) maintains cross-layer correctness via machine-checked refinement proofs, and (c) uses automated test gates to verify observable equivalence on shared projections is a variant of this concept.

---

## Concept 10: Structural Entitlement and Feasible-Set Narrowing

**What it is.** A computation has *structural entitlement* to a claim P when three things are present: (a) a structural object in machine state (partition, morphism, witness counter, or formula package), (b) a checked relation between that object and P, and (c) a trace-visible certification event that makes later use of P admissible.

**Quantitative bound.** For any trace realizing strict feasible-set narrowing (Ω' ⊊ Ω) with a distinguishing observation and a certified posterior predicate, the µ cost satisfies:

⌈log₂|Ω|⌉ − ⌈log₂|Ω'|⌉ ≤ Δµ

**Decision tree witness.** The formal record must provide an explicit decision tree, a numeric payment condition relating its depth to the trace's cert-setter count, and a posterior-representative reduction tying every prior state to a posterior representative. In the current theorem, “realized by the trace” is that numeric depth/payment condition; it is not a claim that the opcode sequence walks the tree node by node. Without the tree/payment and representative premises, the narrowing is not admissible as the stated structural-entitlement witness. `coq/kernel/nfi/HonestNoFI_TheoremsWithoutAssumptions.v`, record `SoundStructuralShortcut` and theorem `structural_entitlement_representation`.

---

## Concept 11: µ-Ledger Irrecoverability from Classical State

**Statement.** No function of (vm_mem, vm_regs, vm_pc) can recover vm_mu, vm_certified, or vm_graph. The cited nonrecoverability results use colliding witnesses for specified projections; they do not assert ambiguity at every individual state:
- µ ⊥ (mem, regs, pc)
- certified ⊥ (mem, regs, pc)
- certified ⊥ (mem, regs, pc, µ)
- µ ⊥ (mem, regs, pc, certified)
- vm_graph ⊥ (mem, regs, pc, µ, certified)

These nonrecoverability statements concern the named projections. The symbol ⊥ here denotes failure of functional recovery, not statistical independence or a geometric inner product. `NecessityOfMuLedger.v`, `NecessityAbstract.v`.

---

## Concept 12: The Inquisitor Proof Hygiene System

**What it is.** An automated CI proof audit using `scripts/inquisitor.py` plus `scripts/comment_hygiene.py`.
Inquisitor scans every Coq file in the active proof tree for admitted lemmas, vacuous theorems, undocumented global axioms, physics stubs, circular import chains, and proof-scope findings.
The comment gate scans maintained project-owned source and documentation comments across the repository for unfinished or historical review markers.
Both scans use syntactic and heuristic checks; neither is a complete detector of false interpretations or inconsistent theorem premises.
Inquisitor fails on HIGH or MEDIUM findings; LOW findings are reported without independently failing the command.

**Current status.** A current Inquisitor run records 0 HIGH, 0 MEDIUM, and 0 LOW unsuppressed findings across 295 Coq files. In-source suppression markers and their justifications are reported separately by the audit; zero unsuppressed findings is not a claim that no checks were suppressed.

**Variants disclosed.** Any automated proof hygiene system that enforces zero-admit discipline and detects vacuous, tautological, or circular proofs via static analysis of proof assistant source files is a variant of this concept.

---

## Concept 13: Kernel-Conversion Vacuity Gate

**What it is.** A static analyser sitting upstream of the Inquisitor (`scripts/vacuity_gate.py`) that mechanically checks whether each Theorem's conclusion is *definitionally* equal to `True` or to one of its own hypotheses, after δ/ι/ζ/β reduction. For every Theorem in a target `.v` file, the gate synthesises two Coq probes, `Proof. intros; lazy; exact I. Qed.` and `Proof. intros; lazy in *; assumption. Qed.`, and runs `coqc` on each. A successful probe is conclusive: Coq's own kernel accepted a trivial proof, which means the theorem is a tautology dressed up. The Inquisitor consumes the gate's audit (`artifacts/vacuity_audit.json`) and emits HIGH findings on any vacuous theorem.

**Why it exists.** Inquisitor's existing vacuity rules are syntactic regex scans. The gate catches the failure mode they miss: theorems whose conclusion is `Some.Module.Predicate x y z` rather than literally `True`, but where unfolding the predicate's definition reduces to `True` or to a hypothesis. The smoke fixture `coq/test_fixtures/VacuitySmoke.v` carries five known-vacuous and four known-real theorems with inline `EXPECT_VACUOUS_TRUE` / `EXPECT_VACUOUS_HYP` / `EXPECT_CLEAR` annotations; `tests/test_vacuity_gate.py` asserts the gate matches every annotation. Sound by construction (a positive probe is genuine kernel-level acceptance), incomplete for patterns the probes cannot reduce, those slip through silently rather than producing false positives.

**Variants disclosed.** Any automated proof-vacuity detector that synthesises proof obligations against the same source kernel and uses the kernel's own acceptance as the vacuity verdict is a variant of this concept.

---

## Concept 14: Verifier Corollary: Sound Verification Requires Structural Access

**Statement.** Concept 11 (µ-Ledger Irrecoverability) says no function on the classical projection recovers µ. The verifier corollary lifts that fact into verifier theory: no verifier whose transcript is the classical projection alone is simultaneously sound and complete on a claim that distinguishes the colliding witness states. The two single-step witnesses from `NecessityOfMuLedger.v` (`po1_state_A` with µ = 1, `po1_state_B` with µ = 0) project to the same strict-shadow trace; soundness and completeness against the µ = 1 claim cannot both hold. Theorem `bare_setting_no_sound_complete_verifier` in `coq/VerifierImpossibility.v`.

**Three structurally distinct sufficient escapes.** Each one is a closed Coq theorem with a concrete verifier:
- **Substrate-trust** (`coq/VerifierEscape_Substrate.v`): the transcript carries the full `VMState`; the verifier reads µ directly. Constant-cost sound and complete. Theorem `substrate_escape_succeeds`.
- **Hardness** (`coq/VerifierEscape_Hardness.v`): the transcript carries an unforgeable commitment under a parameterised `HardnessHypothesis` record (parameter, not axiom). Constant-cost weak-sound. Theorem `hardness_escape_succeeds`.
- **Interaction** (`coq/VerifierEscape_Interaction.v`): the verifier elicits a response that pins the claim. Constant-cost sound and complete when the response set reports µ. Theorem `interactive_escape_succeeds`.

**Factorisation impossibility.** The general obstruction is stated by `V_does_not_factor_through_classical` in `coq/VerifierExhaustiveness.v`: for any transcript type `T` and any projection `π : T → BareTranscript`, no verifier `V : T → bool` that is sound and complete on the µ-sensitive claim factors through `π`. Verification must use evidence not determined by the colliding bare observation. This is not an exhaustive classification of all possible mechanisms. The substrate channel is what the structural axis newly makes available; hardness and interaction are the two routes classical cryptography and complexity already used.

**Variants disclosed.** Any verifier model parameterised over transcripts where the bare-classical channel admits a witness-state-collision impossibility, and where escape mechanisms supplying non-classical structural data restore sound completeness is a variant of this concept.

---

## Concept 15: Structural Undecidability and Observation Separation

**Statement.** The following results separate undecidability for internally representable deciders from nonrecoverability under a selected projection. They do not establish infinitely many independent dimensions or undecidability of the full-state membership predicate:

- **The axis carries its own undecidable predicate.** No internally representable decision procedure decides "this program admits a sound structural shortcut." Substrate-level: `structural_shortcut_undecidable` (`coq/kernel/nfi/StructuralUndecidability.v`), a Kleene-1938 diagonalization over the abstract `Substrate` typeclass. Unconditional for a concrete nat-coded substrate: `nat_structural_shortcut_undecidable` (`coq/kernel/foundation/NatSubstrateInstance.v`). For the actual 51-opcode VM the Gödel encoding is **discharged concretely** (program code stored via `program_to_nat` in `vm_logic_acc`, round-trip `nat_to_program_program_to_nat`); the VM theorem `vm_structural_shortcut_undecidable_encoded` (`coq/kernel/nfi/VMSubstrateEncoded.v`) is then conditional on exactly one premise, the VM's internal recursion theorem (a universal interpreter as a `list vm_instruction` plus s-m-n).

- **The predicate is not a function of the classical configuration (Rung A, the keystone).** `structural_shortcut_not_function_of_classical` / `structural_axis_invisible_to_classical` (`coq/kernel/nfi/StructuralAxisOrthogonality.v`): no function of the Turing configuration `forget s : TMSnapshot` agrees with the structural-shortcut reading on every state. The witnesses are two states **reachable** from `init_state`, `run_cert_set` (fires the cert channel, `csr_cert_addr = 650`) and `run_cert_unset` (a cost-matched no-cert run, `csr_cert_addr = 0`), with byte-identical `forget` image. This is the dividing line from Rice's theorem: the predicate is not present in the classical input, so no classical decider can be correct about it for an information-theoretic reason, on top of the computational one.

- **It survives any classical oracle (Rung B).** `structural_axis_survives_any_classical_oracle` / `structural_axis_survives_halting_oracle` (`coq/kernel/nfi/StructuralAxisRelativization.v`): no decider reading the classical configuration plus any classical oracle, a halting oracle included, is correct. The obstruction is information-theoretic, so it relativizes for free: a classical oracle's answer is itself a function of `forget s`.

- **The two axes are mutually independent, and that is not a Turing-degree gap (Rung C).** `axes_mutually_independent` (each axis not a function of the other's projection, reachable witnesses both ways) together with `structural_membership_decidable` (the structural-shortcut set is decidable from the full state, Turing degree 0, below halting, hence *comparable*, not incomparable). The independence is therefore information-theoretic, not degree-theoretic; the decidability theorem is an explicit guard against the degree-theoretic over-reading.

**What it does not claim.** µ is used only as a monotone ledger; this does not establish µ measures entropy or Kolmogorov information. The mutual independence is not a Turing-degree separation. The VM undecidability is conditional on the VM recursion theorem; the unconditional discharge is the nat substrate.

**Variants disclosed.** Any computational model carrying state at the step-transition level that a classical projection drops, equipped with a predicate detected through that state, where (i) the predicate is undecidable by the model's own deciders and (ii) the predicate is provably not a function of the classical projection, so that no classical decider, oracle-equipped or not, can be correct about it is a variant of this concept.

---

## Prior Art Timeline

| Date | Event |
|------|-------|
| January 2025 | Development begins. Categorical rendering engine, first categorical CPU concepts. |
| August 15, 2025 | First public commit to this repository. The repository history records early versions of the concepts above; the exact scope of that first revision is a historical question, not a theorem of the current tree. |
| August–December 2025 | Coq kernel developed. No Free Insight proven. µ-initiality proven. LASSERT dual-witness requirement formalized. |
| January–April 2026 | Hardware proofs completed (Abstraction.v). Slice-coherence ↔ NPA biconditional proven. µ-hierarchy proven. |
| May 2026 | v2.0.0 published to GitHub and Zenodo. Disclosure and monograph published. |
| May 19, 2026 | Public statement (commit 655d0a1c) that the level-1 NPA cone strictly contains the Tsirelson set for CHSH, the Q_{1+AB} lift with the Ishizaka correlator-level exactness citation, and the full-elliptope connection named as an open gap, predating the July 2026 publication of the behavior-set finite-level impossibility result (Chaturvedi, arXiv:2607.14569), which this project cites and does not claim. |
| June 2026 | v2.0.1: zero admits across 267 files; 3,823 theorems probed, zero project-local axioms. |
| June 2026 | v2.0.2: the Q_{1+AB} moment matrix uses −γ5 in the (A₀B₁, A₁B₀) conjugate cell under ⟨B₀B₁⟩ = 0. The level-1+AB checker includes a CHSH = 2.4 acceptance example. |
| June 2026 | v3.0.0: five minimal models inspired by PoS finality, gas metering, TEE attestation, certificate transparency, and proof-carrying verification instantiate the kernel’s abstract records. Receipt: 273 files, 3,905 theorems probed, zero project-local axioms. |
| July 2026 | v3.0.1: structural cost and certification results, with explicit witness constructions, cost schedules, and falsification conditions. Receipt: 277 files, 3,937 theorems probed, zero project-local axioms. |
| July 2026 | v3.1.0: existential PSD completion for CHSH correlators, a sound integer elliptope gate with interior and boundary certificates, and five minimal pointer-observable models. `five_disciplines_are_pointers` is closed under the global context; the theorem concerns the chosen observer models. Receipt: 281 files, 3,980 theorems probed, zero project-local axioms. |

---

## Repository and Reproducibility

The formal and executable components can be checked with the following commands; physical applicability and modeling judgments require additional evidence:

```bash
make -C coq -j4          # builds the active Coq project
python3 scripts/inquisitor.py  # audits proof hygiene
pytest tests/ -q         # runs the test suite
```

Coq compilation checks proof terms against their statements and assumptions. It does not establish that physical premises have an instance, that a model matches a deployment, or that broader prose follows from the quantified theorem. The assumption receipt records the library dependencies of the checked results.

---

## Note on Scope

This disclosure records the concepts, implementations, variants, dates, and source locations described above. It is meant to make the public record clear, searchable, and dated; it does not decide legal prior-art status, patentability, scope of any claim, or what another party may obtain. The technical boundaries in this document are the boundaries I can support from this repository.

*Devon Thiele, July 2026*
