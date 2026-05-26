# Technical Disclosure: The Thiele Machine

**Author:** Devon Thiele  
**First public disclosure:** August 15, 2025 (repository creation; development began January 2025)  
**Current date:** May 2026  
**Repository:** https://github.com/sethirus/The-Thiele-Machine  
**License:** Apache 2.0 (software), CC-BY-SA-4.0 (monograph/documentation)  
**Purpose of this document:** Defensive publication. Every concept described here is publicly disclosed prior art under 35 U.S.C. § 102 (US) and Article 54 EPC (Europe) as of the dates above. This document is submitted for indexing to IP.com and similar prior art databases.

---

## Summary

The classical theory of computation has two axes: time and space. The Thiele Machine adds a third — certification cost — and proves the classical models are its structural-axis projection. The argument is four steps; to dismiss it, name the step you reject.

**1. A2 cannot be written on a classical step relation.** A2 is the rule that any step flipping certification from false to true costs at least 1. A Turing machine, a register machine, a lambda reducer carries no certification flag for A2 to constrain. The rule is unformulable on classical state, not merely unenforced. See `cs_cert_costs` in `coq/kernel/nfi/UniversalCertificationCost.v`.

**2. Therefore the substrate is forced.** Any model that formalises certification cost at the step rule must carry state classical models do not have. The structural axis (`vm_mu`, `vm_certified`) is the minimum state for A2 to be a sentence in the first place. The substrate is not an extension of classical computation; it is what is required for the classical models' silent omission to be representable at all.

**3. Classical computation is the projection.** `lift_config`, `thiele_simulates_turing`, and `degenerate_projection_theorem` (in `coq/kernel/foundation/`) mechanise that classical computation is exactly the image of substrate computation under the projection that forgets the structural axis. `D4_strictness` witnesses substrate states with no classical preimage. Every Turing machine, every register machine, every lambda-calculus reducer, every CPU on every desk: a Thiele Machine running with the structural axis sidelined.

**4. Every concept disclosed below is downstream of these four steps.** The foundational claim does not require 47 opcodes, an FPGA, or any of the specific instruction semantics enumerated in this document. The minimum instruction set that witnesses the substrate is two opcodes: any classical compute primitive (so subsumption has something to project to) and one opcode that flips certification (so A2 has something to enforce). `instr_certify` is the load-bearing opcode for A2; everything else is engineering exploration of what the substrate can express.

**The standard misread.** The trained reflex is: A2 can be enforced in software on a TM, so the substrate distinction is a hardware/software boundary, not a fundamental one. The falsifier is one sentence. A Turing machine cannot refuse to execute a buggy A2-simulator. A Thiele substrate cannot execute one. Load a Thiele simulator onto a TM with a bug — a program that certifies without incrementing μ. The TM runs it faithfully, because its step rule has no field for A2 and cannot detect the bug. Load the same buggy program onto a Thiele substrate; the step rule traps. A2 is not interpreted by the simulator and could be skipped; it is the transition law itself. Subsumption is a step-rule claim, not a software-layer claim. "Thiele is simulable on a TM" is true and is not the question. "Thiele's step rule can be written down on a TM" is the question, and the answer is no.

The concrete realisation disclosed in the remainder of this document is a Coq kernel formalisation of µ (a monotone cost ledger), No Free Insight (a conservation law proven from the kernel's step function), a 47-opcode instruction set architecture, an extracted OCaml reference runner, and synthesizable Verilog RTL extracted from Coq through the Kami framework. All theorems described here have been machine-checked in Coq with zero admitted lemmas in the active proof tree.

---

## Concept 1: The µ-Ledger (Structural Cost Register)

**What it is.** Every Thiele Machine state carries a field `vm_mu : nat` — a natural number that starts at 0 and is monotonically non-decreasing. Every instruction carries an explicit `mu_delta` parameter encoding its cost. The machine's step function adds exactly `instruction_cost(i)` to `vm_mu` on every step, including error cases. There is no backdoor. There is no instruction that decreases `vm_mu`.

**The cost schedule.** Instructions fall into two classes:
- *Ordinary compute* (ADD, LOAD, STORE, JUMP, PNEW, MORPH, etc.): cost = `mu_delta`, which may be 0.
- *Certification and revelation* (CERTIFY, MORPH_ASSERT, LASSERT, LJOIN, EMIT, REVEAL, READ_PORT): cost = `S(mu_delta)` = `mu_delta + 1` at minimum. Even with `mu_delta = 0`, these cost at least 1.

**EMIT, REVEAL, READ_PORT** additionally charge proportional to information content: `|payload|_bits + S(mu_delta)`.

**LASSERT** charges `flen × 8 + S(mu_delta)` where `flen` is the encoded formula-unit count read from the formula's own in-memory header.

**Why S(δ) = δ+1 is the unique honest minimum.** δ+0 allows free certification. δ+2 overcharges. δ+1 is the unique minimum that makes certification impossible for free. This is proven, not chosen: `MuCostDerivation.v`, theorems `cost_necessity` and `cost_uniqueness`.

**Hardware.** In the synthesized RTL (`thielecpu/hardware/rtl/thiele_cpu_kami.v`), `vm_mu` is a 32-bit register incremented inline within the step rule. The cost field occupies bits [7:0] of the 32-bit instruction word.

**Variants disclosed.** The µ-ledger concept applies to any instruction-set architecture where: (a) every instruction carries an explicit cost field, (b) a dedicated monotone accumulator tracks total cost, and (c) a mandatory-floor class of instructions is precluded from zero cost. This includes implementations on x86, ARM, RISC-V, MIPS, GPU PTX, and FPGA soft-cores, using any monotone cost domain (natural numbers, floating-point entropy, hash-chain tips, p-adic valuations, or any ordered monoid).

---

## Concept 2: No Free Insight (Conservation Law)

**Statement.** For any trace of the Thiele Machine that starts with neither certification channel active and ends with at least one active, the total `vm_mu` increase is at least 1. More strongly: if the trace starts with feasible set Ω and ends with a strictly smaller certified feasible set Ω', then:

    Δµ ≥ ⌈log₂|Ω|⌉ − ⌈log₂|Ω'|⌉

**Proof structure.** The two concrete certification channels are:
1. `csr_cert_addr`: set to the ASCII checksum of a property string when MORPH_ASSERT succeeds on a non-empty property.
2. `vm_certified`: set to true by the CERTIFY opcode.

Both CERTIFY and MORPH_ASSERT are in the mandatory-floor class (cost ≥ 1). No other instruction touches either channel. This is verified by case analysis over all 46 opcodes. Therefore any trace that activates either channel paid at least 1. `AbstractNoFI.v`, `NoFreeInsight.v`.

**Abstract version.** The theorem holds for any abstract certification system satisfying: (a) a certification predicate, (b) a step function, (c) a cost function where every single-step uncertified→certified transition costs ≥ 1. The Thiele Machine is an instance. `coq/kernel/nfi/AbstractNoFI.v`, theorem `no_free_certification`. The substrate-agnostic version is `universal_nfi_any_substrate` in `coq/kernel/nfi/UniversalCertificationCost.v`.

**Variants disclosed.** No Free Insight as a conservation law applies to any computational system, hardware or software, that (a) distinguishes certified from uncertified structural claims in its state, and (b) charges a positive cost for the certification transition. This includes formal verification co-processors, hardware security modules, trusted execution environments, and any system implementing proof-carrying code or certificate-validated computation.

---

## Concept 3: µ-Initiality (Uniqueness of the Cost Measure)

**Statement.** Let M be any function on machine states satisfying: (a) M(init_state) = 0, and (b) M(vm_apply s i) = M(s) + instruction_cost(i) for all reachable states. Then M = vm_mu on all reachable states. There is no alternative instruction-consistent cost measure. `MuInitiality.v`.

**What this means.** Given the cost assignment (S(δ) for cert-setters, |payload|+S(δ) for EMIT, etc.), µ is not just one valid accounting. It is the only valid accounting. Any system that assigns costs the same way must produce the same totals.

---

## Concept 4: The µ-Hierarchy Theorem

**Statement.** For every k ≥ 1, a level-k certification event costs exactly k in µ. There is no shortcut that achieves level-k certification at cost < k. The hierarchy is strict: no finite trace collapses two adjacent levels. `coq/kernel/mu_calculus/MuHierarchyTheorem.v`, theorem `mu_hierarchy_theorem`.

---

## Concept 5: The CERTIFY Opcode

**What it is.** A dedicated instruction that sets `vm_certified = true` in machine state. Cost: `S(mu_delta) = mu_delta + 1 ≥ 1`. Once set, `vm_certified` is never cleared by any subsequent instruction. The CERTIFY opcode is the only instruction that sets this field.

**Hardware.** In the RTL, `certified` is a 1-bit register. The CERTIFY case in the step rule sets it unconditionally. The cost is charged to the `mu` register in the same cycle.

**Variants disclosed.** Any ISA extension, co-processor instruction, microcode operation, or hardware primitive that: (a) sets a persistent certification bit in processor state, (b) charges a mandatory positive cost to a monotone accumulator, and (c) is the sole instruction capable of setting that bit — is a variant of this concept.

---

## Concept 6: The LASSERT Opcode (Logic Assertion with Dual Witness)

**What it is.** LASSERT reads a logical formula from memory (at the address in register `freg`), reads a certificate block from memory (at the address in register `creg`), and validates both using an on-chip Logic Engine FSM. Parameters: `freg` (formula address register), `creg` (certificate address register), `kind` (boolean: SAT or UNSAT path), `flen` (declared formula-unit count), `cost` (mu_delta).

**Dual-witness requirement.** In the SAT path (`kind = true`): the certificate block must contain both a satisfying assignment and a falsifying assignment. LASSERT succeeds only if the declared `flen` matches the formula's in-memory header count, the first witness satisfies the formula, and the second witness falsifies it. This proves the formula is neither unsatisfiable (it has a witness) nor a tautology (it has a falsifying witness), and therefore genuinely narrows the feasible set.

**Anti-gaming.** If the declared `flen` in the instruction encoding does not match the actual formula length read from the formula's in-memory header, the machine traps: PC jumps to `LASSERT_TRAP_PC = 0xF00`, `vm_err` is set, and the check does not succeed. The µ cost is still charged even on trap. This prevents declaring a small `flen` for a large formula. `StateSpaceCounting.v`, theorems `lassert_honest_cost` and `lassert_honest_mu_cost`.

**On-chip Logic Engine.** Formula verification is performed entirely on-chip by a finite-state machine (phases: idle, header, SAT scan, UNSAT scan, UNSAT conflict check) without calling any external solver. The FSM reads formula words and certificate bytes from `vm_mem` via register-indexed addressing.

**Variants disclosed.** Any hardware instruction or co-processor command that: (a) reads a logical formula from memory, (b) verifies a satisfying and a falsifying witness in hardware without external solver calls, (c) charges cost proportional to formula length to a monotone accumulator, and (d) traps on length-declaration mismatch — is a variant of this concept.

---

## Concept 7: The Partition Graph as First-Class Machine State

**What it is.** The Thiele Machine state includes a field `vm_graph` that is a partition graph: a record of named modules (memory regions with attached axiom sets) and typed morphisms between them. This is not a data structure stored in memory. It is a separate top-level field of the machine state, alongside registers, memory, and program counter.

**Operations.** The ISA includes dedicated opcodes for partition graph manipulation: PNEW (allocate module), PSPLIT (split module into two), PMERGE (merge two modules), PDISCOVER (query structure), MORPH (create morphism), COMPOSE (compose morphisms), MORPH_ID (identity morphism), MORPH_DELETE (remove morphism), MORPH_ASSERT (assert property on morphism, activates cert channel), MORPH_TENSOR (tensor morphisms), MORPH_GET (query morphism).

**µ-Ledger Necessity.** The partition graph is provably irrecoverable from any combination of (memory, registers, program counter, µ, vm_certified). There exist reachable states with identical classical shadow but different morphism structure. This is not a design choice; it is a theorem. `NecessityOfMuLedger.v`, `PartitionSeparation.v`.

**Variants disclosed.** Any processor architecture, ISA extension, or hardware accelerator that maintains partition structure (module decomposition, morphism map, or typed relational structure between memory regions) as a distinct top-level field of architectural state — separate from the flat memory and register file — is a variant of this concept.

---

## Concept 8: The CHSH_TRIAL Instruction and Witness Counters

**What it is.** A dedicated instruction that increments one of eight counters in `vm_witness` based on measurement settings (a,b) ∈ {(0,0),(0,1),(1,0),(1,1)} and outcome (same/different). The eight counters are: `wc_same_00`, `wc_diff_00`, `wc_same_01`, `wc_diff_01`, `wc_same_10`, `wc_diff_10`, `wc_same_11`, `wc_diff_11`. The CHSH score S = E₀₀ + E₀₁ + E₁₀ − E₁₁ where E_ab = (wc_same_ab − wc_diff_ab) / (wc_same_ab + wc_diff_ab).

**In hardware.** All eight counters are implemented as hardware registers in the RTL. The CHSH_TRIAL case in the step rule selects the appropriate counter via a nested match on the (a,b,outcome) tuple.

**Classical bound.** |S| ≤ 2 for any local hidden-variable strategy. Proven in Coq from first principles: `ClassicalBound.v`.

**Tsirelson bound.** |S| ≤ 2√2 for the zero-marginal NPA polynomial model. Proven algebraically in `AlgebraicCoherence.v`.

**Thiele-honesty biconditional.** The machine's internal column-contractivity conditions (the conditions under which the machine is "honest" about its CHSH statistics) are exactly equivalent to the zero-marginal NPA polynomial realizability conditions. This is a zero-axiom biconditional proven in Coq: `coq/kernel/quantum/QuantumPartitionPSD.v`, corollary `column_contractive_iff_quantum_realizable`. The forward direction (`zero_marginal_npa_column_contractive_implies_psd`) lives in `coq/kernel/nfi/MuLedgerQuantumBridge.v`; the reverse direction (`npa_psd_implies_column_contractive`) is proved by vector specialization plus `quadratic_nonneg_discriminant` from `coq/kernel/quantum/ConstructivePSD.v`.

**Variants disclosed.** Any ISA instruction, microcode operation, or hardware counter array that: (a) records outcomes of two-party binary games by (settings, outcome) tuple, (b) maintains per-setting-pair same/different counts as architectural state, and (c) supports computation of CHSH-style correlation statistics from those counts — is a variant of this concept.

---

## Concept 9: The Three-Layer Isomorphism (Coq → OCaml → Verilog)

**What it is.** The Thiele Machine is specified once in Coq and instantiated in three forms: (1) the Coq kernel itself (`coq/kernel/foundation/VMState.v`, `VMStep.v`), (2) an OCaml runner extracted from Coq via Coq's standard extraction mechanism (`build/thiele_core.ml`), and (3) synthesizable Verilog RTL extracted from Coq through the Kami hardware description framework (`thielecpu/hardware/rtl/thiele_cpu_kami.v`).

**What is proven.** `coq/kami_hw/Abstraction.v` establishes that the hardware step relation refines the kernel step relation: `kami_refines_vm_step`. This is proven for all 46 opcodes; the official partition (`rtl_coverage_partition` in `coq/kami_hw/RTLGapRegistry.v`) is 36 unconditional + 10 under the joint structural invariant `morph_table_wf ∧ coupling_wf ∧ coupling_desc_safe` + 0 gaps = 46. Each component of the joint invariant is preserved by every `kami_step` (`morph_table_wf_kami_step_preserved`, `coupling_desc_safe_kami_step_preserved`, `coupling_wf_kami_step_preserved`); the latter takes `coupling_desc_safe` as a side hypothesis, which is why the conjunction is the actual inductive invariant. Zero structural gaps: `coq/kami_hw/RTLGapRegistry.v`, theorem `rtl_gap_count`.

**Variants disclosed.** Any pipeline that: (a) derives multiple independent executable artifacts (software interpreter, RTL, bytecode VM) from a single formal specification, (b) maintains cross-layer correctness via machine-checked refinement proofs, and (c) uses automated test gates to verify observable equivalence on shared projections — is a variant of this concept.

---

## Concept 10: Structural Entitlement and Feasible-Set Narrowing

**What it is.** A computation has *structural entitlement* to a claim P when three things are present: (a) a structural object in machine state (partition, morphism, witness counter, or formula package), (b) a checked relation between that object and P, and (c) a trace-visible certification event that makes later use of P admissible.

**Quantitative bound.** For any trace realizing strict feasible-set narrowing (Ω' ⊊ Ω) with a distinguishing observation and a certified posterior predicate, the µ cost satisfies:

    ⌈log₂|Ω|⌉ − ⌈log₂|Ω'|⌉ ≤ Δµ

**Decision tree witness.** The trace must provide an explicit decision tree realized by the trace's actual sequence of observations. The posterior-representative reduction must tie every prior state to a posterior representative. Without both, the narrowing is not admissible as sound structural entitlement. `coq/kernel/nfi/HonestNoFI_TheoremsWithoutAssumptions.v`, record `SoundStructuralShortcut` and theorem `structural_entitlement_representation`.

---

## Concept 11: µ-Ledger Irrecoverability from Classical State

**Statement.** No function of (vm_mem, vm_regs, vm_pc) can recover vm_mu, vm_certified, or vm_graph. The independence results hold simultaneously and from every reachable machine state:
- µ ⊥ (mem, regs, pc)
- certified ⊥ (mem, regs, pc)
- certified ⊥ (mem, regs, pc, µ)
- µ ⊥ (mem, regs, pc, certified)
- vm_graph ⊥ (mem, regs, pc, µ, certified)

The three non-classical fields (µ, vm_certified, vm_graph) are each irrecoverable from any combination of the others plus classical state. `NecessityOfMuLedger.v`, `NecessityAbstract.v`.

---

## Concept 12: The Inquisitor Proof Hygiene System

**What it is.** An automated CI tool (`scripts/inquisitor.py`) that scans every Coq file in the active proof tree for: Admitted lemmas, `admit` tactics, vacuous theorems (conclusion is `True` or `0=0`), undocumented global axioms, physics stubs (quantity defined as placeholder constant), circular import chains, and TODO/FIXME markers in proof comments. The tool enforces zero-tolerance on all categories and fails CI on any finding.

**Current status.** 0 HIGH, 0 MEDIUM, 0 LOW findings across 205 active Coq files.

**Variants disclosed.** Any automated proof hygiene system that enforces zero-admit discipline and detects vacuous, tautological, or circular proofs via static analysis of proof assistant source files is a variant of this concept.

---

## Concept 13: Kernel-Conversion Vacuity Gate

**What it is.** A static analyser sitting upstream of the Inquisitor (`scripts/vacuity_gate.py`) that mechanically checks whether each Theorem's conclusion is *definitionally* equal to `True` or to one of its own hypotheses, after δ/ι/ζ/β reduction. For every Theorem in a target `.v` file, the gate synthesises two Coq probes — `Proof. intros; lazy; exact I. Qed.` and `Proof. intros; lazy in *; assumption. Qed.` — and runs `coqc` on each. A successful probe is conclusive: Coq's own kernel accepted a trivial proof, which means the theorem is a tautology dressed up. The Inquisitor consumes the gate's audit (`artifacts/vacuity_audit.json`) and emits HIGH findings on any vacuous theorem.

**Why it exists.** Inquisitor's existing vacuity rules are syntactic regex scans. The gate catches the failure mode they miss: theorems whose conclusion is `Some.Module.Predicate x y z` rather than literally `True`, but where unfolding the predicate's definition reduces to `True` or to a hypothesis. The smoke fixture `coq/test_fixtures/VacuitySmoke.v` carries five known-vacuous and four known-real theorems with inline `EXPECT_VACUOUS_TRUE` / `EXPECT_VACUOUS_HYP` / `EXPECT_CLEAR` annotations; `tests/test_vacuity_gate.py` asserts the gate matches every annotation. Sound by construction (a positive probe is genuine kernel-level acceptance), incomplete for patterns the probes cannot reduce — those slip through silently rather than producing false positives.

**Variants disclosed.** Any automated proof-vacuity detector that synthesises proof obligations against the same source kernel and uses the kernel's own acceptance as the vacuity verdict is a variant of this concept.

---

## Concept 14: Verifier Corollary — Sound Verification Requires Structural Access

**Statement.** Concept 11 (µ-Ledger Irrecoverability) says no function on the classical projection recovers µ. The verifier corollary lifts that fact into verifier theory: no verifier whose transcript is the classical projection alone is simultaneously sound and complete on any µ-sensitive claim. The two single-step witnesses from `NecessityOfMuLedger.v` (`po1_state_A` with µ = 1, `po1_state_B` with µ = 0) project to the same strict-shadow trace; soundness and completeness against the µ = 1 claim cannot both hold. Theorem `bare_setting_no_sound_complete_verifier` in `coq/VerifierImpossibility.v`.

**Three structurally distinct sufficient escapes.** Each one is a closed Coq theorem with a concrete verifier:
- **Substrate-trust** (`coq/VerifierEscape_Substrate.v`): the transcript carries the full `VMState`; the verifier reads µ directly. Constant-cost sound and complete. Theorem `substrate_escape_succeeds`.
- **Hardness** (`coq/VerifierEscape_Hardness.v`): the transcript carries an unforgeable commitment under a parameterised `HardnessHypothesis` record (parameter, not axiom). Constant-cost weak-sound. Theorem `hardness_escape_succeeds`.
- **Interaction** (`coq/VerifierEscape_Interaction.v`): the verifier elicits a response that pins the claim. Constant-cost sound and complete when the response set reports µ. Theorem `interactive_escape_succeeds`.

**Factorisation impossibility.** The trichotomy is closed at the bottom by `V_does_not_factor_through_classical` in `coq/VerifierExhaustiveness.v`: for any transcript type `T` and any projection `π : T → BareTranscript`, no verifier `V : T → bool` that is sound and complete on the µ-sensitive claim factors through `π`. Verification must access non-classical structural information in the transcript. The substrate channel is what the structural axis newly makes available; hardness and interaction are the two routes classical cryptography and complexity already used.

**Variants disclosed.** Any verifier model parameterised over transcripts where the bare-classical channel admits a witness-state-collision impossibility, and where escape mechanisms supplying non-classical structural data restore sound completeness, is a variant of this concept.

---

## Prior Art Timeline

| Date | Event |
|------|-------|
| January 2025 | Development begins. Categorical rendering engine, first categorical CPU concepts. |
| August 15, 2025 | First public commit to this repository. All concepts above are present in some form. |
| August–December 2025 | Coq kernel developed. No Free Insight proven. µ-initiality proven. LASSERT dual-witness requirement formalized. |
| January–April 2026 | Hardware proofs completed (Abstraction.v). Thiele-honesty ↔ NPA biconditional proven. µ-hierarchy proven. Zero admits confirmed across 205 files. |
| April 2026 | This disclosure published. Monograph published. |

---

## Repository and Reproducibility

All claims in this disclosure are verifiable by running:

```bash
make -C coq -j4          # builds all 323 Coq files
python3 scripts/inquisitor.py  # confirms zero findings
pytest tests/ -q         # 952 tests pass
```

The Coq proof compilation is the ground truth. If a proof does not compile, the claim is not proven. Every theorem listed in this document compiles to `Qed`.

---

## Note on Scope

This disclosure covers the concepts as implemented. It does not claim to cover all conceivable implementations of structural cost accounting in computation — only the specific inventive concepts described above, as first publicly disclosed in this repository. The goal of this document is defensive: to ensure that the public record contains a clear, searchable, dated description of these concepts so that no third party can obtain a patent on them.

*Devon Thiele, May 2026*
