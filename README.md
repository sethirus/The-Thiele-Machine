# The Thiele Machine

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.17316437.svg)](https://doi.org/10.5281/zenodo.17316437)
[![Latest release](https://img.shields.io/github/v/release/sethirus/The-Thiele-Machine?label=release)](https://github.com/sethirus/The-Thiele-Machine/releases/latest)
[![CI](https://github.com/sethirus/The-Thiele-Machine/actions/workflows/ci.yml/badge.svg)](https://github.com/sethirus/The-Thiele-Machine/actions/workflows/ci.yml)
[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)
[![Coq](https://img.shields.io/badge/Coq-0%20project--local%20axioms-EF4135?logo=coq&logoColor=white)](coq/)
[![Inquisitor](https://img.shields.io/badge/Inquisitor-0%20findings-brightgreen)](scripts/inquisitor.py)
[![Kami intermediate bridge](https://img.shields.io/badge/Kami%20intermediate%20bridge-47%2F47%20Qed-orange)](coq/kami_hw/GraphReconstructionBridge.v)

**I didn't invent a machine. I found one.**

That is how I see this work.
I think there is structure here that the usual picture of computation leaves out.

**What the Thiele Machine is.**
It is an abstract model of computation.
It is a machine the way Turing's machine is a machine: mathematics you can reason about, not a device.
It is not a CPU.
It is not an instruction set, a VM, a graph, or category theory.
Those are things I built with it, or things it can carry.
The model is small: a state, a step rule, a ledger that only climbs, a rule for which steps have to pay, and a window saying what an observer sees.
The event it accounts for happens on any computer, whether anybody keeps track of it or not.
Turing's model has no place for the record of that event and doesn't enforce one.
A Turing machine can be programmed to keep the record, and then it obeys the toll and is a Thiele machine; but when it runs another program's record as data on its tape, nothing in its own step enforces it.
The event's physical cost comes in only under Landauer's principle, as a named premise.
The record exists only if something keeps it, and keeping it, priced, is what the model adds: accounting, not computing power.

**Names.**
The Thiele Machine, with capitals, is the model and nothing else.
A Thiele machine, lower case, is any particular system proved to meet the model's definition (a certification system: states, moves, a step, a cost, a reading, and the toll), the way one rule table is a Turing machine.
A Thiele machine is Thiele-complete when its base is Turing-universal, so it computes anything a Turing machine can while carrying the record and paying the toll.
A universal Thiele machine runs any machine of a stated class as a guest, with the guest's record kept and its toll collected by its own step; one is proved for the small machine's programs ([minimal/UniversalThiele.v](minimal/UniversalThiele.v)), and a machine from elsewhere keeps its computation and toll there but not its exact prices.

**What this repository is.**
It is an argument, made with that model, about what an account of computation should preserve.
The usual account describes a computation by what it reads and writes: memory, registers, where the program is.
I think that account is a shadow.
There is another axis: what the computation established, and what establishing it cost.

1. **The shadow loses something real.** Two runs can look identical through the usual window and still differ in what they established and paid. Proved, for each window I name.
2. **Establishing is not free.** If the step that turns uncertified into certified has to pay, every run from uncertified to certified has paid. Proved, for any system that follows that rule. The rule isn't arbitrary: on a machine with finite memory, a certificate that can never be revoked can only be switched on by a step that merges two states, and merging is what Landauer's principle charges for whenever the machine could be in either state. Proved in [PermanentCertification.v](coq/kernel/nfi/PermanentCertification.v), with Landauer's principle as the named premise. The heat comes from that uncertainty: a machine already known to be in one state loses nothing, and [PermanentCertificationEntropy.v](coq/kernel/nfi/PermanentCertificationEntropy.v) proves both sides. A small finite piece of the VM is such a machine: programs built from CERTIFY 0, JUMP a 2 and CHECKPOINT run on the VM paying exactly what their merges cost, where the JUMP charge of two is the program's own choice of cost ([FiniteCertMachine.v](coq/kernel/nfi/FiniteCertMachine.v)). In the full VM, every certification flip is a priced merge, while JUMP 0 0 is a zero-cost merge. Thus the VM does not price every merge; the theorem does not classify all non-certifying merges.
3. **Leaning on a fact takes a paid history.** A computation is entitled to lean on a structural fact when it holds the evidence and a history that earned it. Defined; the cost floor is proved for shortcuts that hand over their receipts.
4. **So the axis belongs in the step.** Proposed. This is the conviction the proofs are there to test. Part of it is proved. An account that prices certification exactly, never less and never more, can't compute that price from the window: a step that certifies and a step that doesn't can look the same through it, and the VM has such a pair for both windows I name ([ShadowPricing.v](coq/kernel/nfi/ShadowPricing.v)). The exact price needs the reading in the step. And on a machine with finite memory, an account that charges one unit for every halving of the number of distinct states (Landauer's principle in counting form) already charges every step that writes a permanent record at least the logarithm of how many states it squeezes together ([PermanentRecordPricing.v](coq/kernel/nfi/PermanentRecordPricing.v)). The same bound holds in bits of Shannon entropy, and for the uniform distribution on the m certified and k switching states, with Landauer's principle as a named premise, it is at least k_B T ln((m+k)/m) of heat ([PermanentCertificationEntropy.v](coq/kernel/nfi/PermanentCertificationEntropy.v)). Whether every account has to price merges is physics.
5. **Which events every account has to price.** Certification is the one I pinned down. On finite hardware the events that must be priced are the merges; every permanent-record write is one, and a flip escapes the price only when the same step can take it back. Proved, with Landauer's principle as the named premise. The guess that the priced events are exactly the permanent records is false; a three-state counterexample is in the same file. No theorem selects another universal class of priced events.
6. **What carries the weight.** Three results. Every machine can carry the record axis: take a Turing machine, a RAM, the VM, any deterministic machine, and any event it reaches, and the machine plus a latch on that event, charging one unit when the latch sets, is an honest extension of it ([`latch_core_honest`](coq/kernel/foundation/RecordAxisDiscrimination.v)). The record can't be read back off the shadow: on the VM, no function of the named windows returns certification or μ (`cert_not_function_of_forget`, `mu_not_function_of_bare_observable`). And on finite hardware a step that writes a permanent record merges two states (`permanent_flip_is_not_injective`), so an account that prices merges already prices the write (`a2_from_merging_price_and_permanence`). Proved. The shape of the axis is close to definitional: a record that never switches off and is driven by the computation moves as a latch on one event (`record_axis_is_latch_holds`), and that follows from those two conditions in a few lines. The pointer question asks which event gets latched; no theorem here selects one uniquely.

Two machines here are Thiele machines.
The small one, [minimal/EarnedCore.v](minimal/EarnedCore.v), earns its commitments: a commitment goes through only on a fact a passing check wrote, and every certification traces back to such a check.
It runs any two-counter program, so by Minsky's theorem (cited, not re-proved) it computes whatever a Turing machine computes, which makes it Thiele-complete.
The big one is a test bench: the 51-opcode VM and the Coq kernel that defines it, with the extracted runner and the CHSH check.
It prices commitments and doesn't check that they were earned.
Whether it is Thiele-complete is open, and nothing depends on it.
The CPU is not a Thiele machine: it is hardware that implements the kernel within stated bounds (47 of the 51 opcodes, 32-bit words).
Both are there so the argument has something you can run and try to break.
They are witnesses.
They are not the subject.

A computation gives you an answer.
What did it establish on the way there?
Which distinctions did it keep?
What did it cost to establish them?
I want those questions inside the mathematics, where somebody can take the argument apart and check it.

Certification is one point I could pin down.
There is more here than one point, and I am not done looking.
I pinned down the definitions, built a VM you can run, and made Coq check what happens when you throw some of that information away.

I call what remains a **shadow**.
For the projections in the proofs, the blindness is real: different executions become indistinguishable, and no clever decoder can recover a distinction the observation has erased.
Keep the full information in another encoding and you can recover it.
That makes the question sharper: what should an account of computation keep?

I think this reaches further than a useful accounting machine.
I think there is something foundational here.
That is my conviction, and the larger argument is still mine to earn.
The proofs already give you something concrete to challenge: accounting laws, pricing results, structural separation, certificate checks, and implementations you can run.

## Run it. Don't take my word.

I don't trust my own eye to catch a gap in an argument I want to believe, so I made Coq check the formal claims and built separate tests and audits for prose, artifacts, and implementation boundaries.
You shouldn't trust me either.
Run it.

Coq 8.18+ and Python 3, clean checkout:

```bash
make verify        # about ten seconds
make verify-research  # observation policies, event floors, and descent from traces
```

No Coq where you are?
Most review environments, laptops and LLM sandboxes alike have none, and the argument doesn't get to hide behind a toolchain.
There is a tier for that: Python's standard library and nothing else.

```bash
python3 minimal/nofi_demo.py   # exhaustive sweeps + measured algorithms against the cost floor; exits 0
python3 -c "import json; d=json.load(open('artifacts/print_assumptions_all_proofs.json')); print(d['summary'])"
```

The second command prints the assumption receipt: 14,574 theorems probed, zero *project-local* axiom findings.
The badge says project-local, and that is the precise claim: it is not "zero axioms".
6,994 of those theorems are closed under the global context outright; the remaining 7,580 use only Coq standard-library assumptions: dependent functional extensionality, `Eqdep.Eq_rect_eq.eq_rect_eq`, `ClassicalDedekindReals.sig_not_dec`, `ClassicalDedekindReals.sig_forall_dec`, and `Classical_Prop.classic`.
Those library assumptions are disclosed in the receipt; what is zero is axioms this project added.
Validate the committed receipt quickly with `make assumption-receipt-check`.
That path reuses the exact theorem/axiom results when the semantic fingerprint is unchanged and performs the full corpus derivation only after proof-relevant inputs drift.
Regenerate the receipt itself with `make assumption-receipt`.
**The output of these two commands is the ground floor for any review, human or AI.**
**An assessment without it is an assessment of the prose, not of the repository.**

`make verify` compiles [minimal/MuCore.v](minimal/MuCore.v): a minimal instance of the cost and projection arguments in one file, standard library only, nothing of mine to import.
A machine state is the classical part you already know, memory and registers and a program counter, plus two fields this bare configuration omits: a cost ledger μ, and a bit that says *certified*.
One law, called A2: any single step that flips that bit from false to true costs at least 1, charged right there in the step, not in some checker you could skip.
Ten theorems fall out of that, and every one ends with `Print Assumptions` reporting `Closed under the global context`.
Zero axioms.
Zero `Admitted`.
If a theorem were leaning on a hidden assumption, that line would rat it out and `make verify` would stop.
It doesn't.

It compiles [minimal/Napkin.v](minimal/Napkin.v) too: the three-line napkin argument written out as seven theorems, each closing the same way, zero axioms.
The napkin doesn't just hold; it compiles.

[minimal/EarnedCore.v](minimal/EarnedCore.v) is the smallest machine I could build that earns its commitments instead of pricing them.
Two counters, a table of checked facts, and three priced instructions: CHECK, COMMIT and CERTIFY.
A COMMIT goes through only on a fact that a passing CHECK wrote for that counter at its current version, CERTIFY only after a COMMIT, and anything else traps.
From a clean start, every certified run contains a passing CHECK, then a passing COMMIT of that same claim with the counter untouched in between, then CERTIFY (`earned_certification_provenance`).
On a run from a clean start, a fact whose counter hasn't been written since its check names a true claim about that counter (`checker_soundness`), and every fact in the table was written by a passing CHECK of exactly that claim.
From a clean start a certified run costs at least 3 (`certified_run_min_cost`), and 3 is reached.
The counter instructions are a two-counter machine, so it runs any two-counter program, and [EarnedCoreLinks.v](coq/kernel/foundation/EarnedCoreLinks.v) proves its halting problem undecidable from the vendored two-counter result.
Twenty-nine theorems, standard library only, each closed under the global context: `coqc minimal/EarnedCore.v`.
[minimal/UniversalThiele.v](minimal/UniversalThiele.v) builds a universal Thiele machine on it: one host runs any small-machine program as a guest, its mirror of the guest's flag always equals that flag (`record_agreement`), and the mirror rises only in a guest step that passed CERTIFY, charged in that same step, for every sequence of host moves (`no_free_host_certification_step`, `toll_enforced_by_host_step`); a machine from elsewhere enters through the two-counter encoding with its computation and toll kept but not its own prices.

Then it runs [minimal/nofi_demo.py](minimal/nofi_demo.py), which rebuilds the quantitative floor with none of my code anywhere near it.
The examples compare finite-map image sizes and query costs under explicit models; they do not measure physical erasure or derive the VM cost law from Landauer.
Binary search rides it at 100% efficiency, linear scan pays fifty times over for the same answer, and nothing beats it.
The number comes out identical whoever runs it.
That's the point of handing you a thing that runs instead of a thing to believe.

The full kernel includes these arguments, additional structural results, and the execution model.
MuCore's header maps each minimal theorem to its full-kernel counterpart.
The [Formal Spine](#formal-spine) table maps every load-bearing claim to its file.

The ordinary Python test gate also runs `scripts/comment_hygiene.py`.
It checks maintained project-owned comments across source, workflow, HDL, and documentation files for unfinished or historical review markers.
Generated and vendored surfaces are governed by their own generators and are not treated as maintained source.

## The argument, formally

1. **A local law constrains admissible executions.**
   The flip from uncertified to certified has to happen at some step, and wherever it happens, that step pays.
   For any `CertificationSystem`, A2 requires positive instruction cost on a false-to-true transition of its designated predicate.
   `universal_nfi_any_substrate` proves the corresponding trace-level floor.
   The state space and predicate are abstract; the VM's `vm_certified` field is one instance.
2. **Pricing adequacy can be characterized.**
   A2 sets a floor.
   It doesn't set a price list.
   `CommitmentPredicateAdequacy.v` proves which local charged-event predicates cover certification flips.
   Requiring both the floor and no overcharge *relative to flip count* characterizes exact unit event pricing.
   For a finite family of unit event floors, the least joint charge is one whenever any event fires.
   Several events can share that unit; independent coordinates alone do not force additive charges.
   This does not derive the choice of event or the entire VM cost schedule from A2.
3. **Selected projections lose relevant distinctions.**
   Two runs can look identical through a window and still need different answers.
   The receipt and separation theorems exhibit equal observations with different ledgers, certification values, or graph structure.
   No decoder of those observations can recover the differing property on every state.
   The general condition is exact: the query must be constant on each observation class.
   Given a representative of every class, that condition also constructs a decoder.
   It applies to arbitrary queries, including ones unrelated to certification.
4. **The construction supports further mathematics and implementations.**
   Fix the schedule and the starting value, and the books only balance one way.
   Ledger uniqueness follows for a fixed schedule and initial value.
   `thiele_trace_fold_initial` gives unique instruction-list evaluation from a chosen basepoint; evaluation defines a unique target value per reachable VM state exactly when equal VM outcomes give equal target outcomes.
   Constructing a reachable simulation also takes representative traces and certification agreement.
   An A2 target retaining full instruction history can fail this condition even when certification agrees exactly.
   Quantum certificate algebra, compiler results, and hardware commutation have their own explicit contracts.

The VM realizes these laws.
Generic `CERTIFY` sets a flag and charges for doing so; it checks no proposition.
`MORPH_ASSERT` checks morphism existence and uses property text as a checksum label; it does not interpret an arbitrary proposition or validate its certificate string.
`CHSH_LASSERT` has a separate soundness theorem for its restricted PSD test.
Payment and semantic truth must be assessed separately.
The small machine is the contrast: there CERTIFY needs a COMMIT, and a COMMIT needs a fact a passing CHECK wrote.

The mathematical [elliptope completion and gate](coq/kernel/quantum/ElliptopeGate.v) extend beyond the runtime check's fixed orthogonal slice.
The completion gate is not bound into the executable ISA.
The Coq hardware model has full-state trace commutation under `WFDrivenRun`, the preconditions of the actual executed run.
Generated RTL retains its named compiler/backend trust boundary.

## The verifier corollary

Two runs look the same to the checker, and only one of them paid.
For the selected strict-shadow transcript, that collision makes honest verification impossible.

A verifier whose transcript is `list StrictClassicalState`, the strict-shadow trace, cannot soundly decide a claim that depends on μ.
The two single-step witnesses from the Core Proof project to the same classical trace; one satisfies the μ=1 claim, one does not.
Soundness forces the claim to hold for every state that could explain the transcript, including the one where it fails.
Completeness forces acceptance on the honest run.
Both bars cannot be cleared.
The bare-setting impossibility is `bare_setting_no_sound_complete_verifier`, in [coq/VerifierImpossibility.v](coq/VerifierImpossibility.v).

Three sufficient evidence interfaces are formalized under their respective premises:

- **Substrate**: the transcript carries the full `VMState`; the verifier reads `vm_mu` directly. `substrate_escape_succeeds`, in [coq/VerifierEscape_Substrate.v](coq/VerifierEscape_Substrate.v).
- **Hardness, as a commitment contract**: the transcript carries a commitment bit, assumed to agree exactly with the claim for every explaining state. In a deployed system a signature and its hardness assumption would have to supply that contract; here it is assumed. `commitment_contract_verifier` constructs the verifier under it, in [coq/VerifierEscape_Hardness.v](coq/VerifierEscape_Hardness.v). It does not prove cryptographic security.
- **Interaction**: the verifier challenges the prover for a response that pins the claim. `interactive_escape_succeeds`, in [coq/VerifierEscape_Interaction.v](coq/VerifierEscape_Interaction.v).

The substrate channel is the option the structural axis makes available.
The other two are what classical cryptography and complexity already use.
The bottom of the three is `V_does_not_factor_through_classical` in [coq/VerifierExhaustiveness.v](coq/VerifierExhaustiveness.v).
Its exact scope matters: **given a transcript type whose classical projection collides two witnesses** (`proj t_A = proj t_B`, supplied as a hypothesis, with an explanation premise for each fixed VM witness), no sound + complete verifier on the μ-sensitive claim can be a function of that projection.
Where the collision exists, verification must access non-classical structure, and the three escapes are three concrete ways to expose it.

The collision is a hypothesis, not a conclusion: on a transcript rich enough to separate the witnesses it is unsatisfiable, and the statement is vacuous there.
So the three routes are pinned at the bottom *where the projection collides*, which is the case the argument is about.
"There is no fourth way" would be the informal reading of that, and it is not a theorem: nothing shows the three are the only sufficient interfaces.
Full meta-theoretic exhaustiveness, whether some list of routes partitions the space of non-classical structures, sits outside Coq's object-level type theory.
This file reduces that meta-question to the structural-enrichment question; it does not settle it, and the file header says so.

## Observation, enforcement, and representation

Enforcing a law, storing it, and seeing it are three different things.
A machine can enforce a rule in every step and still show you a window that hides the evidence.
Going the other way, having a ledger field doesn't prove every step keeps it right.
So every comparison here names the steps allowed, the window, and what you're trusting the implementation to do.

Even a reset can keep information around in a bigger state.
Record the previous state in a history list and each fixed-instruction step becomes injective.
So a program counter collapsing to one place doesn't prove anything was globally erased, and it doesn't give a physical heat bound.

Ordinary encodings can hold the full state, and a particular machine can enforce an invariant just by which transitions it allows.
Turing equivalence is about what can be computed.
It doesn't hand you this accounting discipline, and it doesn't forbid it either.
When this README says a ledgerless shadow, it means the specified window or fragment with those distinctions left out.

The concrete kernel lets some structural operations happen for free, alongside the paid events.
So it doesn't prove that every observable change costs something.
Its ledger starts at zero and adds up the declared schedule, and the certification operations carry mandatory positive floors.

## The Core Proof

Start from an empty VM and run one instruction.

| Program | Instruction | Cost | Final classical state | Final receipt |
|---|---:|---:|---|---|
| A | `CERTIFY 0` | `1` | empty memory, empty registers, `pc = 1` | certified, `mu = 1` |
| B | `PNEW [] 0` | `0` | empty memory, empty registers, `pc = 1` | uncertified, `mu = 0` |

The strict classical state is identical after both programs.
The receipt is not.
Therefore no function of `(memory, registers, pc)` can recover the receipt for all VM states.

Machine-checked anchors:

- [coq/ReceiptTheorem.v](coq/ReceiptTheorem.v) states the compact theorem.
- [coq/NecessityOfMuLedger.v](coq/NecessityOfMuLedger.v) contains the two-state separation and the stronger necessity results.
- [coq/kernel/foundation/VMStep.v](coq/kernel/foundation/VMStep.v) defines the instruction costs and single-step VM semantics.

## Proof Receipts At A Glance

The proof is meant to be checkable immediately. These are the small, concrete receipts behind the core claim.

The relevant cost clauses in [VMStep.v](coq/kernel/foundation/VMStep.v) are:

```text
instruction_cost (instr_pnew _ cost)                  = cost
instruction_cost (instr_lassert _ _ _ flen cost)      = flen * 8 + S cost
instruction_cost (instr_certify cost)                 = S cost
```

So the one-step witnesses are fixed by the kernel, not by prose:

```text
po1_instr_A  = instr_certify 0       ->  mu = 1, certified = true
po1_instr_B  = instr_pnew [] 0       ->  mu = 0, certified = false
strict_shadow po1_state_A = strict_shadow po1_state_B
```

The compact theorem is small enough to quote:

```coq
Theorem ReceiptTheorem :
  ~ exists f : StrictClassicalState -> nat,
      forall s : VMState, f (strict_shadow s) = s.(vm_mu).
```

The proof instantiates `f` at the two witness states.
Since their strict classical shadows are equal, `f` would have to return both `1` and `0` on the same input.
Coq closes the contradiction by `congruence`.

`Print Assumptions ReceiptTheorem` reports:

```text
Closed under the global context
```

The broader audit receipt [artifacts/print_assumptions_all_proofs.json](artifacts/print_assumptions_all_proofs.json) records 14,574 addressable theorems probed across 510 files and no user/project-local axiom findings in the committed assumption scan.

## Beyond the minimal witness

The minimal witness demonstrates a collision under a projection.
The abstract accounting theorem ranges over arbitrary state and instruction types, and pricing adequacy classifies local rules relative to the designated event.
The broader development also studies structural entitlement, graph operations, verifier interfaces, quantum certificate algebra, and realizations in software and hardware.

These results are reasons to keep studying the framework.
They don't make its modeling choices for it.
The verifier impossibility comes out of the observation collision.
The Python examples check finite combinatorial and algorithmic cases.
The CHSH soundness bridge adds more algebra.
Put together, they aren't an independent derivation of A2 from physics.

The pointer-observable models ask why some commitment events get recorded by other parties.
The models and their counterexamples are part of the research argument.
Consensus, exact observation, and a common coordinator-free update rule do not force permanence: two observers can agree while both track a bit that toggles (`toggle_game_refutes_strong_pointer_necessity`).
Adding durable views recovers permanence (`durable_consensus_implies_permanence`), but then persistence is an explicit premise.
Certification is one worked example, not an event selected by a necessity theorem.

## Formal Spine

These are the load-bearing formal claims.
The fourth column is the artifact that refutes the row, each one constructible in Coq or Python, no philosophy required.

| Claim | Meaning | Main proof files | Refute it |
|---|---|---|---|
| Minimal core | The core accounting claim in one self-contained file: A2, the cost floor, receipt separation, and the classical machine as the zero-cost fragment. Zero axioms, compiles in seconds. Run `make verify`. | [minimal/MuCore.v](minimal/MuCore.v) | An `f : shadow -> nat` with `f (strict_shadow s) = st_mu s` for all `s`; Coq accepts it where `no_mu_oracle` proves none exists. |
| Earned commitments | In the small machine, every certified run from a clean start passed a CHECK, then a COMMIT of the same claim with its counter untouched in between, then CERTIFY; it costs at least 3, and 3 is reached. | [minimal/EarnedCore.v](minimal/EarnedCore.v), [EarnedCoreLinks.v](coq/kernel/foundation/EarnedCoreLinks.v) | A clean-start trace that ends certified without a passing CHECK of the committed claim before its COMMIT; `earned_certification_provenance` falls. |
| Receipt theorem | `mu` is not determined by strict classical state. | [ReceiptTheorem.v](coq/ReceiptTheorem.v), [NecessityOfMuLedger.v](coq/NecessityOfMuLedger.v) | An `f : StrictClassicalState -> nat` with `f (strict_shadow s) = vm_mu s` for every `VMState`; `ReceiptTheorem` falls. |
| No Free Insight | Certification from an uncertified state requires positive `mu`. | [AbstractNoFI.v](coq/kernel/nfi/AbstractNoFI.v), [NoFreeInsight.v](coq/kernel/nfi/NoFreeInsight.v) | A VM step taking `vm_certified` false→true at instruction cost 0; `no_free_certification_certified` falls. |
| Universal cost floor | Any substrate with a cert-flip cost floor satisfies the same no-free-certification result. | [UniversalCertificationCost.v](coq/kernel/nfi/UniversalCertificationCost.v) | A `CertificationSystem` trace from uncertified to certified with `cs_total_cost = 0`; `universal_nfi_any_substrate` falls. |
| `mu` initiality | Any zero-starting, instruction-consistent ledger equals `mu` on reachable states. | [MuInitiality.v](coq/kernel/mu_calculus/MuInitiality.v) | A `CostFunctional` (zero-starting, instruction-consistent) differing from `mu` on a reachable state; `mu_is_universal` falls. |
| Honest cost tracking | A2 is a strict well-formedness condition: systems without it admit free certification. | [HonestCostTracking.v](coq/kernel/nfi/HonestCostTracking.v) | A `CertificationSystem` (A2 in scope) with a non-empty cert-flip trace at total cost 0, or a proof that every `CostBearingSystem` satisfies A2; `honest_cost_tracking_strict_restriction` falls either way. |
| Verification-cost separation | Slice coherence is checked by the kernel discipline; unconstrained traces require positional inspection. | [VerificationCostSeparation.v](coq/kernel/nfi/VerificationCostSeparation.v) | A correct `PositionalVerifier` for free-world traces that skips inspecting some cert position; `free_world_honesty_verifier_must_inspect_every_cert_position` falls. |
| `mu` hierarchy | Level-`k` certification requires at least `k` units of `mu`; no fixed budget covers every level. | [MuHierarchyTheorem.v](coq/kernel/mu_calculus/MuHierarchyTheorem.v) | A level-`k` certification trace with total `mu` < `k`; `level_k_certification_cost_floor` falls. |
| Structural advantage | The factored-SAT lower bound is proved for the non-adaptive model; the thermodynamic parsing gap is proved separately. | [NonAdaptiveLowerBound.v](coq/kernel/nfi/NonAdaptiveLowerBound.v), [ThermodynamicStructuralAdvantage.v](coq/kernel/nfi/ThermodynamicStructuralAdvantage.v) | A non-adaptive solver deciding the factored instance while probing fewer than `2^n` assignments; `non_adaptive_sat_lower_bound` falls. |
| Algebraic Tsirelson | The CHSH bound follows from rational polynomial constraints by Coq arithmetic. | [AlgebraicCoherence.v](coq/kernel/category/AlgebraicCoherence.v), [QuantumPartitionPSD.v](coq/kernel/quantum/QuantumPartitionPSD.v) | An `algebraically_coherent` correlator with `S² > 8`; `algebraically_coherent_tsirelson_general` falls. |
| Physics closure | Locality, `mu` monotonicity (mu never decreases under any step), causality, and discrete curvature identities are formalized as VM-level consequences or named bridges. The flat/vacuum EFE closure (`full_efe_uniform_two_vertex`) is a discrete-geometry identity (both sides vanish), not a derivation of general relativity. The curvature theorems are about partition graphs in general. On states the VM reaches, no two modules share an address, so no two are adjacent and no face-graph triangle exists (`reachable_no_adjacent_modules`), and calibration holds exactly when there are no modules (`reachable_calibrated_iff_no_modules`). | [PhysicsClosure.v](coq/kernel/curvature/PhysicsClosure.v), [EinsteinEmergence.v](coq/kernel/curvature/EinsteinEmergence.v), [PhysicsConditionalClosure.v](coq/PhysicsConditionalClosure.v) | A state `s` and instruction `i` with `(vm_apply s i)` paying less than `instruction_cost i` in `mu`, or a step writing outside its target module; `vm_apply_mu` (or the locality lemma) falls. |
| Intermediate hardware-model correspondence | The load-bearing theorem is [`driven_step_wf`](coq/kami_hw/GraphReconstructionBridge.v#L3746): for every instruction, the abstracted Kami hardware step equals `vm_apply` under `WFDrivenPrecondition`: `abs_full_snapshot (kami_step ks i) = vm_apply (abs_full_snapshot ks) i`, discharged by per-opcode lemmas. CHSH_LASSERT's Kami snapshot semantics inspect the same witness buckets through the same check function, matching VM-step exactly via `abs_phase1`. (The bookkeeping identity `37 + 10 + 0 = 47` is recorded separately as `rtl_inventory_arithmetic`; it is Peano arithmetic and proves nothing about opcodes, so cite `driven_step_wf`, not the partition.) | [GraphReconstructionBridge.v](coq/kami_hw/GraphReconstructionBridge.v#L3746), [coq/kami_hw](coq/kami_hw) | A cosim input on which synthesised RTL diverges from the Kami step for any synth-realised opcode (run `tests/test_verilog_cosim.py`); `rtl_step_correct` is violated empirically. |
| CHSH ↔ NPA-PSD bridge | A successful `CHSH_LASSERT` step entails the witness-derived NPA moment matrix is PSD. | [chsh_lassert_no_trap_implies_npa_psd](coq/kernel/quantum/QuantumPartitionPSD.v), [column_contractive_check_witness_sound](coq/kernel/nfi/MuLedgerQuantumBridge.v) | A successful `CHSH_LASSERT` step whose witness-derived moment matrix is not PSD; `chsh_lassert_no_trap_implies_npa_psd` falls. |
| Elliptope completion | The completion-based PSD correlator model (physical quantum identification uses external mathematics): every LHV correlator inside (deterministic + n-ary mixtures), Tsirelson `S² ≤ 8` for the whole set, PR box excluded, classical ⊂ elliptope strict. | [ElliptopeCompletion.v](coq/kernel/quantum/ElliptopeCompletion.v) | An elliptope-realizable tuple with `S² > 8` (`elliptope_tsirelson` falls), a sign pattern whose completed Gram form goes negative (`deterministic_strategy_elliptope` falls), or a PSD completion of the PR box (`pr_box_not_elliptope` falls). |
| Elliptope gate | Decidable Z-arithmetic membership check, two branches (fraction-free Sylvester for strict interior, rational LDL^T certificate reaching singular and boundary completions); passing provably entails elliptope membership; the µ=0 tightness witness, (1,0,1,0), and the on-Tsirelson-curve Pythagorean point (3/5,4/5,4/5,−3/5) accepted by computation; the PR box never accepted. | [ElliptopeGate.v](coq/kernel/quantum/ElliptopeGate.v) | Inputs making `elliptope_check_full` return true with correlators outside the set; `elliptope_check_full_sound` falls. |
| Pointer-observable criterion | Observer ecosystems, redundant records, and uniqueness relative to rivals, with five minimal model instances. A two-observer ecosystem proves that consensus, exact observation, and coordinator-free updates do not force the recorded event to be permanent. Event and observer choices are modeling inputs. | [PointerObservable.v](coq/kernel/frontier/PointerObservable.v), [EcosystemGame.v](coq/kernel/frontier/EcosystemGame.v) | Any necessity claim without a durability premise is refuted by `toggle_game_refutes_strong_pointer_necessity`; with durability added, persistence is built into the premise. |
| Counterexamples to stronger criteria | The adversarial search refutes implications from forgery resistance to metering or to record proliferation. The refutations rest on prose arguments about the real designs; the Coq models fix only the observer maps behind them. The public-record criterion is a proposal: public verifiability alone does not imply actual storage. | [PointerObservableCounterexamples.v](coq/kernel/frontier/PointerObservableCounterexamples.v) | Show a candidate's observer map is unfaithful to the real design in a way that changes its verdict; that candidate's refutation falls. |
| PoS finality reduction | Free finalization is the kernel's free forgery: a zero-stake-at-finalize gadget admits no A2 field, and any slashing gadget (finalize risks ≥ 1) pays the finality floor: `universal_nfi_any_substrate` instantiated. The gadget is a synthetic Boolean model, not a Casper accountable-safety model. | [PoSFinality.v](coq/kernel/reductions/PoSFinality.v) | A zero-stake-at-finalize gadget that admits an A2 proof, or a slashing gadget with a finalizing trace of total stake-at-risk 0; `nothing_at_stake_is_free_forgery` or `slashing_finality_floor` falls. |
| Gas-metering reduction | A gas schedule satisfies the commitment floor + no-overcharge iff its charging predicate is the commitment predicate with exact unit pricing; the kernel VM itself inhabits the class. The schedule is an abstract local charging law; no EVM opcode table is modeled. | [GasMetering.v](coq/kernel/reductions/GasMetering.v) | A `GasSchedule` satisfying floor + no-overcharge whose charge predicate differs from cert-flip on some reachable step; `gas_schedule_exactness` falls. |
| TEE attestation reduction | Sound+complete attestation of a μ-dependent claim cannot factor through the bare transcript; the replay shape is the two-preimage witness; exposing the measurement register restores a sound, complete verifier at the model's unit cost. The report is a transcript plus one number stipulated equal to μ; this is not a TEE security model. | [TEEAttestation.v](coq/kernel/reductions/TEEAttestation.v) | A sound+complete attestation verifier `V : TEEReport -> bool` with a proof of `factors_classical report_projection V`; `attestation_cannot_factor_through_bare_transcript` falls. |
| Transparency-log reduction | The CT design, read at one bit, is the commitment escape: log-backed transcripts admit a sound, complete, unit-cost verifier under the disclosure contract, while the log-free equivalent is impossible; a split view has the shape of the impossibility's witness pair. This is not an RFC or Merkle-security theorem. | [TransparencyLog.v](coq/kernel/reductions/TransparencyLog.v) | A sound+complete log-free (bare-transcript) verifier with the same soundness target; `abstract_bare_verifier_impossible` falls. |
| Proof-carrying reduction | Rounds restore sound, complete, unit-cost verification of the μ-claim; level-`k` certification costs ≥ `k` μ (events only, not gate counts or circuit size), with tightness witnessed. The certificate is one number stipulated equal to μ; no PCC checker is modeled. | [ProofCarryingVerifier.v](coq/kernel/reductions/ProofCarryingVerifier.v) | A level-`k` certified trace with total μ < `k`, or a sound+complete zero-round bare verifier; `level_k_verification_floor` or `bare_pcc_impossible` falls. |

The audited claim ledger is [coq/kernel/aggregators/MasterSummary.v](coq/kernel/aggregators/MasterSummary.v). It lists a selected set of established claims.
Its generated closure receipt is [artifacts/master_summary_open_obligations.json](artifacts/master_summary_open_obligations.json).

## Scope

| Result | Scope |
|---|---|
| Universal certification floor | Every system satisfying the specified A2 premise. |
| Exact event pricing | Relative to certification-flip count and the stated local-pricing interface. |
| Ledger uniqueness | Given the instruction schedule and zero initial value, on reachable states. |
| Trace-fold initiality | Unique evaluation of instruction lists; uniqueness of existing compatible state maps is separate. |
| Irrecoverability and verifier separation | For projections/transcripts that identify witnesses disagreeing on the queried property. |
| Quantum certificate soundness | Specified slice or completion PSD conditions; not physical entanglement generation. |
| Hardware trace commutation | The Coq hardware model under `WFDrivenRun`; downstream compiler/RTL trust is explicit. |
| Which narrowing is priced | On a finite machine that prices merges, the machine's own spread of possible states can't shrink for free (`run_narrowing_priced_log`). Observer knowledge need not be charged: `observer_narrowing_can_be_free` exhibits one admissible merge-priced cost assigning zero to an injective measurement, while wiping the record costs at least one (`wipe_costs_at_least_one`). Merge pricing is a lower bound and may overcharge injective steps. The insight No Free Insight prices is certified insight. What the run itself teaches, from the first look to the end, is also free (`demon_refutes_incremental`); the smallest machine that teaches for free has three states (`free_incremental_narrowing_with_three`, `no_free_incremental_narrowing_below_three`). |
| Recursion theorem | Proved for L, a Turing-complete lambda calculus, from its reduction rules (`second_recursion`), with Rice's theorem and halting as corollaries (`L_rice`, `L_halting_undecidable`). For the 12-instruction guest fragment, numeric decoding, fuel-bounded dispatch, agreement with actual VM execution, and semantic s-m-n specialization are proved (`g_decode_guest_code_roundtrip`, `g_eval_is_actual_vm_execution`, `g_smn`); the specialized program on any input is equivalent to the original on the fixed input. The guest also has its own recursion theorem (`vm_guest_recursion_theorem_closed`): every program transformer that a guest program computes on program codes has a fixed point `p` that matches `F p` in all four final registers and in `mu` on every input, and runs forever exactly when `F p` does. The evaluator in that proof runs as guest code: it is extracted to the lambda calculus L, compiled to a Minsky machine, and executed by the guest. For the full 51-opcode VM, a recursion theorem in the sense the bounded diagonal asks for, a fixed point for every map on programs up to equal thousand-step runs from every state, is false (`vm_full_recursion_premise_refuted`): that bounded property is decidable, and the flip of any correct decider for it has no such fixed point (`vm_correct_flip_has_no_fixed_point`). |
| Geometry | The curvature, angle-defect and Einstein-type theorems are about partition graphs in general. On every state the VM reaches, module regions are pairwise disjoint, so no two modules are adjacent, a well-formed triangulated reachable graph with F faces has no interior edge, 3F vertices, 3F edges and Euler characteristic F, the counts of F separate triangles (`reachable_triangulated_isolated`; one PNEW reaches such a graph, `reachable_triangulated_exists`), and calibration holds exactly when there are no modules (`reachable_calibrated_iff_no_modules`). |
| Structural uniqueness | False in the form the words suggest: a Thiele core that bills CPU time is adequate and runs the VM underneath, and it is not the same machine (`adequate_core_uniqueness_refuted`, `honest_vm_extension_uniqueness_refuted`). Up to the price schedule it holds for machines that run the VM and record certification (`cert_record_schedule_uniqueness_holds`); any state-dependent bill is just a schedule (`surcharged_core_equiv_mod_schedule`). Which permanent reading counts as the record is a second free choice (`tied_record_schedule_uniqueness_refuted`). Over any base, a record driven by the computation that never switches off is a latch on one event (`record_axis_is_latch_holds`); a revocable record is not (`toggle_not_latch`). |
| Physical interpretation | A closed two-state discrete master-equation protocol computes bath heat as `Delta / 2`. Choosing `Delta = 2 k_B T ln 2` gives the Landauer value, but changing only the gap changes the heat with identical population dynamics (`master_equation_does_not_fix_heat_scale`). The protocol is an exact calorimeter blueprint. Calibration of one μ to joules requires thermal-admissibility and device-correspondence premises. `landauer_dissipation_premises_inconsistent` separately proves that the full instruction set has no instance of the Landauer-dissipation premise pair. |

The classical embedding results describe the formal fragments and simulation contracts in their cited files.
Multiple preimages rule out recovering the original full state from the projection.
They do not rule out a section that chooses default metadata, or a different encoding that preserves the metadata.

## Exact scope

The central result is the record axis. A permanent record driven by a base
computation is a latch on an event; on finite hardware, writing it merges
states; and the VM's named projections do not recover it. Certification is one
instance of the event, not a uniquely selected one.

A finite monotone record decomposes into threshold latches, but not in general
into one latch. Revocable and probabilistic records do not inherit the same
uniqueness theorem. The guest VM has a direct Rice reduction, a verified
decoder and evaluator, semantic s-m-n specialization, and its own recursion
theorem, with the evaluator running as guest code. For the full VM, a fixed
point for every map on programs, up to equal thousand-step runs, is false:
the flip of any correct decider of the bounded shortcut property has none.
The two-state calorimeter protocol
fixes distributions, a Hamiltonian, a discrete master equation, and exact bath
heat, but also proves that those dynamics do not determine the energy gap.
The ledger therefore has no intrinsic joule value without thermal and device
premises.

The RFC 9162 verifier covers the iterative inclusion and consistency control
flow and executable examples, not collision resistance or signed-tree-head
authenticity. The PCC checker is a small role model, the RAM result covers
addressed list memory, the reversible-machine result covers arithmetic update
cores, and the TPM theorem is a countermodel to authenticity from an
unconstrained signature interface. None is presented as a complete deployed
security system. The graded, writer, potential, and linear-resource results
are comparisons, not full cost-framework embeddings.

The twelve-event observer-map survey proves its formal classifications and
the expected behavior under an event swap. Its MAC-labelled counterexample is
a fact about the chosen observer map; its real-system interpretation depends
on that modeling choice. More generally, a closed two-observer toggle game refutes the
claim that consensus, exact observation, and coordinator-free evolution force
permanent commits. Adding durable observation makes permanence immediate, so
it does not select certification independently. Five narrow real-system consequences reduce to known local
indistinguishability or durability arguments, while five stronger candidates
lack the required protocol or hardware semantics. None supplies a novel result
that both needs the record axis and is ready for external use. The pointer
criterion is a conjecture; its proposed strong necessity theorem is refuted.

## Architecture

This section is the build, not the model.
The core of the model fits in one short file, [minimal/MuCore.v](minimal/MuCore.v): a state, two toy instructions (store and certify), and the law.
None of the VM's 51 opcodes appear in it, and none appear in [minimal/EarnedCore.v](minimal/EarnedCore.v), the small machine with earned commitments.
The 51-opcode test bench has one semantics source and two execution paths:

```text
coq/kernel/foundation/VMStep.v
  -> coq/Extraction.v
     -> build/thiele_core.ml
        -> build/extracted_vm_runner
           -> thielecpu/vm.py

coq/kernel/foundation/VMStep.v
  -> coq/kami_hw/KamiExtraction.v
     -> build/kami_hw/mkModule1_synth.v
        -> thielecpu/hardware/rtl/thiele_cpu_kami.v
```

`thielecpu/vm.py` is a generated protocol layer.
The extracted OCaml runner and the Coq VM step are the normative software semantics.
The RTL path is generated from the same Coq/Kami source.

## Repository Layout

```text
minimal/                 standalone Coq files (MuCore, Napkin, EarnedCore, UniversalThiele) + clean-room demo
coq/                     Coq proof tree, extraction roots, theorem ledger
coq/kernel/              VM semantics, cost laws, NoFI, hierarchy, physics layers
coq/kami_hw/             Kami hardware model and RTL correspondence proofs
build/                   extracted OCaml artifacts and generated Kami outputs
thielecpu/               Python protocol layer and tracked RTL surface
examples/                assembly and Python examples
tests/                   parity, extraction, RTL, receipt, and regression tests
tools/                   verification and audit utilities
scripts/                 build, extraction, audit, and assembler scripts
artifacts/               committed receipts and generated audit outputs
monograph/               narrative monograph and mathematical specification
```

## Quick Start

Clone with the vendored Coq libraries.
The hardware-bridge proofs depend on **Kami** and **bbv**, which are git submodules.
Without them `make coq-gate` fails rather than skipping.

```bash
git clone --recurse-submodules https://github.com/sethirus/The-Thiele-Machine.git
# already cloned without --recurse-submodules:
git submodule update --init --recursive
```

Verify the core claim first (Coq 8.18+ and Python 3 only):

```bash
make verify
```

Then the full development environment:

```bash
python -m venv .venv
source .venv/bin/activate
pip install -r requirements.txt
pip install -e . --no-deps
make ocaml-runner
pytest -q
```

Full proof and hardware gates additionally need Coq 8.18+, OCaml with `ocamlfind`, and the RTL toolchain used by the target you run (`iverilog`, `verilator`, and/or `yosys`).
The exact versions are the ones CI earns its badges with: plain apt on `ubuntu-latest`, Ubuntu 24.04, which ships Coq 8.18.0.

```bash
sudo apt-get install -y coq coinor-csdp ocaml ocaml-findlib   # proof gates
sudo apt-get install -y libcoq-core-ocaml-dev libcoq-equations libstdlib-shims-ocaml-dev
bash scripts/install_metacoq.sh                                # MetaCoq 1.2.1 for the L extraction in VMGuestEvalL.v
sudo apt-get install -y iverilog verilator yosys              # RTL gates only
```

`coinor-csdp` is not garnish: the algebraic Tsirelson theorem closes its sum-of-squares certificate through `psatz`, and `psatz` asks CSDP for the certificate.

### Full proof build (the `coq-gate`)

The project uses native tools and repository sources.
Docker, container images, and a container daemon are not part of the build or review workflow.

For a complete source-only rebuild with dependency checking:

```bash
python3 scripts/reproduce_coq.py --jobs 1
```

This copies only source/configuration into a fresh directory under `artifacts/reproduction/`.
It builds the vendored bbv and Kami libraries plus the project, including the pinned MM2 dependency.
It runs the review probes and checks the selected compiled libraries with `coqchk`.
It records input hashes, native tool versions, commands, individual exit codes, and raw logs.
It does not install libraries globally or download anything.
The native prerequisites above must already be available; this is a source-contained project, not a bundled OS or compiler distribution.
See [native reproduction](docs/REPRODUCTION.md).

For incremental development in the checkout:

```bash
export COQPATH="$PWD/vendor/bbv/src:$PWD/vendor/kami"
make -C vendor/bbv
make -C vendor/kami
make coq-gate
```

`COQPATH` selects the repository libraries, so no global `make install` is needed.
`make verify` and `pytest` alone do not compile the full Coq corpus.

The CPU proofs are about the CPU's own Kami rules: executable semantics for all 12 rules, reset facts, and preservation of register names and kinds (`CoreRules`, `CoreExecution`, `CoreTyping`, `DispatchReset`); retirement of every admitted instruction against the Kami step (`admitted_retires`); and, from reset, runs of admitted instructions that keep the table invariants and match the Kami step run (`fsm_retirement_refinement`).
They exclude compiler semantic preservation and every step on which a CPU-only guard fires.
[Assurance and scope](docs/ASSURANCE.md) identifies each boundary.

The unbounded VM has a checked 122-instruction self-interpreter for twelve arithmetic and control instructions over four guest registers.
Program and input vary as executable data.
Its contracts cover positive host simulation, both directions of result correctness, malformed code, and divergence.
Guest structural fields remain unchanged.
[VM contracts](docs/VM_CONTRACTS.md) records the exact fragment and observations.

For that model, the checked Rice reduction proves undecidability for extensional predicates separating the divergent program from a well-formed program, including halting on zero and returning zero.
Guest-program deciders are covered.
The guest's internal recursion theorem is proved separately (`vm_guest_recursion_theorem_closed`).
Neither supplies the premise of the bounded diagonal for the full VM, and nothing can: asked for every map on programs, that premise is false (`vm_full_recursion_premise_refuted`).
[VM contracts](docs/VM_CONTRACTS.md) records the assumptions and checked results.

## Run A Program

Assemble and run through the extracted OCaml backend:

```bash
python scripts/thiele_asm.py examples/fibonacci.asm --run
```

Emit the trace format consumed by the extracted runner:

```bash
python scripts/thiele_asm.py examples/fibonacci.asm -o build/fibonacci.trace
./build/extracted_vm_runner build/fibonacci.trace
```

Run through the RTL simulation path when `iverilog` is available:

```bash
python scripts/thiele_asm.py examples/fibonacci.asm --sim
```

## Useful Make Targets

| Target | Purpose |
|---|---|
| `make verify` | One-command verification of the core claim (minimal Coq core + clean-room measurement). |
| `make ocaml-runner` | Rebuild the extracted OCaml runner. |
| `make test` | Run the pytest suite. |
| `make canonical-extract` | Rebuild canonical OCaml and Kami extraction artifacts. |
| `make canonical-e2e` | Run the extraction-to-RTL smoke pipeline. |
| `make rtl-synth` | Run Yosys synthesis and emit synthesis artifacts. |
| `make rtl-cosim` | Run RTL co-simulation tests. |
| `make rtl-verify` | Compile, synthesize, and co-simulate the RTL path. |
| `make proof-undeniable` | Run the stronger proof hygiene gate with `coqchk`. |
| `make closeout-gate` | Run the full repository closure gate. |

Use `make help` for the complete target list.

## Proof Hygiene

Two independent receipts track proof assumptions.

- [scripts/inquisitor.py](scripts/inquisitor.py) scans for proof-hygiene issues such as admitted proofs, undeclared axioms, vacuous theorem shapes, and circular claim patterns.
- [artifacts/print_assumptions_all_proofs.json](artifacts/print_assumptions_all_proofs.json) records Coq `Print Assumptions` over the audited theorem set.

The selected theorem ledger is [coq/kernel/aggregators/MasterSummary.v](coq/kernel/aggregators/MasterSummary.v).
The generated assumption receipt reports 14,574 addressable theorems probed across 510 files and no user/project-local axiom findings.
The split: 6,994 close under the global context outright, and the remaining 7,580 lean only on Coq-stdlib axiom families.
Those families are `functional_extensionality_dep` (7,270), `eq_rect_eq` (3,945), the classical-reals pair `sig_forall_dec` (1,168) and `sig_not_dec` (342), and `classic` (105).
Those families enter through the real-number and physics layers; the minimal core uses none of them.
"Zero axioms" here means zero project-local axioms, the same convention the monograph uses.
The receipt is what enforces that count.
A test ([tests/test_proof_hygiene_numbers.py](tests/test_proof_hygiene_numbers.py)) holds this paragraph to the committed artifact, number by number.

Run the hygiene pass directly:

```bash
python scripts/inquisitor.py
```

Run the stronger formal gate:

```bash
make proof-undeniable
```

## ISA Summary

The VM exposes 51 opcodes.
The CPU implements 47 of them.
The other four are the Q_{1+AB} forms of `CHSH_LASSERT` (`instr_chsh_lassert_1ab*`): the kernel, the extracted runner, the Python VM and `kami_step`, the Gallina model of the hardware step, all run them, and the CPU has no opcode for them.
They account for the parity tests' tolerated slack of 4 (the count is 37 + 10 + 0 = 47; `rtl_inventory_arithmetic` records that sum and checks no opcode).
The 47 CPU opcodes fall into six families.

| Family | Examples | Cost behavior |
|---|---|---|
| Partition and module structure | `PNEW`, `PSPLIT`, `PMERGE`, `PDISCOVER` | Programmer-declared, with zero-cost reversible structure supported by the model. |
| Logic and certification | `LASSERT`, `LJOIN`, `MDLACC` | `LASSERT` charges eight units per declared formula word plus the certification floor. |
| Memory, ALU, control flow | `LOAD`, `STORE`, `ADD`, `JUMP`, `HALT` | Classical compute surface. |
| Witness, tensor, cert flags | `CHSH_TRIAL`, `CERTIFY`, `REVEAL`, `TENSOR_SET`, `TENSOR_GET` | Certification/revelation instructions carry positive cost floors. |
| Categorical morphisms | `MORPH`, `COMPOSE`, `MORPH_ID`, `MORPH_ASSERT` | Morphism assertions are certification-bearing. |
| CHSH-aware certification | `CHSH_LASSERT` | Kernel-level column-contractivity check on `vm_witness` buckets. Decidable integer-arithmetic check; success ⇒ NPA-PSD via the bridge theorem [`chsh_lassert_no_trap_implies_npa_psd`](coq/kernel/quantum/QuantumPartitionPSD.v). Cost `S(mu_delta) ≥ 1` regardless of outcome (cert-setter discipline). |

Partition operations work on ranges of data memory.
PNEW claims a range, PSPLIT cuts a module's range at its middle, and PMERGE joins two ranges that touch.
Each traps instead (error flag set, program counter to the trap address, cost charged, graph unchanged) when the range runs past the 128-word data memory, overlaps a module without being that module's range, the two ranges don't touch, or the 64-slot module table has no free number; the CPU traps on the same conditions.
From a state with no modules, every reachable state keeps the regions pairwise disjoint, contiguous and inside memory, with every module number below 64 (`vm_reachable_partition_in_bounds`).
COMPOSE of two identity arrows stores an identity arrow (`graph_compose_identities_is_identity`), and composition of stored arrows is associative with identity arrows as units, up to equal endpoints, equal identity flags and equivalent couplings (`graph_compose_assoc_stored`, `graph_compose_left_identity_stored`, `graph_compose_right_identity_stored`).

The CPU is not the kernel at a different speed.
Its data words are 32 bits; the kernel's are 64.
Its ledger μ is a 32-bit register that wraps at 2^32; the kernel's μ is an unbounded natural number.
Each refinement theorem assumes the counters it touches fit in 32 bits (`cpu_preconditions` asks for μ below 2^31).
The CPU also checks things the kernel doesn't: that LOAD, STORE, their heap forms, CALL and RET stay inside the active module's range, that PDISCOVER's declared cost is at least its second operand, that μ stays at or above the tensor total, and the rich-format fields of the 128-bit instruction word.
On any of these it traps with a named error code, and the refinement theorems cover only steps on which none fires.

Single-step semantics live in [coq/kernel/foundation/VMStep.v](coq/kernel/foundation/VMStep.v).

## Hardware

The hardware is a check on the build. Each check below says what it compares, and nothing more.

- **Coq.** `driven_step_wf` and the retirement theorems above relate the Kami model of the CPU to `vm_apply`, under their stated premises.
- **Gate-level simulation of the exact board top** ([scripts/board_gls.py](scripts/board_gls.py), CI Full). The netlist the bitstream is built from (written back to Verilog and simulated with yosys's Xilinx cell models; block RAM through a pinned functional model checked against Xilinx UNISIM), the same board top as RTL, and the extracted VM run the same programs through the board pins: the program goes in over the serial line and the status report comes back on it. Gates are compared with RTL on the report bytes, the LEDs and every probed state field; RTL is compared with the VM on pc, μ, the error flag, the sixteen registers, the 128 data words, certification, the module table, the module counter, the morphism table, the witness counters and the logic accumulator. The RTL run also carries the formal property files as simulation checks and must reach every cover that is reachable from reset. Every program runs again with no reset press, the gates from their INIT values and the RTL from all zeros, and must end the same: the board wrapper holds the system in reset for its first sixteen CPU clock cycles after configuration. The programs are split over four shards, and a final job requires every shard and checks that all programs, comparisons and coverage targets are present. This is zero-delay simulation of the netlist before place and route, with behavioural models of the three Xilinx clock and buffer cells; it says nothing about timing or the analogue behaviour of the RAM.
- **SymbiYosys properties of the extracted CPU and loader** ([formal/](formal/), CI Full). Over every state reachable from reset. cpu_prove_pt: the module table stays within 64 slots, empty above the module counter, with every range inside the 128-word memory and the ranges pairwise disjoint; a partition trap goes to the trap vector and leaves the table unchanged; only PNEW, PSPLIT and PMERGE write it (321 mandatory induction obligations: reset, frame, bounds and trap, and every pair of slots; RAM reads are left arbitrary; the environment calls start only while the CPU is halted, which sys_prove proves of the loader). cpu_prove_ctrl (PDR): the error flag never clears except by reset and nothing executes after it is set, the morphism-table bounds hold, μ changes only when a charging rule fires, and halted clears only through start. sys_prove (k-induction with proved loader invariants; the depth bounds the induction search, not the executions covered): the loader starts the CPU only while it is halted, starts it at most once, loads nothing after the start, and sends one status report, only after a stop. cpu_cover and sys_cover: each property's trigger is reached by a real transition, within 16 cycles, from a state satisfying all the properties. μ never decreasing is not stated: the 32-bit register can wrap.
- **RTL/netlist equivalence** ([scripts/rtl_netlist_equiv.py](scripts/rtl_netlist_equiv.py), [formal/loader-equivalence.txt](formal/loader-equivalence.txt), CI Full). Board/loader equivalence, conditional on the CPU interface. For every finite execution from the specified power-on and reset state (a reset base case and an arbitrary inductive step, both mandatory), the board wrapper and loader in the bitstream netlist produce the same UART transmit line, the same four LEDs, the same CPU start and instruction-load enables, and the same connected instruction and address bus bits as their RTL, provided both sides receive the same seven CPU responses (pc, μ, the error, halted and certification flags, the error code, and instruction-load readiness). Equal responses are a condition of the result, not a proved property of the CPU. The CPU and its RAM are outside this comparison, and the clock cells are checked only for their types and divider ratio. Their integration is exercised by the gate-level simulation instead.
- **Timing.** nextpnr-xilinx reports that the CPU clock meets its 20 MHz target. That is a tool report, not vendor sign-off timing.

No physical board has run this design.

## Reading Path

| Document | Role |
|---|---|
| [THIELE_MACHINE.txt](THIELE_MACHINE.txt) | The model and the argument in plain text, no build details. Start here. |
| [monograph/monograph.pdf](monograph/monograph.pdf) | The monograph, in six parts after a short version: the picture, the axiom, the logic (Parts I to III, the abstract model only), the machine (the small machine first, then the 51-opcode test bench), the hardware, and how to check it and where it ends. Appendices hold the vocabulary, every assumption, what's mine and what isn't, the crosswalk from claims to Coq, and the CHSH derivation. |
| [monograph/thiele_machine_math_spec.tex](monograph/thiele_machine_math_spec.tex) | Mathematical specification. |
| [coq/kernel/aggregators/MasterSummary.v](coq/kernel/aggregators/MasterSummary.v) | Audited ledger of the selected established claim set. |
| [coq/README.md](coq/README.md) | Map of the active Coq proof tree. |
| [coq/PhysicsConditionalClosure.v](coq/PhysicsConditionalClosure.v) | VM accounting results and a conditional Tsirelson theorem from a full PSD completion. |
| [TECHNICAL_DISCLOSURE.md](TECHNICAL_DISCLOSURE.md) | Prior-art disclosure for the public technical concepts. |
| [PATENT_PLEDGE.md](PATENT_PLEDGE.md) | Non-assertion pledge for repository concepts. |

## IP And Prior Art

The software in this repository is Apache 2.0 licensed, including the license's patent grant for contributor-owned claims. [PATENT_PLEDGE.md](PATENT_PLEDGE.md) adds an explicit non-assertion commitment for the concepts in this repository.

[TECHNICAL_DISCLOSURE.md](TECHNICAL_DISCLOSURE.md) records the public prior-art surface for the core concepts: the `mu` ledger, No Free Insight, certification opcodes, partition state, witness counters, and the cross-layer proof-to-RTL pipeline.

## Citation

```bibtex
@misc{thielemachine2026,
  title        = {The Thiele Machine: A Computational Model with Explicit Structural Cost},
  author       = {Thiele, Devon},
  year         = {2026},
  version      = {3.3.0},
  doi          = {10.5281/zenodo.17316437},
  publisher    = {Zenodo},
  howpublished = {\url{https://doi.org/10.5281/zenodo.17316437}}
}
```

## Contact

To confirm, refute, build on, or point out what's wrong: thethielemachine@gmail.com, or open an issue at [github.com/sethirus/The-Thiele-Machine](https://github.com/sethirus/The-Thiele-Machine).
A submission that names a theorem gets, within 14 days, one of exactly two replies: "correct, fixing it," or the line where the construction fails.

The kernel's machine semantics (its opcodes, step relation, and cost law) define the machine studied here.
The elliptope gate, pointer-observable definitions, and selected model instances are characterization tiers over that semantics; they do not alter the step relation or cost law. The general pointer criterion is a conjecture.
Different machine semantics belong in separate repositories citing this one.

## License

The software is licensed Apache-2.0; see [LICENSE](LICENSE).
The monograph and distillation are licensed CC-BY-SA-4.0.
That split is intentional: the code carries a patent grant, and the writing carries share-alike.
