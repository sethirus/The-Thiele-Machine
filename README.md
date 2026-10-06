# The Thiele Machine

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.17316437.svg)](https://doi.org/10.5281/zenodo.17316437)
[![Latest release](https://img.shields.io/github/v/release/sethirus/The-Thiele-Machine?label=release)](https://github.com/sethirus/The-Thiele-Machine/releases/latest)
[![CI](https://github.com/sethirus/The-Thiele-Machine/actions/workflows/ci.yml/badge.svg)](https://github.com/sethirus/The-Thiele-Machine/actions/workflows/ci.yml)
[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)
[![Coq](https://img.shields.io/badge/Coq-0%20project--local%20axioms-EF4135?logo=coq&logoColor=white)](coq/)
[![Inquisitor](https://img.shields.io/badge/Inquisitor-0%20findings-brightgreen)](scripts/inquisitor.py)

**I didn't invent a machine. I found one.**

That is how I see this work.
I think there is structure here that the usual picture of computation leaves out.

**What the Thiele Machine is.**
It is an abstract model of computation.
It is a machine the way Turing's machine is a machine: mathematics you can reason about, not a device.
It is not a CPU.
It is not an instruction set, a VM, a graph, or category theory.
The model is small: a state, a step rule, a ledger that only climbs, a rule for which steps have to pay, and a window saying what an observer sees.
The event it accounts for happens on any computer, whether anybody keeps track of it or not.
Turing's model has no place for the record of that event and doesn't enforce one.
A Turing machine can be programmed to keep the record, and then it obeys the toll and is a Thiele machine; but when it runs another program's record as data on its tape, nothing in its own step enforces it.
The event's physical cost comes in only under Landauer's principle, as a named premise.
The record exists only if something keeps it, and keeping it, priced, is what the model adds: accounting, not computing power.

**Names.**
The Thiele Machine, with capitals, is the model and nothing else.
A Thiele machine, lower case, is any particular system proved to meet the model's definition (a certification system: states, moves, a step, a cost, a reading, and the toll), the way one rule table is a Turing machine.
A Thiele machine is weakly Thiele-complete when its base is Turing-universal.
That bar is nearly empty: a clock bolted to a computer clears it.
So Thiele-complete asks for four things ([minimal/ThieleComplete.v](minimal/ThieleComplete.v)): a universal base whose moves are free and can't touch the record; a record that rises only after a passing check of a claim, a commitment to that same claim with nothing it's about changed in between, and a certificate; an exact toll, one mark for each of those three acts and nothing for anything else; and a claim whose check could have failed.
Every clock-style machine fails that, whatever its record (`clock_not_thiele_complete`).
A universal Thiele machine is one fixed program that runs any machine of a stated class as a guest, with the guest's record earned again and its toll paid by the host's own steps.
One is proved here for the small machine's programs: U, a fixed program of 3728 instructions of the small machine's own six kinds ([UniversalRun.v](coq/kernel/foundation/UniversalRun.v)).

**What this repository is.**
It is an argument, made with that model, about what an account of computation should preserve.
The usual account describes a computation by what it reads and writes: memory, registers, where the program is.
I think that account is a shadow.
There is another axis: what the computation established, and what establishing it cost.

1. **The shadow loses something real.** Two runs can look identical through the usual window and still differ in what they established and paid. Proved, for every Thiele-complete machine and its own window ([ThieleCompleteWindow.v](minimal/ThieleCompleteWindow.v)).
2. **Establishing is not free.** If the step that turns uncertified into certified has to pay, every run from uncertified to certified has paid. Proved, for any system that follows that rule. The rule isn't arbitrary: on a machine with finite memory, a certificate that can never be revoked can only be switched on by a step that merges two states, and merging is what Landauer's principle charges for whenever the machine could be in either state. Proved in [PermanentCertification.v](coq/kernel/nfi/PermanentCertification.v), with Landauer's principle as the named premise. The heat comes from that uncertainty: a machine already known to be in one state loses nothing, and [PermanentCertificationEntropy.v](coq/kernel/nfi/PermanentCertificationEntropy.v) proves both sides. A finite machine with eight states meets both premises as theorems, not as a chosen rule ([FiniteCertMachine.v](coq/kernel/nfi/FiniteCertMachine.v)).
3. **Leaning on a fact takes a paid history.** A computation is entitled to lean on a structural fact when it holds the evidence and a history that earned it. Defined. On the small machine it is a theorem: a commitment goes through only on a fact a passing check wrote.
4. **So the axis belongs in the step.** Proposed. This is the conviction the proofs are there to test. Part of it is proved. An account that prices certification exactly, never less and never more, can't compute that price from a window that shows a step that certifies and a step that doesn't the same way ([ShadowPricing.v](coq/kernel/nfi/ShadowPricing.v)); every Thiele-complete machine has such a pair for its own window. The exact price needs the reading in the step. And on a machine with finite memory, an account that charges one unit for every halving of the number of distinct states (Landauer's principle in counting form) already charges every step that writes a permanent record at least the logarithm of how many states it squeezes together ([PermanentRecordPricing.v](coq/kernel/nfi/PermanentRecordPricing.v)). The same bound holds in bits of Shannon entropy, and for the uniform distribution on the m certified and k switching states, with Landauer's principle as a named premise, it is at least k_B T ln((m+k)/m) of heat ([PermanentCertificationEntropy.v](coq/kernel/nfi/PermanentCertificationEntropy.v)). Whether every account has to price merges is physics.
5. **Which events every account has to price.** Certification is the one I pinned down. On a finite machine the events that must be priced are the merges; every permanent-record write is one, and a flip escapes the price only when the same step can take it back. Proved, with Landauer's principle as the named premise. The guess that the priced events are exactly the permanent records is false; a three-state counterexample is in the same file. No theorem selects another universal class of priced events.
6. **What carries the weight.** Three results. Every machine can carry the record axis: take a Turing machine, a RAM, L, any deterministic machine, and any event it reaches, and the machine plus a latch on that event, charging one unit when the latch sets, is an honest extension of it ([`latch_core_honest`](coq/kernel/foundation/RecordAxisDiscrimination.v)). The record can't be read back off the shadow: every Thiele-complete machine hides its record and its ledger from its own window (`complete_hides_record`, `complete_hides_ledger`). And on a finite machine a step that writes a permanent record merges two states (`permanent_flip_is_not_injective`), so an account that prices merges already prices the write (`a2_from_merging_price_and_permanence`). Proved. The shape of the axis is close to definitional: a record that never switches off and is driven by the computation moves as a latch on one event (`record_axis_is_latch_holds`), and that follows from those two conditions in a few lines. The pointer question asks which event gets latched; no theorem here selects one uniquely.

The machine here is the small one, [minimal/EarnedCore.v](minimal/EarnedCore.v).
It earns its commitments: a commitment goes through only on a fact a passing check wrote, and every certification traces back to such a check.
It runs any two-counter program, so by Minsky's theorem (cited, not re-proved) it computes whatever a Turing machine computes, and it meets the four clauses: it is Thiele-complete (`earned_core_thiele_complete`).
It is there so the argument has something you can run and try to break.
It is a witness.
It is not the subject.

A computation gives you an answer.
What did it establish on the way there?
Which distinctions did it keep?
What did it cost to establish them?
I want those questions inside the mathematics, where somebody can take the argument apart and check it.

Certification is one point I could pin down.
There is more here than one point, and I am not done looking.
I pinned down the definitions, built a small machine that meets them, and made Coq check what happens when you throw some of that information away.

I call what remains a **shadow**.
For the projections in the proofs, the blindness is real: different executions become indistinguishable, and no clever decoder can recover a distinction the observation has erased.
Keep the full information in another encoding and you can recover it.
That makes the question sharper: what should an account of computation keep?

I think this reaches further than a useful accounting machine.
I think there is something foundational here.
That is my conviction, and the larger argument is still mine to earn.
The proofs already give you something concrete to challenge: accounting laws, pricing results, structural separation, certificate checks, and a machine you can run.

## Run it. Don't take my word.

I don't trust my own eye to catch a gap in an argument I want to believe, so I made Coq check the formal claims and built separate tests and audits for prose and artifacts.
You shouldn't trust me either.
Run it.

Coq 8.18+ and Python 3, clean checkout:

```bash
make verify        # about ten seconds
make verify-research  # observation policies and the window theorem
```

No Coq where you are?
Most review environments, laptops and LLM sandboxes alike have none, and the argument doesn't get to hide behind a toolchain.
There is a tier for that: Python's standard library and nothing else.

```bash
python3 minimal/nofi_demo.py   # exhaustive sweeps + measured algorithms against the cost floor; exits 0
python3 -c "import json; d=json.load(open('artifacts/print_assumptions_all_proofs.json')); print(d['summary'])"
```

The second command prints the assumption receipt: 5,369 theorems probed, zero *project-local* axiom findings.
The badge says project-local, and that is the precise claim: it is not "zero axioms".
4,882 of those theorems are closed under the global context outright; the remaining 487 use only Coq standard-library assumptions: dependent functional extensionality, `ClassicalDedekindReals.sig_not_dec`, `ClassicalDedekindReals.sig_forall_dec`, and `Classical_Prop.classic`.
Those library assumptions are disclosed in the receipt; what is zero is axioms this project added.
The receipt's counts are written by the receipt generator on Linux (`make assumption-receipt`, then `scripts/sync_assumption_receipt_readme.py`), never by hand.
Validate the committed receipt quickly with `make assumption-receipt-check`.
That path reuses the exact theorem/axiom results when the semantic fingerprint is unchanged and performs the full corpus derivation only after proof-relevant inputs drift.
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
The showcase check can fail, and a run whose check fails is refused forever (`earned_run_check_can_fail`, `earned_run_refused_forever`).
The counter instructions are a two-counter machine, so it runs any two-counter program, and [EarnedCoreLinks.v](coq/kernel/foundation/EarnedCoreLinks.v) proves its halting problem undecidable from the vendored two-counter result.
`coqc minimal/EarnedCore.v` checks it with the standard library only, every theorem closed under the global context.

[minimal/ThieleComplete.v](minimal/ThieleComplete.v) states what Thiele-complete means and proves the small machine meets it, and so does the same machine over any property with a proved checker, sorted lists included; every clock-style machine fails it.
[minimal/ThieleCompleteWindow.v](minimal/ThieleCompleteWindow.v) proves that every Thiele-complete machine hides its record and its ledger from its own window.
[minimal/UniversalThiele.v](minimal/UniversalThiele.v) builds a host that runs any small-machine program as a guest: its mirror of the guest's flag always equals that flag (`record_agreement`), and the mirror rises only in a guest step that passed CERTIFY, charged in that same step (`no_free_host_certification_step`).
The universal machine U goes further: one fixed program, with no guest step built into anything, runs every program of the small machine from every start ([UniversalRun.v](coq/kernel/foundation/UniversalRun.v)).
It halts exactly when its guest halts, with the guest's answer in its first two registers (`universal_halting`, `universal_output`).
Its flag goes up exactly when the guest's would, by its own check, its own commit and its own certificate (`universal_flag_iff`, `universal_earned`).
Its ledger is the guest's, mark for mark, wherever the two line up (`universal_ledger_exact`).
And the machine it runs on is Thiele-complete (`universal_thiele_complete`).

Then it runs [minimal/nofi_demo.py](minimal/nofi_demo.py), which rebuilds the quantitative floor with none of my code anywhere near it.
The examples compare finite-map image sizes and query costs under explicit models; they do not measure physical erasure or derive a cost law from Landauer.
Binary search rides it at 100% efficiency, linear scan pays fifty times over for the same answer, and nothing beats it.
The number comes out identical whoever runs it.
That's the point of handing you a thing that runs instead of a thing to believe.

The [Formal Spine](#formal-spine) table maps every load-bearing claim to its file.

The ordinary Python test gate also runs `scripts/comment_hygiene.py`.
It checks maintained project-owned comments across source, workflow, and documentation files for unfinished or historical review markers.
Generated and vendored surfaces are governed by their own generators and are not treated as maintained source.

## The argument, formally

1. **A local law constrains admissible executions.**
   The flip from uncertified to certified has to happen at some step, and wherever it happens, that step pays.
   For any `CertificationSystem`, A2 requires positive instruction cost on a false-to-true transition of its designated predicate.
   `universal_nfi_any_substrate` proves the corresponding trace-level floor.
   The state space and predicate are abstract; the small machine's certified flag is one instance (`earned_core_floor`).
2. **Pricing adequacy can be characterized.**
   A2 sets a floor.
   It doesn't set a price list.
   `CommitmentPredicateAdequacy.v` proves which local charged-event predicates cover certification flips.
   Requiring both the floor and no overcharge *relative to flip count* characterizes exact unit event pricing.
   For a finite family of unit event floors, the least joint charge is one whenever any event fires.
   Several events can share that unit; independent coordinates alone do not force additive charges.
   This does not derive the choice of event from A2.
3. **Selected projections lose relevant distinctions.**
   Two runs can look identical through a window and still need different answers.
   The window theorems exhibit equal observations with different ledgers and certification values.
   No decoder of those observations can recover the differing property on every state.
   The general condition is exact: the query must be constant on each observation class (`decoding_requires_fiber_constancy`).
   Given a representative of every class, that condition also constructs a decoder (`selected_representatives_give_decoder`).
   It applies to arbitrary queries, including ones unrelated to certification.
4. **A machine can earn what it certifies.**
   A2 prices the flip; it doesn't check what was certified.
   The small machine does: there CERTIFY needs a COMMIT, and a COMMIT needs a fact a passing CHECK wrote.
   Payment and semantic truth are still separate claims, and each has its own theorem.

## Observation, enforcement, and representation

Enforcing a law, storing it, and seeing it are three different things.
A machine can enforce a rule in every step and still show you a window that hides the evidence.
Going the other way, having a ledger field doesn't prove every step keeps it right.
So every comparison here names the steps allowed, the window, and what you're trusting the implementation to do.

Even a reset can keep information around in a bigger state.
Record the previous state in a history list and each fixed-instruction step becomes injective (`retained_history_step_injective`).
So a program counter collapsing to one place doesn't prove anything was globally erased, and it doesn't give a physical heat bound.

Ordinary encodings can hold the full state, and a particular machine can enforce an invariant just by which transitions it allows.
Turing equivalence is about what can be computed.
It doesn't hand you this accounting discipline, and it doesn't forbid it either.
When this README says a ledgerless shadow, it means the specified window or fragment with those distinctions left out.

The small machine lets its counter moves happen for free, alongside the paid events.
So it doesn't prove that every observable change costs something.
Its ledger starts where the run starts and adds up exactly one mark for each CHECK, COMMIT and CERTIFY.

## The Core Proof

Start from the empty state of [minimal/MuCore.v](minimal/MuCore.v) and run one instruction.
One run stores and leaves the bit alone; the other certifies.

The classical part, memory, registers and the program counter, is identical after both.
The receipt is not: one is certified with μ = 1, the other is not, with μ = 0 (`receipt_separation`).
Therefore no function of the classical part can recover μ for all states (`no_mu_oracle`), or the certified bit (`no_cert_oracle`).
The proof instantiates the would-be function at the two witness states.
Since their classical parts are equal, it would have to return two different answers on the same input.
Coq closes the contradiction.

`Print Assumptions no_mu_oracle` reports:

```text
Closed under the global context
```

The broader audit receipt [artifacts/print_assumptions_all_proofs.json](artifacts/print_assumptions_all_proofs.json) records 5,369 addressable theorems probed across 308 files and no user/project-local axiom findings in the committed assumption scan.

## Beyond the minimal witness

The minimal witness demonstrates a collision under a projection.
The abstract accounting theorem ranges over arbitrary state and instruction types, and pricing adequacy classifies local rules relative to the designated event.
The broader development also studies the record axis over any base, permanence and its price on finite machines, observer knowledge, quantum certificate algebra, and models of real systems.

These results are reasons to keep studying the framework.
They don't make its modeling choices for it.
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
| Thiele-complete | The four clauses: universal free base, earned record, exact toll, a check that can fail. The small machine, the generic machine and the sorted machine meet them; every clock machine fails them. | [minimal/ThieleComplete.v](minimal/ThieleComplete.v), [EarnedGenericLinks.v](coq/kernel/foundation/EarnedGenericLinks.v) | An interface for a clock machine meeting the four clauses (`clock_not_thiele_complete` falls), or a clean-start run of the small machine that certifies without its chain (`earned_core_thiele_complete` falls). |
| The window | Every Thiele-complete machine hides its record and its ledger from its own window: two runs agree on the window and differ on the record and the ledger. | [minimal/ThieleCompleteWindow.v](minimal/ThieleCompleteWindow.v) | A function of the window that returns the record on every state of a Thiele-complete machine; `complete_no_record_oracle` falls. |
| Universal Thiele machine | One fixed program U of 3728 instructions runs every small-machine program from every start: it halts exactly when the guest halts, with the same answer, the flag raised by its own earned chain, the guest's ledger mark for mark at matching points; its host is Thiele-complete and its halting problem is undecidable. | [UniversalRun.v](coq/kernel/foundation/UniversalRun.v), [UniversalInterpreterLinks.v](coq/kernel/foundation/UniversalInterpreterLinks.v) | A small-machine program and start where the guest halts and U doesn't, or the reverse; `universal_halting` falls. |
| Universal cost floor | Any substrate with a cert-flip cost floor satisfies the same no-free-certification result. | [UniversalCertificationCost.v](coq/kernel/nfi/UniversalCertificationCost.v) | A `CertificationSystem` trace from uncertified to certified with `cs_total_cost = 0`; `universal_nfi_any_substrate` falls. |
| Honest cost tracking | A2 is a strict well-formedness condition: systems without it admit free certification. | [HonestCostTracking.v](coq/kernel/nfi/HonestCostTracking.v) | A `CertificationSystem` (A2 in scope) with a non-empty cert-flip trace at total cost 0, or a proof that every `CostBearingSystem` satisfies A2; `honest_cost_tracking_strict_restriction` falls either way. |
| The toll from permanence | On a finite machine, a permanent certificate is switched on only by a merge, so merge pricing yields A2. | [PermanentCertification.v](coq/kernel/nfi/PermanentCertification.v), [PermanentRecordPricing.v](coq/kernel/nfi/PermanentRecordPricing.v) | A finite machine with a permanent reading switched on by an injective step; `permanent_flip_is_not_injective` falls. |
| Threshold floor | Certifying with a threshold of evidence K costs at least K when each step's cost bounds the evidence it adds. | [QuantitativeNoFI.v](coq/kernel/nfi/QuantitativeNoFI.v) | A `QuantitativeCertificationSystem` run from zero evidence to certified with total cost below the threshold; `universal_nfi_quantitative` falls. |
| The record axis | A record driven by the computation that never switches off is a latch on one event, over any base; every base carries one. | [StructuralRecordAxis.v](coq/kernel/foundation/StructuralRecordAxis.v), [RecordAxisDiscrimination.v](coq/kernel/foundation/RecordAxisDiscrimination.v) | An honest extension whose record is not a latch on any event; `record_axis_is_latch_holds` falls. |
| Shadow pricing | No account that prices from a window with a collision prices certification exactly; a window that shows the reading can. | [ShadowPricing.v](coq/kernel/nfi/ShadowPricing.v) | A shadow price meeting the floor and never overcharging on a window with a collision; `shadow_cannot_price_exactly` falls. |
| Which narrowing is priced | The machine's own spread can't shrink for free; an observer's knowledge can. | [KnowledgeNarrowing.v](coq/kernel/nfi/KnowledgeNarrowing.v) | A merge-priced run whose image shrinks by more than its cost allows; `run_narrowing_priced_log` falls. |
| Algebraic Tsirelson | The CHSH bound follows from rational polynomial constraints by Coq arithmetic. | [AlgebraicCoherence.v](coq/kernel/category/AlgebraicCoherence.v), [TsirelsonGeneral.v](coq/kernel/quantum/TsirelsonGeneral.v) | An `algebraically_coherent` correlator with `S² > 8`; `algebraically_coherent_tsirelson_general` falls. |
| CHSH integer check | An integer check on the eight trial counts entails that the counts' zero-marginal NPA moment matrix is PSD, hence the Tsirelson bound. | [CHSHColumnCheck.v](coq/kernel/quantum/CHSHColumnCheck.v) | Counts on which `column_contractive_check_witness` returns true while the moment matrix is not PSD; `column_contractive_check_witness_npa_psd` falls. |
| Elliptope completion | The completion-based PSD correlator model (physical quantum identification uses external mathematics): every LHV correlator inside (deterministic + n-ary mixtures), Tsirelson `S² ≤ 8` for the whole set, PR box excluded, classical ⊂ elliptope strict. | [ElliptopeCompletion.v](coq/kernel/quantum/ElliptopeCompletion.v) | An elliptope-realizable tuple with `S² > 8` (`elliptope_tsirelson` falls), a sign pattern whose completed Gram form goes negative (`deterministic_strategy_elliptope` falls), or a PSD completion of the PR box (`pr_box_not_elliptope` falls). |
| Elliptope gate | Decidable Z-arithmetic membership check, two branches (fraction-free Sylvester for strict interior, rational LDL^T certificate reaching singular and boundary completions); passing provably entails elliptope membership; the Pythagorean point (3/5,4/5,4/5,−3/5) on the Tsirelson curve accepted by computation; the PR box never accepted. | [ElliptopeGate.v](coq/kernel/quantum/ElliptopeGate.v) | Inputs making `elliptope_check_full` return true with correlators outside the set; `elliptope_check_full_sound` falls. |
| Pointer-observable criterion | Observer ecosystems, redundant records, and uniqueness relative to rivals, with five minimal model instances. A two-observer ecosystem proves that consensus, exact observation, and coordinator-free updates do not force the recorded event to be permanent. Event and observer choices are modeling inputs. | [PointerObservable.v](coq/kernel/frontier/PointerObservable.v), [EcosystemGame.v](coq/kernel/frontier/EcosystemGame.v) | Any necessity claim without a durability premise is refuted by `toggle_game_refutes_strong_pointer_necessity`; with durability added, persistence is built into the premise. |
| Counterexamples to stronger criteria | The adversarial search refutes implications from forgery resistance to metering or to record proliferation. The refutations rest on prose arguments about the real designs; the Coq models fix only the observer maps behind them. The public-record criterion is a proposal: public verifiability alone does not imply actual storage. | [PointerObservableCounterexamples.v](coq/kernel/frontier/PointerObservableCounterexamples.v) | Show a candidate's observer map is unfaithful to the real design in a way that changes its verdict; that candidate's refutation falls. |
| PoS finality reduction | Free finalization is free forgery: a zero-stake-at-finalize gadget admits no A2 field, and any slashing gadget (finalize risks ≥ 1) pays the finality floor: `universal_nfi_any_substrate` instantiated. The gadget is a synthetic Boolean model, not a Casper accountable-safety model. | [PoSFinality.v](coq/kernel/reductions/PoSFinality.v) | A zero-stake-at-finalize gadget that admits an A2 proof, or a slashing gadget with a finalizing trace of total stake-at-risk 0; `nothing_at_stake_is_free_forgery` or `slashing_finality_floor` falls. |
| Gas-metering reduction | A gas schedule satisfies the commitment floor + no-overcharge iff its charging predicate is the commitment predicate with exact unit pricing; a concrete schedule inhabits the class. The schedule is an abstract local charging law; no EVM opcode table is modeled. | [GasMetering.v](coq/kernel/reductions/GasMetering.v) | A `GasSchedule` satisfying floor + no-overcharge whose charge predicate differs from cert-flip on some reachable step; `gas_schedule_exactness` falls. |
| TPM quote | A function of the two-field modeled quote cannot decide a runtime label that was never measured into the PCRs; it decides any claim about the retained digest. A scoped abstraction of TPM quote fields, not a TPM security model. | [TPMQuoteGap.v](coq/kernel/reductions/TPMQuoteGap.v) | A decider on the modeled quote that returns the runtime label for every platform; `quote_cannot_attest_unmeasured_state` falls. |

## Scope

| Result | Scope |
|---|---|
| Universal certification floor | Every system satisfying the specified A2 premise. |
| Exact event pricing | Relative to certification-flip count and the stated local-pricing interface. |
| Thiele-completeness | The four clauses of `thiele_complete`, for the machines named in [ThieleComplete.v](minimal/ThieleComplete.v). The definition does not ask the checker to be computable. |
| The universal machine | Guests are small-machine programs started clean from `start x y`; the whole-run theorems are about loaded hosts. A guest with a different property language needs a different host property. |
| Irrecoverability | For projections and windows that identify witnesses disagreeing on the queried property. |
| Quantum certificate soundness | Specified slice or completion PSD conditions; not physical entanglement generation. |
| Which narrowing is priced | On a finite machine that prices merges, the machine's own spread of possible states can't shrink for free (`run_narrowing_priced_log`). Observer knowledge need not be charged: `observer_narrowing_can_be_free` exhibits one admissible merge-priced cost assigning zero to an injective measurement, while wiping the record costs at least one (`wipe_costs_at_least_one`). Merge pricing is a lower bound and may overcharge injective steps. The insight No Free Insight prices is certified insight. What the run itself teaches, from the first look to the end, is also free (`demon_refutes_incremental`); the smallest machine that teaches for free has three states (`free_incremental_narrowing_with_three`, `no_free_incremental_narrowing_below_three`). |
| Recursion theorem | Proved for L, a Turing-complete lambda calculus, from its reduction rules (`second_recursion`), with Rice's theorem and halting as corollaries (`L_rice`, `L_halting_undecidable`). The small machine's halting problem is undecidable (`earned_core_halting_undecidable`), and so is U's (`interp_halting_undecidable`). |
| Structural core | Over any base, a record driven by the computation that never switches off is a latch on one event (`record_axis_is_latch_holds`); a revocable record is not (`toggle_not_latch`). |
| Physical interpretation | A closed two-state discrete master-equation protocol computes bath heat as `Delta / 2`. Choosing `Delta = 2 k_B T ln 2` gives the Landauer value, but changing only the gap changes the heat with identical population dynamics (`master_equation_does_not_fix_heat_scale`). The protocol is an exact calorimeter blueprint. Calibration of one μ to joules requires thermal-admissibility and device-correspondence premises. |

The classical embedding results describe the formal fragments and simulation contracts in their cited files.
Multiple preimages rule out recovering the original full state from the projection.
They do not rule out a section that chooses default metadata, or a different encoding that preserves the metadata.

## Exact scope

The central result is the record axis. A permanent record driven by a base
computation is a latch on an event; on a finite machine, writing it merges
states; and a Thiele-complete machine's own window does not recover it.
Certification is one instance of the event, not a uniquely selected one.

A finite monotone record decomposes into threshold latches, but not in general
into one latch. Revocable and probabilistic records do not inherit the same
uniqueness theorem. The two-state calorimeter protocol
fixes distributions, a Hamiltonian, a discrete master equation, and exact bath
heat, but also proves that those dynamics do not determine the energy gap.
The ledger therefore has no intrinsic joule value without thermal and device
premises (`mu_has_no_intrinsic_joule_value`).

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

## Repository Layout

```text
minimal/                 the small machine and its standalone Coq files (MuCore, Napkin,
                         EarnedCore, EarnedGeneric, EarnedMulti, ThieleComplete,
                         ThieleCompleteWindow, UniversalThiele, UniversalCodes,
                         UniversalNoCopy) + the clean-room demo
coq/kernel/foundation/   record-carrying machines, the record axis, the Turing kernel,
                         L's recursion theorem, the universal machine U, and the Links
                         files that tie the small machine to the abstract results
coq/kernel/nfi/          certification systems, the universal floor, permanence and its
                         price, shadow pricing, narrowing, the threshold floor
coq/kernel/quantum/      CHSH algebra, the integer check, NPA, the elliptope
coq/kernel/frontier/     pointer observables, observation policy, the ecosystem game
coq/kernel/reductions/   models of real systems (Casper, RFC 9162, PCC, TPM, gas, RAM)
coq/kernel/thermodynamic/ the two-state calorimeter protocol
vendor/coq-undecidability/ the pinned undecidability library (Minsky machines, L)
scripts/                 build, audit, assumption-receipt and hygiene scripts
tests/                   proof-scope, citation, receipt, hook and model tests
artifacts/               committed receipts and generated audit outputs
monograph/               narrative monograph and mathematical specification
```

## Quick Start

Clone the repository.

```bash
git clone https://github.com/sethirus/The-Thiele-Machine.git
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
pytest -q
```

The full proof build needs Coq 8.18 with CSDP, and MetaCoq for the vendored L modules the build compiles.
The exact versions are the ones CI earns its badges with: plain apt on `ubuntu-latest`, Ubuntu 24.04, which ships Coq 8.18.0.

```bash
sudo apt-get install -y coq coinor-csdp ocaml ocaml-findlib
sudo apt-get install -y libcoq-core-ocaml-dev libcoq-equations libstdlib-shims-ocaml-dev
bash scripts/install_metacoq.sh                                # MetaCoq 1.2.1 for the vendored L modules
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
It builds the project, including the pinned undecidability modules it imports, and checks every compiled module with `coqchk`.
It records input hashes, native tool versions, commands, individual exit codes, and raw logs.
It does not install libraries globally or download anything.
The native prerequisites above must already be available; this is a source-contained project, not a bundled OS or compiler distribution.
See [native reproduction](docs/REPRODUCTION.md).

For incremental development in the checkout:

```bash
make coq-gate
```

`make verify` and `pytest` alone do not compile the full Coq corpus.

## Useful Make Targets

| Target | Purpose |
|---|---|
| `make verify` | One-command verification of the core claim (minimal Coq core + clean-room measurement). |
| `make test` | Run the pytest suite. |
| `make coq-gate` | Build every proof and fail on any `Admitted`. |
| `make proof-gate-repro` | Clean rebuild, zero-`Admitted` gate, and `coqchk` of every module. |
| `make proof-undeniable` | Run the stronger proof hygiene gate with the Inquisitor and `coqchk`. |
| `make assumption-receipt-check` | Validate the committed assumption receipt. |
| `make vacuity-audit` | Kernel-conversion vacuity gate over `scripts/vacuity_targets.json`. |

Use `make help` for the complete target list.

## Proof Hygiene

Two independent receipts track proof assumptions.

- [scripts/inquisitor.py](scripts/inquisitor.py) scans for proof-hygiene issues such as admitted proofs, undeclared axioms, vacuous theorem shapes, phantom imports, and circular claim patterns, and checks that every proof file connects to the foundation chain (the certification system, the record-carrying machine, the substrate, the Turing kernel, and the small machine) or says why it stands alone.
- [artifacts/print_assumptions_all_proofs.json](artifacts/print_assumptions_all_proofs.json) records Coq `Print Assumptions` over the audited theorem set.

The generated assumption receipt reports 5,369 addressable theorems probed across 308 files and no user/project-local axiom findings.
The split: 4,882 close under the global context outright, and the remaining 487 lean only on Coq-stdlib axiom families.
Those families are `functional_extensionality_dep` (460), `eq_rect_eq` (0), the classical-reals pair `sig_forall_dec` (487) and `sig_not_dec` (154), and `classic` (91).
Those families enter through the real-number layers; the minimal core uses none of them.
These counts are written by the receipt generator on Linux, never by hand.
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

## Reading Path

| Document | Role |
|---|---|
| [THIELE_MACHINE.txt](THIELE_MACHINE.txt) | The model and the argument in plain text, no build details. Start here. |
| [monograph/monograph.pdf](monograph/monograph.pdf) | The monograph: the picture, the axiom, the logic (the abstract model only), then the small machine, the universal machine, and how to check it and where it ends. Appendices hold the vocabulary, every assumption, what's mine and what isn't, the crosswalk from claims to Coq, and the CHSH derivation. |
| [monograph/thiele_machine_math_spec.tex](monograph/thiele_machine_math_spec.tex) | Mathematical specification. |
| [docs/THEOREM_MEANINGS.md](docs/THEOREM_MEANINGS.md) | What each theorem the book cites says, in plain words. |
| [docs/RESULTS.md](docs/RESULTS.md) | The settled questions and their exact statements. |
| [coq/README.md](coq/README.md) | Map of the active Coq proof tree. |
| [TECHNICAL_DISCLOSURE.md](TECHNICAL_DISCLOSURE.md) | Prior-art disclosure for the public technical concepts. |
| [PATENT_PLEDGE.md](PATENT_PLEDGE.md) | Non-assertion pledge for repository concepts. |

## IP And Prior Art

The software in this repository is Apache 2.0 licensed, including the license's patent grant for contributor-owned claims. [PATENT_PLEDGE.md](PATENT_PLEDGE.md) adds an explicit non-assertion commitment for the concepts in this repository.

[TECHNICAL_DISCLOSURE.md](TECHNICAL_DISCLOSURE.md) records the public prior-art surface for the core concepts: the `mu` ledger, No Free Insight, earned certification, and the record axis.
It also keeps the disclosure of the hardware embodiment (certification opcodes, partition state, witness counters and the proof-to-RTL pipeline), which is published at release v3.3.0 and its Zenodo version; that build is not in this tree.

## Citation

```bibtex
@misc{thielemachine2026,
  title        = {The Thiele Machine: A Computational Model with Explicit Structural Cost},
  author       = {Thiele, Devon},
  year         = {2026},
  version      = {4.0.0},
  doi          = {10.5281/zenodo.17316437},
  publisher    = {Zenodo},
  howpublished = {\url{https://doi.org/10.5281/zenodo.17316437}}
}
```

## Contact

To confirm, refute, build on, or point out what's wrong: thethielemachine@gmail.com, or open an issue at [github.com/sethirus/The-Thiele-Machine](https://github.com/sethirus/The-Thiele-Machine).
A submission that names a theorem gets, within 14 days, one of exactly two replies: "correct, fixing it," or the line where the construction fails.

The abstract model's definitions and the small machine's semantics define what is studied here.
The elliptope gate, pointer-observable definitions, and selected model instances are characterization tiers over that model; they do not alter it. The general pointer criterion is a conjecture.
Different machine semantics belong in separate repositories citing this one.

## License

The software is licensed Apache-2.0; see [LICENSE](LICENSE).
The monograph and distillation are licensed CC-BY-SA-4.0.
That split is intentional: the code carries a patent grant, and the writing carries share-alike.
