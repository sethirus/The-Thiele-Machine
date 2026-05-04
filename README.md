# The Thiele Machine

[![CI](https://github.com/sethirus/The-Thiele-Machine/actions/workflows/ci.yml/badge.svg)](https://github.com/sethirus/The-Thiele-Machine/actions/workflows/ci.yml)
[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)

**I claim every certified computation has a unique cost receipt that classical machine state cannot record. The instruction set forces the receipt. I did not choose it. Here is the proof. Twenty seconds.**

## What a computer's "state" means

Every model of a computer since the 1930s describes its state with three things:

- **memory.** What is stored.
- **registers.** What the processor is currently holding.
- **program counter.** Which instruction comes next.

Turing's machine. Von Neumann's architecture. Every CPU you have ever owned. They all agree: that trio is the state.

Here is the claim. Every certified computation has a cost receipt the trio cannot record. The instruction set forces the receipt. I did not choose it. The kernel calls the receipt **μ**.

## The proof

Run two short programs from a completely empty machine. Each runs for one instruction.

- **Program A: `CERTIFY 0`.** The instruction that stamps a result as certified. Cost: 1.
- **Program B: `PNEW [] 0`.** An instruction that does unrelated bookkeeping. Cost: 0.

Those costs are not arbitrary. The kernel's instruction-cost law fixes them in [coq/kernel/VMStep.v:202](coq/kernel/VMStep.v#L202), and [`mu_initiality`](coq/kernel/MuInitiality.v#L716) proves any honest accounting over this ISA lands on the same values. The receipt is forced, not chosen. Hold that. The next section uses it.

Look at the classical state each program leaves:

|                 | memory | registers | program counter |
|-----------------|--------|-----------|-----------------|
| after Program A | empty  | empty     | 1               |
| after Program B | empty  | empty     | 1               |

Identical.

Look at the rest of the facts about each resulting machine:

|                 | certified? | cost paid (μ) |
|-----------------|------------|---------------|
| after Program A | **yes**    | **1**         |
| after Program B | **no**     | **0**         |

Different.

Suppose a function `f(memory, registers, program counter)` returns whether the machine is certified. `f` would have to return **yes** when fed Program A's state and **no** when fed Program B's state. The two states are *the same input*. So `f` would have to give two different answers to one input.

There is no such function. ∎

Certification and μ are not in the classical state. They are forced by the trace, not derivable from where the trace ended.

> _The two final states are the kernel's `po1_state_A` and `po1_state_B` at [coq/NecessityOfMuLedger.v:299](coq/NecessityOfMuLedger.v#L299) and [coq/NecessityOfMuLedger.v:306](coq/NecessityOfMuLedger.v#L306). The full classical-vs-receipt contradiction is `po1_cond7_mu_contradiction_components` at [coq/NecessityOfMuLedger.v:454](coq/NecessityOfMuLedger.v#L454)._

## Why this isn't a tautology

The pushback to make. It is the right one:

> "You defined μ as separate from `(memory, registers, program counter)`, then proved it's separate. That's a 5th-wheel argument. You bolted a wheel to the roof, defined the car as four-wheels-on-the-ground, and proved your roof-wheel isn't a ground-wheel. You wrote the cost law. Coq just verified your axioms are consistent with themselves."

That objection works *only if μ is arbitrary*. Only if the cost law is one design choice among many I could equally have made. It isn't. The kernel forces the cost-law structure at three independent layers. None of them is my design preference.

### Layer 1: A2 is the minimal honest-accounting axiom (substrate-independent)

[`UniversalCertificationCost.v`](coq/kernel/UniversalCertificationCost.v) abstracts over everything (state type, instruction type, step function, cost function) and asks: what is the minimal premise under which "you cannot certify for free" holds?

Answer: **A2.** *"The step that flips an uncertified state to certified costs ≥ 1."* That single premise is enough. [`universal_nfi_any_substrate`](coq/kernel/UniversalCertificationCost.v#L108) proves any system, with any cost function, satisfying A2 has trace-cost ≥ 1 from any uncertified-to-certified trajectory.

[Lines 240–247](coq/kernel/UniversalCertificationCost.v#L240-L247) prove A2 cannot be weakened. Drop it. Allow `cs_cost i = 0` for a cert-flip step. Now the system has *free certification*. Running that one instruction certifies for nothing, total cost zero, theorem false. So A2 is **exactly the right minimal condition**, not a chosen one. Strengthen it and you exceed the minimum. Relax it and you no longer have honest accounting at all.

This argument never mentions the Thiele instruction set. It applies to any cost-tracking system on any substrate. I did not write A2. A2 is forced by what "honest" means for cost-bearing certification.

### Layer 2: The Thiele VM is the initial object in the category of cost machines

[`thiele_morphism_exists`](coq/kernel/UniversalCertificationCost.v#L411) and [`thiele_morphism_unique_on_traces`](coq/kernel/UniversalCertificationCost.v#L425) prove: in the category of `CertCostMachine` (Thiele instructions, A2-honoring step + cost + cert), the Thiele VM is initial. There is a unique cost-preserving simulation from Thiele into any other machine in the category, agreeing on reachable states.

Initiality is a categorical-canonicality result. It does not say I chose well. It says Thiele's vm_apply is the *defining* dynamics for this category. Any other cost machine over the same instructions either equals Thiele on reachable states or fails to be a CertCostMachine.

> _A fair Birkhoff-style critique. This initiality is **localized** to the Thiele instruction set. It is the canonical implementation of its own specification: the free algebra of the Thiele cost-machine signature, modulo A2. Not a claim that Thiele is canonical across all possible instruction sets. The claim that something like A2 is canonical across all instruction sets is Layer 1 above (`universal_nfi_any_substrate`), which is universal in the relevant sense and not subject to the Birkhoff trivialization. Layer 2 says: given the Thiele ISA, Thiele is the canonical implementation. Layer 1 says: across all ISAs, A2 is the minimal honest-accounting axiom. Both are true. Layer 1 is the load-bearing one._

### Layer 3: Specific cost values are forced by independent information bounds

Inside Thiele, the per-instruction cost values come from a mix of lower-bound proofs and explicit model choices grounded in standard physics. I'm going to be precise about which is which:

- **LASSERT.** ([`cost_uniqueness`](coq/kernel/MuCostDerivation.v#L493), [`cost_necessity`](coq/kernel/MuCostDerivation.v#L449)). The formula `flen * 8 + S(delta)` is provably the **minimum** of any implementation that simultaneously satisfies (a) the Shannon entropy reduction bound `log₂(Ω/Ω')` and (b) the description-complexity bound `semantic_complexity_bits(formula)`. Two independent lower bounds, both proven inside Coq. **This one is substantive. Not a tautology.**
- **CERTIFY.** ([`no_free_certification_certified`](coq/kernel/AbstractNoFI.v#L652)). Cost ≥ 1, discharging A2 directly. Substantive. A2 is forced by Layer 1.
- **PNEW / PSPLIT / PMERGE.** Zero cost in this model under **Bennett's reversible-computing principle** (Bennett 1973): reversible operations cost no energy, only time and trace-tape length, and can in principle be undone without dissipation. The Coq theorem [`partition_ops_zero_cost`](coq/kernel/MuCostDerivation.v#L234) confirms the cost model is internally consistent with this principle. It is essentially a definitional unfold (`reversible_info_cost := 0`) and does **not** independently prove physical reversibility. Whether these operations are physically reversible on real hardware is a model-design choice grounded in Bennett. Not a Coq derivation. I want that on the record.

`mu_initiality` then proves that within Thiele, μ is the unique zero-starting instruction-consistent monotone ledger over the cost law described above. The LASSERT and CERTIFY lower bounds are forced by independent information theory. The partition-zero-cost is a Bennett-grounded model choice. The kernel is precise about which is which.

### What about "I'll just put μ in memory"?

The most common technical rebuttal:

> *"A standard Turing machine can map μ to an address. Increment `MU_ADDR` on each cert-flip. Set `CERT_ADDR := true` on certify. Now `(memory, registers, pc)` differs between Program A and Program B because memory differs. Your projection theorem evaporates."*

That rebuttal **constructs a witness for the theorem. Not a counterexample to it.** A TM that increments `MU_ADDR` on every cert-flip and never decrements it satisfies A2 by construction. The cert-flip step costs ≥ 1 (the increment). It therefore *is* a `CertCostMachine` in the sense of [`UniversalCertificationCost.v`](coq/kernel/UniversalCertificationCost.v). [`universal_nfi_any_substrate`](coq/kernel/UniversalCertificationCost.v#L108) covers it. The Thiele VM is its initial simulation by [`thiele_morphism_exists`](coq/kernel/UniversalCertificationCost.v#L411).

I built the substrate-independent layer to absorb this rebuttal. Whatever you call your projection (tape contents, memory + registers + pc, anything excluding `MU_ADDR`), if your machine is honest about cost-tracking, it satisfies A2 and is covered. The only way to escape the universal theorem is to **drop A2.** Allow a cert-flip step at cost 0. That is free forgery. Not honest accounting. The system that allows it has *given up* certification, not refuted the theorem.

So "I'll put μ in memory" amounts to: admit μ is real state that has to live somewhere, pick memory as the place to put it, and don't notice that this concedes the entire claim.

### What μ tracks: irreversibility, not time

A follow-up attack:

> *"You allow PNEW/PSPLIT/PMERGE to cost 0. So I can encode a SAT search as 2^N reversible structural operations at cost 0, then call CERTIFY once at cost ≥ 1. You've built an adiabatic NP oracle that violates physical scaling laws."*

That isn't a violation. It's **Bennett's reversible computing** (Bennett 1973). Reversible computation **can** do arbitrary work at zero asymptotic *energy* cost. The resource paid is **time** (clock cycles) and **trace-tape length** (Bennett's "garbage tape"). Mainstream theoretical computer science since 1973. Not specific to this project.

What μ tracks is **irreversibility.** The bits whose erasure forces dissipation under Landauer's principle. Certification (CERTIFY, LASSERT) is irreversible. It commits to a claim, reducing the accessible state-space, and that bit-erasure is what pays μ. A reversible structural search is, by definition, not irreversible. So it doesn't pay μ. The cost model is working as designed. It is not a paradox.

Time complexity is a separate measure this model is silent on. The instruction count `length trace` is its own quantity, distinct from μ. A 2^N-step reversible search has μ ≈ O(M) but trace length 2^N. Both are real. Neither replaces the other. The Receipt Theorem is a statement about *certified entitlement*. Not about computation speed.

The "trace is a thermodynamic sink" half-truth. Yes, in Bennett's framework the instruction trace plays the role of the garbage tape that absorbs the entropy reversible operations would otherwise destroy. But the trace is the *history* of execution. It is not the *state at a moment*. The Receipt Theorem says μ is not a function of `(memory, registers, program counter)` *at any single moment*. It is recoverable from the trace by summing instruction costs. That's exactly what `trace_total_cost` is. These are consistent, not contradictory. The trace records cost. The state-at-a-moment does not. μ is the running summary of trace cost stored as state. Conflating "trace history" with "state at a moment" is what makes the paradox appear, and the conflation does not survive a careful read.

### What is and isn't forced

- **The cost-law structure** (monotone ledger, A2, instruction-summed cost): substrate-independent, forced. Not my choice. Theorem: `universal_nfi_any_substrate`.
- **The LASSERT and CERTIFY cost values:** forced by Shannon entropy reduction + description complexity (LASSERT) and A2 directly (CERTIFY). Both proven inside Coq as substantive lower-bound results. Theorems: `cost_uniqueness`, `no_free_certification_certified`.
- **The PNEW / PSPLIT / PMERGE cost = 0:** a model-design choice consistent with Bennett's reversible-computing principle (Bennett 1973). The Coq-level theorem `partition_ops_zero_cost` is a definitional unfold. Reversibility is the model assumption. Not a Coq derivation.
- **The numerical calibration to physical units** (Joules, kelvin, etc.): an *explicit named hypothesis* in [`NoFIToEinstein.v`](coq/kernel/NoFIToEinstein.v#L9-L12) (`mu_landauer_unruh_calibrated`). Not an axiom, not hidden. A bridge premise the document calls out by name.

Each layer is what it is. The substrate-independent layer and the LASSERT/CERTIFY lower bounds are substantive theorems. Partition-zero-cost is a Bennett-grounded model choice. Physical-unit calibration is a named bridge hypothesis. I am being honest about which is which.

## The same proof, machine-checked

The full file is at [coq/ReceiptTheorem.v](coq/ReceiptTheorem.v). Build it with `cd coq && make ReceiptTheorem.vo` against this repo's kernel.

```coq
From Kernel Require Import VMState VMStep.
Require Import NecessityOfMuLedger.

Theorem ReceiptTheorem :
  ~ exists f : StrictClassicalState -> nat,
      forall s : VMState, f (strict_shadow s) = s.(vm_mu).
Proof.
  intros [f Hf].
  pose proof (Hf po1_state_A) as HA.
  pose proof (Hf po1_state_B) as HB.
  rewrite po1_cond2_final_shadow_equal in HA.
  rewrite po1_cond4_trace_A_mu_paid in HA.
  rewrite po1_cond5_trace_B_mu_zero in HB.
  congruence.
Qed.

Print Assumptions ReceiptTheorem.
```

Coq's response:

```text
Closed under the global context
```

That is the strongest attestation Coq can give. The Receipt Theorem holds in pure constructive type theory. No excluded middle. No functional extensionality. No project-local axioms. Zero. The contradiction is forced by the kernel's three lemmas (`po1_cond2_final_shadow_equal`, `po1_cond4_trace_A_mu_paid`, `po1_cond5_trace_B_mu_zero` in [coq/NecessityOfMuLedger.v](coq/NecessityOfMuLedger.v)) and the definition of `strict_shadow`. Nothing else.

## The five formal claims

Every claim has a Coq theorem name, a file:line citation, and a precise falsification condition. To dismiss the project, you have to break at least one of them.

1. **μ is not classical.** No total function `(mem, regs, pc) → μ` exists for the Thiele VM. Theorem: `vm_mu_not_classically_determined`, [coq/NecessityOfMuLedger.v:511](coq/NecessityOfMuLedger.v#L511). *Falsify by:* defining a total function from `(mem, regs, pc)` that recovers `vm_mu` on every reachable state.

2. **μ is unique.** Any zero-starting, instruction-consistent, monotone cost ledger over the Thiele ISA equals μ on every reachable state. Theorem: `mu_initiality`, [coq/kernel/MuInitiality.v:716](coq/kernel/MuInitiality.v#L716). *Falsify by:* exhibiting a different zero-starting instruction-consistent monotone ledger that disagrees with μ on any reachable state.

3. **μ is necessary for certification.** Every trace that flips `vm_certified` from false to true has strictly increased μ. Theorem: `certification_requires_positive_mu`, [coq/kernel/AbstractNoFI.v:652](coq/kernel/AbstractNoFI.v#L652). *Falsify by:* a trace that ends certified with μ unchanged from the start.

4. **The structure is substrate-independent.** For *any* state, instruction, step, cost, and certification flag, if the cert-flip step costs ≥ 1, then any uncertified-to-certified trace pays ≥ 1 in total. The proof references no Thiele-specific structure and closes under the global context. Theorem: `universal_nfi_any_substrate`, [coq/kernel/UniversalCertificationCost.v:108](coq/kernel/UniversalCertificationCost.v#L108). *Falsify by:* finding any system on any substrate where the cert-flip step costs ≥ 1, but a multi-step uncertified-to-certified trace nonetheless costs 0.

5. **Thiele is initial in the category of cost machines.** Any honest cost-tracking machine over the Thiele instructions is a unique cost-preserving simulation of the Thiele VM, agreeing on reachable states. Theorems: `thiele_morphism_exists`, [coq/kernel/UniversalCertificationCost.v:411](coq/kernel/UniversalCertificationCost.v#L411); `thiele_morphism_unique_on_traces`, [coq/kernel/UniversalCertificationCost.v:425](coq/kernel/UniversalCertificationCost.v#L425). *Falsify by:* a `CertCostMachine` over the same instruction set that is not equal to Thiele on the reachable image of `vm_apply`.

The unique cost receipt of certified work is provably absent from classical machine state, canonically forced by what honest cost-accounting means at all, and instantiated by the Thiele VM as the initial member of the category.

## The Tsirelson result

A separately publishable result. The standard derivation of the quantum bound |S| ≤ 2√2 on CHSH correlations needs the global C\* algebra (Hilbert space, operator algebra, Born rule). Equivalently, the NPA-1 hierarchy condition that the 4×4 zero-marginal moment matrix is positive semi-definite (PSD).

This kernel proves the bound from a **strictly weaker** algebraic predicate, defined entirely in [coq/kernel/AlgebraicCoherence.v](coq/kernel/AlgebraicCoherence.v) without any operator-algebra import:

> A correlator (E00, E01, E10, E11) is **algebraically coherent** if |E_xy| ≤ 1 and four specific 3×3 principal minors are non-negative, given two existential rational parameters t, s.

That predicate is genuinely weaker than NPA-1. It admits 4×4 moment matrices that are *not* PSD. A hostile reviewer running scipy located such matrices: `[c, d, z, w, u, v] = [0.477, 0.477, -0.477, 0.477, 0.477, -0.477]` makes the four 3×3 minors evaluate to ≥ 0.1 while the full 4×4 determinant is ≈ −1.38. The predicate strictly relaxes the quantum constraint set.

The Tsirelson bound still holds on every algebraically coherent correlator:

```coq
Theorem algebraically_coherent_tsirelson_general :
  forall c : Correlators,
    algebraically_coherent c ->
    (S_from_correlators c) * (S_from_correlators c) <= 8.
```

Proof: degree-4 Positivstellensatz over ℚ via Coq's `psatz Q 4` tactic, finding a rational sum-of-squares certificate. No Hilbert space. No operator algebra. No quantum-mechanical postulate. Pure polynomial arithmetic on rational correlators. Theorem at [coq/kernel/AlgebraicCoherence.v:748](coq/kernel/AlgebraicCoherence.v#L748).

The bound is tight. The witness e = 7071/10000 achieves S = 28284/10000 ≈ 2.8284 and satisfies algebraic coherence. Theorem: [`tsirelson_bound_tight`](coq/kernel/AlgebraicCoherence.v#L723).

**Falsifying this:** find a correlator (E00, E01, E10, E11) over ℚ satisfying the four 3×3 minor conditions, with witnesses t, s, achieving S² > 8. Coq's `psatz Q 4` will fail to discharge `algebraically_coherent_tsirelson_general` and the proof will not compile.

## Current state

952 tests pass. Zero Admitted in the active proof tree. Zero Inquisitor findings. All 46 opcodes have formal hardware bisimulation proofs. 3,310 named theorems audited by Coq's own kernel. Zero project-local axioms.

If you have an hour and want the full claim ledger, read [OVERVIEW.md](OVERVIEW.md). Every assertion ties to a Coq theorem and a falsification condition.

## How to break this

Every claim has a concrete falsification condition. The main ones:

- **Falsify No Free Insight**: find a trace starting with `vm_certified = false`, `mu = 0`, ending with `vm_certified = true`, `mu = 0`. Add it as a Coq theorem. The proof of `certification_requires_positive_mu` won't compile.
- **Falsify ledger necessity**: define a total function from strict classical state `(mem, regs, pc)` that recovers `vm_mu` or `vm_certified` for every VM state. This contradicts `mu_ledger_necessity`, `vm_mu_not_classically_determined`, or `vm_certified_not_classically_determined`.
- **Falsify mu-monotonicity**: find a state `s` and instruction `i` where `(vm_apply s i).mu < s.mu`. `vm_apply_mu` fails.
- **Falsify categorical separation**: prove all states with identical classical shadow produce identical behavior. Contradicts `categorical_separation`.
- **Falsify the hardware bisimulation**: find an opcode where the Kami hardware step diverges from `vm_apply`. The bisimulation proof for that opcode won't close.
- **Run the gates**: `make closeout-gate`. If anything is wrong, it fails loudly.

If none of these can be done, the structure is doing what the proofs claim it is doing. If any of them can be done, this whole thing is wrong, and I want to know.

## The core idea

A Turing machine sees one tape cell at a time. It can compute over structured objects, but structure is not first-class state. If a graph decomposes into independent components, or two subproblems share no variables, the machine has no primitive way to know that. It has to compute its way to that knowledge, and it pays the same cost whether the structure was obvious or hard-won.

The Thiele Machine keeps the full classical compute surface and adds explicit structural state: a partition graph, certification channels, witness counters, a tensor layer, and the `mu` ledger. Programs can build and manipulate structure at zero cost. Certifying a structural claim is what costs. The design split is deliberate:

- structure creation can be cheap — even free
- certified structural entitlement is never free
- once a trace gains certified evidence, `mu` must have increased — proven, not assumed

That is what "No Free Insight" means. It is a machine-checked theorem, not a slogan.

## What the proofs establish

The Thiele Machine contains classical computation as a fragment and strictly extends it:

- every classical program embeds directly into the Thiele VM, leaving the structural layer untouched (`TuringClassicalEmbedding.v`, `ClassicalConservativity.v`)
- there exist Thiele states reachable by structural instructions that no classical trace can reach from the same start (`TuringStrictness.v`, `ShadowProjection.v`)
- `mu` is the unique canonical cost measure. Any other instruction-consistent, zero-starting, monotone functional equals `mu` on every reachable state (`MuInitiality.v`).
- the `mu` balance, certification flag, and partition graph are each provably independent of strict classical state `(mem, regs, pc)` and of each other. Five independence results, complete classification, from every reachable state, for any prefix computation of any length (`NecessityOfMuLedger.v`, `NecessityAbstract.v`).
- the `mu`-cost of any program is intrinsic to the instruction sequence. Any instruction-consistent accounting system starting at zero assigns exactly `trace_total_cost` to the result — the Turing machine was always paying this cost, silently, on every execution (`NecessityOfMuLedger.v` §7).
- certification requires positive `mu`, unconditionally, for both cert channels, over any trace of any length (`AbstractNoFI.v`, `NoFreeInsight.v`).
- classical projection loses morphism structure. Two states with identical registers, memory, mu, and PC can differ in ways no classical function can see (`PartitionSeparation.v`).
- the Tsirelson bound |S| ≤ 2√2 is proven by two independent routes: (1) from PSD of the zero-marginal NPA moment matrix (`MuLedgerQuantumBridge.v`), and (2) from algebraic conditions strictly weaker than NPA-1, by Positivstellensatz over ℚ (`AlgebraicCoherence.v`). See [The Tsirelson result](#the-tsirelson-result) section above for the witness coordinates and falsification condition.

Every claim in the short thesis has a Coq file and a falsification condition. The short thesis is the fastest route to the full claim ledger.

## Repository layout

```text
coq/                  proof tree, extraction roots, ThieleMachineComplete.v
build/                extracted OCaml artifacts, compiled runner, Kami outputs
thielecpu/            generated Python protocol layer, receipt helpers
thielecpu/hardware/rtl/  tracked RTL surface
tests/                parity, gate, fuzz, RTL, receipt, and regression tests
thesis/               long thesis, short thesis, math spec
tools/                TRS-1.0 verification tooling
scripts/              build and audit scripts
artifacts/            committed manifests and closeout audit outputs
```

## Ground truth chain

One semantics source, two execution paths:

```text
coq/kernel/VMStep.v
  -> coq/Extraction.v
     -> build/thiele_core.ml
        -> build/extracted_vm_runner      (OCaml)
           -> thielecpu/vm.py             (generated protocol layer)

coq/kernel/VMStep.v
  -> coq/kami_hw/KamiExtraction.v
     -> build/kami_hw/mkModule1_synth.v
        -> thielecpu/hardware/rtl/thiele_cpu_kami.v
```

`thielecpu/vm.py` is generated. It is not the normative semantics. The extracted OCaml runner is. `build/thiele_core.ml` and `build/thiele_core_complete.ml` are bit-for-bit identical — the CI checks this on every commit.

## Quick start

```bash
python -m venv .venv && source .venv/bin/activate
pip install -r requirements.txt && pip install -e . --no-deps
make ocaml-runner
pytest -q
```

Full proof and hardware gates also need: Coq 8.18+, OCaml with `ocamlfind`, `iverilog` and/or `verilator`, `yosys`.

## Run a program

Assemble and run through the extracted OCaml backend:

```bash
python scripts/thiele_asm.py examples/fibonacci.asm --run
```

Or emit the trace format the runner consumes directly:

```bash
python scripts/thiele_asm.py examples/fibonacci.asm -o build/fibonacci.trace
./build/extracted_vm_runner build/fibonacci.trace
```

Through the RTL path (needs iverilog):

```bash
python scripts/thiele_asm.py examples/fibonacci.asm --sim
```

## Key make targets

| Target | What it does |
|--------|-------------|
| `make ocaml-runner` | Rebuild the extracted OCaml runner from the current proof tree |
| `make canonical-extract` | Rebuild canonical OCaml and Kami extraction artifacts |
| `make canonical-e2e` | Full extraction → RTL → cosim → smoke pipeline |
| `make closeout-gate` | Full repository closeout gate (proof + extraction + tests + bitlock) |
| `make proof-undeniable` | Stronger gate: adds `coqchk` and bitlock checks |
| `make rtl-synth` | Yosys synthesis + circuit diagram (DOT/SVG in `artifacts/synthesis_gate/`) |
| `make rtl-cosim` | RTL co-simulation tests |
| `make rtl-verify` | Compile + synthesize + cosim in one shot |

`make help` for the full list.

## ISA

46 opcodes. Five families:

| Family | Opcodes | Cost floor |
|--------|---------|-----------|
| Partition and module structure | PNEW, PSPLIT, PMERGE, PDISCOVER | 0 (programmer-declared) |
| Logic and certification | LASSERT, LJOIN, MDLACC | LASSERT: `flen×8 + S(delta) ≥ 1` |
| Memory, ALU, control flow | LOAD, STORE, ADD, JUMP, HALT, ... | 0 |
| Witness, tensor, cert flags | CHSH_TRIAL, CERTIFY, REVEAL, TENSOR_SET/GET | CERTIFY/REVEAL: `S(delta) ≥ 1` |
| Categorical morphisms | MORPH, COMPOSE, MORPH_ID, MORPH_ASSERT, ... | MORPH_ASSERT: `S(delta) ≥ 1` always |

Single-step semantics: `coq/kernel/VMStep.v`. The CI checks that extraction and RTL stay aligned with that source.

## Thesis and specs

| Document | Path | What it is |
|----------|------|-----------|
| **Overview** | [`OVERVIEW.md`](OVERVIEW.md) | **One-hour foundational explanation, with every claim tied to a Coq theorem.** Start here. |
| Short thesis | `thesis/short_thesis.tex` / `.pdf` | The full informal argument with the Turing blind spot, CHSH, and physics bridges |
| Long thesis | `thesis/main.tex` / `.pdf` | Full 13-chapter narrative |
| Math spec | `thesis/thiele_machine_math_spec.tex` / `.pdf` | Complete mathematical specification |

`OVERVIEW.md` is the hour-long entry point. The short thesis is the deep informal argument. The math spec is the formal reference.

## Proof hygiene

Run the Inquisitor on demand:

```bash
python scripts/inquisitor.py
```

It writes `INQUISITOR_REPORT.md`. Zero HIGH/MEDIUM/LOW findings means the proof tree is clean. If that number is nonzero, something degraded.

TRS-1.0 receipts:

```bash
python tools/verify_trs10.py path/to/receipt.json --trusted-pubkey <32-byte-hex>
```

## Citation

```bibtex
@misc{thielemachine2026,
  title={The Thiele Machine: A Computational Model with Explicit Structural Cost},
  author={Thiele, Devon},
  year={2026},
  howpublished={\url{https://github.com/sethirus/The-Thiele-Machine}}
}
```

## Why I built this

I was trying to make a 3D renderer.

I had been reading about category theory and thought it was the right structure for a rendering pipeline that couldn't be wrong. January 2025, zero programming background. At 2:15 AM on January 22nd the morphisms were being applied correctly. That was supposed to be the end of the project.

Sixteen days in I realized the categorical framework I had built for rendering also ran Newtonian physics without any changes. I plugged Newton's laws into the same category structure and it ran. I didn't plan that. I discovered it.

I followed that thread for fifteen months. Rendering became physics became formal computation became Coq proofs became hardware. I didn't know what a Turing machine was when I started. I didn't know what Coq was. I learned each thing by needing it for the next step.

I used large language models throughout. The tool was useless for the first several months because nothing like this existed — no reference implementation, no prior work to hand it. I had to build all the context myself before it became useful. The ideas, the architecture, the math, the direction: mine. The proofs compile or they don't.

I don't have a CS degree. I don't have colleagues whose authority I can lean on. When I encounter a claim, I either find the proof or I don't believe it. That's not a methodology. It's how I think.

## IP and prior art

This work is published under Apache 2.0. The Apache license includes a patent grant (Section 3): any contributor grants users a perpetual, royalty-free patent license for their contributions.

**`PATENT_PLEDGE.md`** — explicit non-assertion commitment covering all concepts in this repository.

**`TECHNICAL_DISCLOSURE.md`** — structured prior art disclosure covering 12 core concepts (µ-ledger, No Free Insight, CERTIFY opcode, LASSERT dual-witness, partition graph as machine state, CHSH_TRIAL counters, three-layer isomorphism pipeline, and more). Published for indexing in IP.com and similar patent examiner databases. Every concept described there is prior art from the commit dates in this repository's public history.

## License

Apache 2.0. See [LICENSE](LICENSE).
