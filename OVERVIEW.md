# Overview: What the Thiele Machine Is

**A formal model of computation, with a working CPU implementation in real hardware, that proves every computation has a structural state dimension the Turing machine couldn't see, and exposes it as first-class machine state for the first time.**

This is the document to read if you have an hour and want to know what the project actually is, what's been proven, and why it might matter. Every claim in here has a Coq theorem behind it. Every claim that is not formally proven is marked as motivation, conditional, or consistency-only.

If you only have five minutes, read sections 1 and 9.
If you have ten, also read section 6.
If you have an hour, read all of it.

---

## 1. The one-sentence claim

Computation has a structural state dimension. It is the cost of producing certified knowledge, called μ. It is **provably not derivable** from any function on memory, registers, and program counter, **uniquely determined** by the instruction sequence, and **conserved** across every trace: certified results have a paid receipt, and there is no way around it.

The Thiele Machine is the first formal model and the first running CPU that exposes this dimension as first-class machine state. Until now, every model of computation we used (Turing machines, register machines, every CPU on Earth) silently flattened it.

---

## 2. What this is, and what it isn't

**This is:**
- A new computational model, formalized in Coq, with **3,310 machine-checked theorems** and **zero project-local axioms** (every assumption that survives in the dependency graph is a standard Coq library axiom; receipt pinned in `artifacts/print_assumptions_all_proofs.json`).
- A working CPU built from those proofs, generated through Kami (verified Coq → Verilog), running on FPGA, with formal bisimulation proofs for all 46 opcodes.
- A foundational claim: classical computer state is a strict projection of a richer state space, and information is provably lost in the projection.

**This is not:**
- A claim that Church-Turing is broken. Every Turing-computable function is Thiele-computable. Computability is preserved.
- A claim of solving P=NP, hypercomputation, or any other open problem.
- A new programming paradigm or "better" model. The classical model is correct in its regime.
- An interpretive philosophical position. Every load-bearing claim has a falsification condition, and the proofs compile or they don't.

The shape is the same shape relativity took on Newton: the older model is correct *in its regime* and *flattens a real dimension* the newer one exposes. Newton wasn't wrong; he was incomplete. Same here.

---

## 3. The Turing blind spot

The standard Turing machine state is `(memory, registers, program counter)`. Every CPU since the 1940s (x86, ARM, RISC-V, your laptop, your phone) inherits this shape. State is a snapshot of what's in memory, what's in registers, where the next instruction is.

This shape has a problem. It can describe *what* a computation does, but it cannot describe whether the computation has *certified* what it claims. A Turing trace that ends with the bit "1" on the tape is indistinguishable, by classical state, from a Turing trace that ends with "1" *and has actually proved something*. There's no field for "certified." There's no register that holds the cost of certification.

You can object: just add a register for it.

Here is the surprise. Adding a register doesn't help. **There is no total function from `(mem, regs, pc)` that recovers the cost of certification.** It is provably independent. You can't put it in a register and have the value stay correct under arbitrary computation. It has to be part of the state at the level of the machine model itself, not a derived quantity.

That's the gap. The Thiele Machine fills it.

---

## 4. The cost dimension

The Thiele Machine adds a quantity called **μ** (mu) to machine state. μ is a non-negative integer. It starts at zero. It never decreases. Every instruction either leaves μ unchanged or increases it by a precisely-defined amount specified in the cost model.

The central theorem: **certification requires positive μ.** If a trace begins with `vm_certified = false` and ends with `vm_certified = true`, then μ has strictly increased. There is no trace that goes from uncertified to certified without paying into the ledger. That is the *No Free Insight* theorem ([`coq/kernel/nfi/AbstractNoFI.v`](coq/kernel/nfi/AbstractNoFI.v), [`coq/kernel/nfi/NoFreeInsight.v`](coq/kernel/nfi/NoFreeInsight.v)).

Three further theorems make μ load-bearing rather than decorative:

- **Necessity** ([`coq/NecessityOfMuLedger.v`](coq/NecessityOfMuLedger.v)). Five independence results show that μ is not derivable from `(mem, regs, pc)` by any total function. It is irreducibly new state.
- **Initiality** ([`coq/kernel/mu_calculus/MuInitiality.v`](coq/kernel/mu_calculus/MuInitiality.v)). μ is the *unique* canonical cost measure inside Thiele. Any other instruction-consistent, zero-starting, monotone cost functional over the Thiele ISA equals μ on every reachable state.
- **Intrinsicness** ([`coq/NecessityOfMuLedger.v`](coq/NecessityOfMuLedger.v) §7). Every trace has a definite μ-cost, intrinsic to the instruction sequence. Any honest accounting that starts at zero arrives at the same answer.

Together: μ is real (not derivable from classical state), unique inside Thiele (no alternative cost measure over the Thiele ISA), and intrinsic (a property of the trace, not of the model that runs it).

I am going to be precise about what is forced and what is a model choice, so nothing is hiding:

- **A2 (cert step costs ≥ 1) and the monotone-ledger structure.** Forced by what "honest cost-accounting" means at all. See section 6.7 below: substrate-independent.
- **LASSERT and CERTIFY costs.** Forced by Shannon entropy reduction + description complexity (LASSERT) and A2 directly (CERTIFY). Both are substantive lower-bound proofs in [`coq/kernel/mu_calculus/MuCostDerivation.v`](coq/kernel/mu_calculus/MuCostDerivation.v) and [`coq/kernel/nfi/AbstractNoFI.v`](coq/kernel/nfi/AbstractNoFI.v).
- **PNEW / PSPLIT / PMERGE = 0.** A model-design choice consistent with **Bennett's reversible-computing principle** (Bennett 1973): reversible operations cost no energy, only time and trace-tape length. The Coq theorem [`partition_ops_zero_cost`](coq/kernel/mu_calculus/MuCostDerivation.v) confirms internal consistency. It is essentially a definitional unfold. Whether the operations are physically reversible is the model assumption, not a Coq derivation.
- **Numerical calibration to physical units (Joules, kelvin).** A named bridge hypothesis (`mu_landauer_unruh_calibrated` in [`coq/kernel/curvature/NoFIToEinstein.v`](coq/kernel/curvature/NoFIToEinstein.v)). Not an axiom, not hidden.

The implication is direct. Every Turing-machine trace running today has a definite, mathematically-determined μ-value. Most computations don't certify anything, and for them μ stays at zero. The Turing model is *correct* on those traces. But any computation that produces certified knowledge (any verifier, any compiler proving its own correctness, any test framework signing off on a result) has provably nonzero μ. The cost is being paid. Nobody has been counting.

---

## 5. What's in a Thiele Machine, beyond μ

Beyond μ, the Thiele Machine has additional structural state that the Turing model also lacks. Each axis is provably independent of classical state, so each is *real* state, not derived bookkeeping.

- **A partition graph** — explicit structural decomposition of the computation into independent regions and modules. The graph can be built and manipulated for free; only certified claims about the graph cost μ.
- **A certification flag** — `vm_certified : bool` — which can only flip from false to true with positive μ.
- **A categorical morphism table** — explicit morphism objects with provenance, which can be challenged via the `MORPH_ASSERT` opcode.
- **Witness counters** — including CHSH trial counters that track empirical evidence in 2-player games.
- **A tensor layer** — for multi-dimensional structural state.

The instruction set is 46 opcodes in five families:

| Family | Opcodes | Cost floor |
|---|---|---|
| Partition / module structure | PNEW, PSPLIT, PMERGE, PDISCOVER | 0 (programmer-declared) |
| Logic and certification | LASSERT, LJOIN, MDLACC | LASSERT: `flen×8 + S(delta) ≥ 1` |
| Memory, ALU, control flow | LOAD, STORE, ADD, JUMP, HALT, ... | 0 |
| Witness, tensor, cert flags | CHSH_TRIAL, CERTIFY, REVEAL, TENSOR_SET/GET | CERTIFY/REVEAL: `S(delta) ≥ 1` |
| Categorical morphisms | MORPH, COMPOSE, MORPH_ID, MORPH_ASSERT, ... | MORPH_ASSERT: `S(delta) ≥ 1` always |

The classical compute layer is preserved fully; structural operations are *added*, not *replaced*. Every classical program embeds directly into the Thiele VM ([`coq/kernel/foundation/TuringClassicalEmbedding.v`](coq/kernel/foundation/TuringClassicalEmbedding.v)) and leaves the structural layer untouched ([`coq/kernel/foundation/ClassicalConservativity.v`](coq/kernel/foundation/ClassicalConservativity.v)).

---

## 6. The core theorems, in plain language

Every theorem here is in the repository, machine-checked by Coq, with no project-local axioms.

### 6.1 No Free Insight
*You cannot get from uncertified to certified without paying μ.*

Any trace beginning with `vm_certified = false` and ending with `vm_certified = true` has strictly increased μ. ([`AbstractNoFI.v`](coq/kernel/nfi/AbstractNoFI.v), [`NoFreeInsight.v`](coq/kernel/nfi/NoFreeInsight.v))

This is the theorem that makes μ a *conservation law*. Every certified result has a paid receipt. The receipt cannot be forged. Any forgery would require a trace whose μ stayed at zero across a certification, and the proof of `certification_requires_positive_mu` would not compile.

### 6.2 μ-ledger necessity
*μ is provably not a function of classical state.*

There is no total function from `(mem, regs, pc)` that recovers `vm_mu` for every reachable VM state. ([`NecessityOfMuLedger.v`](coq/NecessityOfMuLedger.v), [`NecessityAbstract.v`](coq/kernel/nfi/NecessityAbstract.v))

This is the theorem that says μ isn't redundant bookkeeping. You cannot add μ to a Turing machine after the fact by computing it from existing state; it has to be part of the machine model.

### 6.3 μ-cost intrinsicness
*Every trace has a definite μ-cost, regardless of who runs it.*

Any cost measure that starts at zero and is instruction-consistent assigns exactly `trace_total_cost` on every result. ([`NecessityOfMuLedger.v`](coq/NecessityOfMuLedger.v) §7)

This is the theorem that says: the cost is a property of the trace itself, not of the machine doing the tracking. The Turing machine was always carrying a definite μ-value; it just wasn't reporting it.

### 6.4 μ-initiality
*μ is the unique canonical cost measure.*

Any instruction-consistent, zero-starting, monotone cost functional equals μ on every reachable state. ([`MuInitiality.v`](coq/kernel/mu_calculus/MuInitiality.v))

There is only one such measure. You cannot define a "competing" cost ledger that disagrees with μ. Any other measure satisfying the basic axioms is equal to it.

### 6.5 Categorical separation
*Two states with identical classical projection can differ.*

There exist VM states with identical `(mem, regs, mu, pc)` that differ in ways no classical function can detect. ([`PartitionSeparation.v`](coq/kernel/foundation/PartitionSeparation.v))

The classical projection is genuinely lossy. Thiele state is strictly richer.

### 6.6 Strict subsumption
*The Thiele Machine strictly contains the Turing Machine.*

Every classical/Turing program embeds into the Thiele VM ([`TuringClassicalEmbedding.v`](coq/kernel/foundation/TuringClassicalEmbedding.v), [`ClassicalConservativity.v`](coq/kernel/foundation/ClassicalConservativity.v)). And: there exist Thiele states reachable by structural instructions that no classical trace can reach ([`TuringStrictness.v`](coq/kernel/foundation/TuringStrictness.v), [`ShadowProjection.v`](coq/kernel/witness/ShadowProjection.v)).

Every Turing trace IS a Thiele trace, in the structurally trivial sector. The containment is strict. The Thiele Machine reaches states the Turing machine cannot.

### 6.7 Substrate-independent No Free Insight
*A2 is the minimal axiom for any honest cost-tracking system, on any substrate.*

[`UniversalCertificationCost.v`](coq/kernel/nfi/UniversalCertificationCost.v) abstracts over everything (state type, instruction type, step function, cost function) and proves: if the cert-flip step costs ≥ 1 (A2), then any uncertified-to-certified trace pays ≥ 1 in total. Theorem: [`universal_nfi_any_substrate`](coq/kernel/nfi/UniversalCertificationCost.v#L108).

A2 cannot be weakened. Drop it. Allow `cs_cost i = 0` for a cert-flip step. Now the system has free certification: one instruction certifies for nothing, total cost zero, theorem false. So A2 is exactly the right minimal condition. Strengthen it and you exceed the minimum. Relax it and you no longer have honest accounting at all.

This argument never mentions the Thiele instruction set. It applies to any cost-tracking system on any substrate. I did not write A2. A2 is forced by what "honest" means for cost-bearing certification. That makes the Thiele cost-law structure (monotone ledger, A2, instruction-summed cost) substrate-independent, not a design preference.

### 6.8 Thiele is initial in the category of cost machines
*Among honest cost machines over the Thiele instruction set, Thiele's vm_apply is canonical.*

Theorems: [`thiele_morphism_exists`](coq/kernel/nfi/UniversalCertificationCost.v#L411), [`thiele_morphism_unique_on_traces`](coq/kernel/nfi/UniversalCertificationCost.v#L425). In the category of `CertCostMachine` (Thiele instructions, A2-honoring step + cost + cert), the Thiele VM is initial. There is a unique cost-preserving simulation from Thiele into any other machine in the category, agreeing on reachable states.

Initiality is a categorical-canonicality result. It does not say I chose well. It says Thiele's vm_apply is the *defining* dynamics for this category. Any other cost machine over the same instructions either equals Thiele on reachable states or fails to be a CertCostMachine.

I want to flag the honest scope of this. Initiality is **localized** to the Thiele instruction set. It is the canonical implementation of its own specification (the free algebra of the Thiele cost-machine signature, modulo A2). The substrate-independent claim that *something* like A2 is canonical across all instruction sets is §6.7 above. Both are true. §6.7 is the load-bearing one for the broad story. §6.8 is the precise statement about the Thiele VM specifically.

### 6.9 The Tsirelson bound from cost algebra alone
*The famous CHSH quantum bound falls out of pure rational algebra, strictly weaker than NPA-1.*

The standard derivation of |S| ≤ 2√2 needs the global C\* algebra (Hilbert space, operator algebra, Born rule). Equivalently, NPA-1: the 4×4 zero-marginal moment matrix is positive semi-definite (PSD).

This kernel proves the bound from a **strictly weaker** algebraic predicate, defined entirely in [`AlgebraicCoherence.v`](coq/kernel/category/AlgebraicCoherence.v) without any operator-algebra import: the four 3×3 principal minors of a moment matrix are non-negative, given two existential rational parameters. That predicate admits 4×4 matrices that are not PSD. A hostile reviewer running scipy located such a matrix at `[c, d, z, w, u, v] = [0.477, 0.477, -0.477, 0.477, 0.477, -0.477]`: the four 3×3 minors evaluate to ≥ 0.1 while the full 4×4 determinant is ≈ −1.38. The predicate strictly relaxes the quantum constraint set.

The Tsirelson bound still holds. Theorem [`algebraically_coherent_tsirelson_general`](coq/kernel/category/AlgebraicCoherence.v#L748): for every algebraically coherent correlator, S² ≤ 8. Proof via degree-4 Positivstellensatz over ℚ (`psatz Q 4`). No Hilbert space. No operator algebra. No quantum-mechanical postulate. Pure polynomial arithmetic on rational correlators. The bound is tight: the witness e = 7071/10000 achieves S = 28284/10000 ≈ 2.8284 and satisfies algebraic coherence ([`tsirelson_bound_tight`](coq/kernel/category/AlgebraicCoherence.v#L723)).

This is a stand-alone result. Even if everything else in the project is wrong, the Tsirelson-from-rational-algebra theorem is a real new contribution to the foundations of quantum information. (Section 8 expands.)

### 6.10 Hardware bisimulation
*The hardware step is the proven step.*

All 46 opcodes have formal Kami bisimulation proofs against the Coq VM step function. The Kami output extracts to Verilog. The Verilog runs on FPGA. ([`coq/kami_hw/`](coq/kami_hw/))

The hardware doesn't simulate the proof. It *is* the proof.

---

### 6.11 Two rebuttals that come up most

I have spent a lot of time being argued with about this work, and these two pushbacks come up every time. Both look like they refute the central claim. Neither does.

#### "I'll just put μ in memory."

The pushback:

> *"A standard Turing machine can map μ to an address. Increment `MU_ADDR` on each cert-flip. Set `CERT_ADDR := true` on certify. Now `(memory, registers, pc)` differs between two such programs because memory differs. Your projection theorem evaporates."*

That rebuttal **constructs a witness for the theorem, not a counterexample to it.** A TM that increments `MU_ADDR` on every cert-flip and never decrements it satisfies A2 by construction. It is a `CertCostMachine` in the sense of [`UniversalCertificationCost.v`](coq/kernel/nfi/UniversalCertificationCost.v). [`universal_nfi_any_substrate`](coq/kernel/nfi/UniversalCertificationCost.v#L108) covers it. The Thiele VM is its initial simulation by [`thiele_morphism_exists`](coq/kernel/nfi/UniversalCertificationCost.v#L411).

I built the substrate-independent layer (§6.7) to absorb this rebuttal. Whatever you call your projection (tape contents, memory + registers + pc, anything excluding `MU_ADDR`), if your machine is honest about cost-tracking, it satisfies A2 and is covered. The only escape is to drop A2: allow a cert-flip step at cost 0. That is free forgery, not honest accounting.

So "I'll put μ in memory" amounts to: admit μ is real state that has to live somewhere, pick memory as the place to put it, and don't notice that this concedes the entire claim.

#### "You've built an adiabatic NP oracle."

The pushback:

> *"You allow PNEW/PSPLIT/PMERGE to cost 0. So I can encode a SAT search as 2^N reversible structural operations at cost 0, then call CERTIFY once at cost ≥ 1. You've broken physics."*

That isn't physics-broken. It's **Bennett's reversible computing** (Bennett 1973). Reversible computation **can** do arbitrary work at zero asymptotic *energy* cost. The resource paid is **time** (clock cycles) and **trace-tape length** (Bennett's "garbage tape"). Mainstream theoretical computer science since 1973.

What μ tracks is **irreversibility.** The bits whose erasure forces dissipation under Landauer's principle. Certification (CERTIFY, LASSERT) is irreversible: it commits to a claim, reducing the accessible state-space. That bit-erasure is what pays μ. A reversible structural search is not irreversible by itself, so it doesn't pay μ. The cost model is working as designed. Time complexity is a separate measure. The Receipt Theorem is a statement about *certified entitlement*, not computation speed.

Sub-pushback: "the trace becomes the thermodynamic sink." Yes. In Bennett's framework the instruction trace plays the role of the garbage tape that absorbs the entropy reversible operations would otherwise destroy. But the trace is the *history* of execution, not the *state at a moment*. The Receipt Theorem says μ is not a function of `(memory, registers, program counter)` *at any single moment*. It is recoverable from the trace by summing instruction costs (that is exactly what `trace_total_cost` is). Trace records cost. State-at-a-moment does not. μ is the running summary of trace cost stored as state. Conflating "trace history" with "state at a moment" is what makes the paradox appear, and the conflation does not survive a careful read.

---

## 7. The Newton → Einstein analogy, properly

This analogy is not decoration. It is structurally tight.

Newtonian mechanics says: a particle has a definite position and velocity at every time, and force equals mass times acceleration. This model is *correct in its regime*. At speeds far below light, in everyday gravitational fields, Newton's predictions match observation to extraordinary precision.

But Newton silently flattens real dimensions of physics:

- **Mass-energy equivalence.** Newton has mass; nothing converts to energy.
- **Time dilation.** Newton has absolute time.
- **Spacetime curvature.** Newton has flat 3D space.

These dimensions are not Newton's *failures*. They are *features of reality* that Newton's model doesn't include. General relativity exposes them. It does not invalidate Newton; it embeds Newton as the low-velocity limit. Every Newtonian particle is a relativistic particle traveling slowly enough that the relativistic corrections are negligible.

Now the parallel:

The Turing machine says: a computation has a definite memory, register, and program-counter state at every step, and the next state is determined by the instruction. This model is *correct in its regime*. For every classical algorithm, Turing's predictions match observation, and the model has been the foundation of computer science for nearly a century.

But Turing silently flattens real dimensions of computation:

- **Cost of certification (μ).** Turing has no field for "how much verification work has been done."
- **Structural state (partition graph).** Turing has no field for "how the computation decomposes."
- **Certification entitlement (cert flag).** Turing has no field for "is this result certified."
- **Categorical morphism state.** Turing has no field for "which morphisms have been applied with provenance."

These dimensions are not Turing's failures. They are *features of computation* that Turing's model doesn't include. The Thiele Machine exposes them. It does not invalidate Turing; it embeds Turing as the structurally-trivial sector. Every Turing trace is a Thiele trace running with μ-tracking off and the structural axes idle.

The parallel goes through cleanly because it isn't an analogy. It is the same logical move. A model that captures part of a phenomenon is generalized to a model that captures more of it. The smaller model is preserved as a limit. Information that the smaller model couldn't see becomes first-class.

---

## 8. The CHSH result, expanded

This deserves its own section because it is a separately publishable result inside the larger project.

The CHSH inequality is a fact about correlations between two observers measuring entangled particles. Classically, the CHSH expression is bounded by 2. Quantum mechanically, it's bounded by 2√2: the **Tsirelson bound**. This is famously a quantum-mechanical fact, derived from operator algebras, Hilbert space, the Born rule, and the structure of quantum states.

The Thiele Machine has a 2-player CHSH game built into it. The honesty condition for the game (what it means for the players to be accurately accounting their μ-cost) turns out to be **exactly equivalent** to the polynomial constraint system from quantum information theory: positive semidefiniteness of the NPA moment matrix for zero-marginal correlations.

Formally: `column_contractive_iff_quantum_realizable` ([`QuantumPartitionPSD.v:227`](coq/kernel/quantum/QuantumPartitionPSD.v)), a biconditional with zero project-local axioms. The Tsirelson bound is then derived two independent ways:

1. From PSD of the zero-marginal NPA moment matrix via `npa_psd_iff_column_contractive` ([`QuantumPartitionPSD.v:183`](coq/kernel/quantum/QuantumPartitionPSD.v)) and the μ-ledger ↔ quantum bridge ([`MuLedgerQuantumBridge.v`](coq/kernel/nfi/MuLedgerQuantumBridge.v)). Uses quantum-information machinery, but no physics axioms.
2. From algebraic coherence alone via a Positivstellensatz Sum-of-Squares certificate ([`AlgebraicCoherence.v`](coq/kernel/category/AlgebraicCoherence.v)). Pure polynomial arithmetic. No quantum-information machinery either.

Read straight: **the famous quantum bound on correlations falls out of pure cost-algebra constraints. No Hilbert space. No Born rule. No quantum mechanics input. Just the algebra of an honest cost ledger.**

The implication is foundational. The Tsirelson bound has been understood as a consequence of *quantum mechanics*. This proof shows it has a purely combinatorial / cost-theoretic provenance, one level deeper than QM. The audience for this is the QIP / TQC / QPL community, the NPA hierarchy people, anyone working on the foundations of quantum nonlocality. It can be published as a 4-page note independently of whether the rest of the Thiele framework is accepted.

---

## 9. From Coq to FPGA

The Thiele Machine is not just a paper machine. There is a working CPU.

The pipeline:

```
coq/kernel/foundation/VMStep.v                       (one normative semantics, in Coq)
   │
   ├─→ coq/Extraction.v                   (extract to OCaml)
   │      └─→ build/extracted_vm_runner   (running OCaml CPU)
   │
   └─→ coq/kami_hw/KamiExtraction.v       (extract to verified RTL via Kami)
          └─→ build/kami_hw/mkModule1_synth.v
                 └─→ thielecpu/hardware/rtl/thiele_cpu_kami.v   (synthesizable Verilog)
                        └─→ FPGA bitstream
```

There is one normative semantics: `vm_step` in Coq. Both execution paths (OCaml runner, Verilog hardware) are *extracted* from that source. The OCaml extraction is bit-for-bit deterministic and CI-checked. The Kami → Verilog path passes through 46 formal bisimulation proofs, one per opcode. The hardware step matches the Coq step exactly.

Most "verified hardware" projects verify either RTL against a hardware spec or compiler against a software spec. Pick one. Few do both, with the same semantics generating both software and hardware, with proofs along both paths, with a single source of truth. The Thiele repo does this for all 46 opcodes.

Practical implication: when you run an example program through `make canonical-e2e`, the hardware execution is mathematically identical to the Coq execution. Not "morally equivalent" or "equivalent up to abstraction" — *identical*, by 46 Qed-closed bisimulation theorems.

---

## 10. How to falsify any of this

Every load-bearing claim has a concrete, executable falsification condition. If anyone constructs any of them, the corresponding theorem fails to compile, and the structural claim collapses.

- **Falsify No Free Insight.** Find a Thiele trace where `vm_certified = false`, `mu = 0` at the start, `vm_certified = true`, `mu = 0` at the end. Encode it as a Coq term. The proof of `certification_requires_positive_mu` will fail.
- **Falsify ledger necessity.** Define a total function `f : (mem × regs × pc) → mu_value` that recovers `vm_mu` for every reachable VM state. This contradicts `mu_ledger_necessity`, `vm_mu_not_classically_determined`, or `vm_certified_not_classically_determined`.
- **Falsify monotonicity.** Find a state `s` and an instruction `i` such that `(vm_apply s i).mu < s.mu`. The lemma `vm_apply_mu` will fail.
- **Falsify categorical separation.** Prove that any two states with identical classical shadow produce identical behavior. This contradicts `categorical_separation`.
- **Falsify the hardware bisimulation.** Find an opcode where the Kami hardware step diverges from `vm_apply` for some state. The bisimulation proof for that opcode will fail.
- **Falsify the Tsirelson cost-algebra result.** Construct values satisfying the cost-algebra axioms whose CHSH expression exceeds 2√2. The Positivstellensatz certificate in `AlgebraicCoherence.v` will fail.
- **Run the gates.** `make closeout-gate`. Anything broken fails loudly.

These are not optional. They are how the project is meant to be checked. If none of them can be done, the structural claims are doing what the proofs say. If any of them can be done, that's a publishable counterexample. File an issue.

---

## 11. The audit

A separate question from "are the proofs internally consistent" is "what assumptions do the proofs rest on." Coq proofs always rest on *some* assumptions, at minimum the type theory of Coq itself.

The Thiele Machine corpus has been audited at full repo scope using Coq's own kernel via `Print Assumptions`, an independent mechanism from any internal hygiene tool.

Result, for **every named theorem in every proof file the project produced** (3,310 theorems across 205 files):

- **Zero project-local axioms.** No `Axiom` or `Parameter` declared by the project survives in the dependency tree of any theorem.
- **Zero admits.** No `Admitted.` proofs.
- **Four standard mathematical assumptions used,** all from Coq's standard library:
  - `ClassicalDedekindReals.sig_forall_dec` — real-number decidability — 734 theorems
  - `FunctionalExtensionality.functional_extensionality_dep` — functional extensionality — 706 theorems
  - `ClassicalDedekindReals.sig_not_dec` — real-number decidability — 216 theorems
  - `Classical_Prop.classic` — excluded middle — exactly **25** theorems (their names are listed in the receipt)
- **2,539 theorems** (76.7%) are `Closed under the global context`. They depend on **zero** axioms beyond Coq's type theory itself.

The receipts:
- [`artifacts/print_assumptions_all_proofs.txt`](artifacts/print_assumptions_all_proofs.txt) — raw coqc output
- [`artifacts/print_assumptions_all_proofs.json`](artifacts/print_assumptions_all_proofs.json) — parsed manifest with per-theorem, per-file, per-namespace rollups
- [`artifacts/print_assumptions_all_proofs.csv`](artifacts/print_assumptions_all_proofs.csv) — flat per-theorem table

Two independent witnesses agree: the project's own hygiene tool ([`scripts/inquisitor.py`](scripts/inquisitor.py), ~80 vacuity rules) and Coq's kernel-level dependency-graph audit. Neither finds a project-local axiom anywhere. The constructivity boundary is precise: only 25 theorems out of 3,310 (0.76%) use excluded middle directly, and those theorems are named.

---

## 12. Who should care

This work is foundational, not industrial. For most software, μ-tracking does not matter. The audience is narrow and real.

**People who should care:**

- **Foundations of computer science.** If "what is the state of a computation, really" is a question that interests you, this is a formal answer that adds new state with proven independence from classical state.
- **Foundations of quantum information.** The CHSH ↔ NPA biconditional is a standalone contribution. The Tsirelson bound has a cost-algebra origin nobody had identified.
- **Verified hardware.** The Coq↔OCaml↔Kami↔Verilog chain with bisimulation proofs for all 46 opcodes is unusual and reusable.
- **Confidential / attested computing.** A μ-ledger is a structurally stronger primitive than a digital signature for proving that verification work was actually performed. The receipt is tied to a cost ledger, not just to a key.
- **AI verification.** "Did this model output actually go through the verification pipeline it claims" is the central question, and a μ-ledger receipt is a stronger answer than current attestation primitives.

**People who should not care:**

- Application programmers. The model does not change how you write a web service.
- Systems engineers without an attestation requirement.
- Anyone looking for performance improvements.

The project is foundational. It changes what you mean by "the state of a computation." Whether that matters to you depends on whether you needed to know.

---

## 13. What's left

The proofs are done. The hardware works. The audit is pinned. Everything load-bearing has a falsification condition.

What hasn't happened: a careful outside reader. The work has not been published in a peer-reviewed venue. No one outside this repository has spent enough time with it to either confirm the foundational reading or refute it. That is the open task. It is not a task the work itself can complete. It requires people.

If you are reading this and you are equipped to be that reader, the load-bearing argument fits in three sections of the short thesis ([`thesis/short_thesis.pdf`](thesis/short_thesis.pdf), §1, §7, §19) plus the math spec abstract ([`thesis/thiele_machine_math_spec.pdf`](thesis/thiele_machine_math_spec.pdf)). The complete claim ledger is in [`coq/kernel/aggregators/MasterSummary.v`](coq/kernel/aggregators/MasterSummary.v). Falsification conditions are at the top of [`README.md`](README.md). The audit receipt is in [`artifacts/`](artifacts/).

---

## 14. How to read further

| If you want | Read |
|---|---|
| The fastest path to the core claim | This document, sections 1, 4, 7 |
| The full informal argument with all theorems tagged to Coq files | [`thesis/short_thesis.pdf`](thesis/short_thesis.pdf) |
| The complete mathematical specification | [`thesis/thiele_machine_math_spec.pdf`](thesis/thiele_machine_math_spec.pdf) |
| The audited claim ledger | [`coq/kernel/aggregators/MasterSummary.v`](coq/kernel/aggregators/MasterSummary.v) |
| The proofs themselves | [`coq/kernel/`](coq/kernel/) (145 files), [`coq/nofi/`](coq/nofi/), [`coq/kami_hw/`](coq/kami_hw/) |
| The hardware path | [`coq/kami_hw/`](coq/kami_hw/) (24 files) |
| The audit receipts | [`artifacts/print_assumptions_all_proofs.json`](artifacts/print_assumptions_all_proofs.json) |
| How to break it | [`README.md`](README.md) §"How to break this" |

---

## 15. About the author

I'm Devon Thiele. I don't have a CS PhD. I started in January 2025 trying to build a 3D renderer using category theory. Sixteen days in, I realized the categorical framework also ran Newtonian physics. I followed that thread for fifteen months: rendering became physics became formal computation became Coq proofs became hardware. I learned Coq, learned what a Turing machine was, learned hardware extraction, in that order, by needing each thing for the next step.

No institutional affiliation. No co-authors. The proofs compile or they don't, and every one of them was checked.

If you want to engage with this work, to confirm it, refute it, build on it, or point out what's wrong, the email is in the repository. The proofs are open. The receipts are pinned.

Either find the falsifier, or take the result.
