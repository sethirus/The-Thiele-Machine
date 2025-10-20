> **ARCHIVAL NOTICE:** This document is preserved for historical context. The final, unified proof and analysis are now complete. For the authoritative summary, see `README.md` and `docs/final_fact_check.md`.

> **Status update (October 2025):** This document is preserved for historical context. For the current analysis of the kernel, μ-spec v2.0, and reproducible evidence see `docs/kernel_analysis.md` and `docs/final_fact_check.md`.

Thiele Machine — Formal Model

This short, self-contained document fixes the mathematical model used by the project.
It is intended to be the canonical specification used by proofs and by the Coq development.

1. The Machine Tuple

Define the Thiele Machine as the 5-tuple

T = (S, Π, A, R, L)

where

- S is the set of machine states. Each s ∈ S encodes the program counter, the machine memory (heap/registers), and any auxiliary bookkeeping (hash chain, local views, etc.).
- Π is a family of partitions over the machine memory: Π = {π} where each partition π is a finite partition of the set of memory locations into labelled blocks. A partition π induces a projection operator proj_π that maps a concrete state s to the tuple of block contents observed under π.
- A is a finite set of instructions (the instruction set). Relevant named instructions used in the development include PNEW, LASSERT, MDLACC and other elemental operations. Each a ∈ A is a syntactic token with an associated operational semantics.
- R ⊆ S × A × S × Obs is the step relation. If (s, a, s', o) ∈ R we write s --a/ o--> s'. The component Obs (observations) is defined below.
- L is the cost/ledger structure used to account for µ-bits; it contains a function bitsize : Cert → Z≥0 and a per-step µ-accounting value mu_delta ∈ Z associated with observations.

2. Observations and Certificates

Define the observation record StepObs := (ev, mu_delta, cert) where

- ev ∈ Option(Event) is an optional externally-visible event produced by the step (for example, a query sent to an SMT oracle or a model returned by a solver).
- mu_delta ∈ Z is the µ-bits charged by this step (can be zero or positive; in proofs we treat it as a non-negative integer). It is the elementary increment of the µ-bits ledger.
- cert ∈ Cert is a succinct certificate attached to the step that attests to the correctness of the step's observable (for example, a DRAT/LRAT proof of UNSAT or a DIMACS model for SAT).

We require for all steps s --a/ obs --> s' that

(1) bitsize(obs.cert) ≤ obs.mu_delta.  (certificate size lower-bounds the charged µ-bits)

This constraint is the formal analogue of the NUSD (No Unpaid Sight Debt) axiom: to produce a certificate of B bits forces the machine to pay at least B µ-bits.

3. Instruction Semantics (informal, formalizable)

Below we give precise, mathematically stated semantics that are directly formalized in Coq alongside these descriptions.

- PNEW(label, description): allocate a new partition block (or reveal a partition descriptor). Semantics: if s ∈ S and π ∈ Π is a partition descriptor described by the instruction, then PNEW updates the machine state s to s' where the partition set used by further operations includes π. The observation produced contains a cert that encodes the canonical serialized description of π; mu_delta is at least bitsize(cert).

- LASSERT(formula): a local assertion executed within the current partition context. Semantics: LASSERT checks a constraint against the projection of the state induced by the currently selected partition; it may produce a small certificate that witnesses the check (for example, a local consistency hash). An LASSERT step may carry mu_delta = 0 when the assertion is purely local; when it requires external checking it must include a cert and pay its bitsize.

- MDLACC(query): a model-access/solver query instruction. Semantics: MDLACC sends a solver query derived from the current projection (the partition-aware problem). The observation ev contains either a model (SAT) or a pointer to a proof object (UNSAT). In either case the step must include an attached cert and charge mu_delta ≥ bitsize(cert). The verification predicate check_step(P, s, s', ev, cert) must succeed iff the certificate correctly witnesses ev with respect to the serialized query.

All other instructions are treated as native transitions that do not themselves change the partition topology; they may still produce observations when they interact with external oracles.

4. Step Relation and Replay

A program P is a finite list of instructions P ∈ A*. The step relation is given by the predicate step(P, s, s', obs) (equivalently s --P[i]/ obs --> s').

Given a trace tr = [(s0, obs0), (s1, obs1), ..., (s_{k-1}, obs_{k-1})] produced by executing P from initial state s0, define the receipts list

receipts(P, s0, tr) = [(s0, s1, ev0, cert0), (s1, s2, ev1, cert1), ..., (s_{k-1}, s_k, ev_{k-1}, cert_{k-1})].

Replay correctness: check_step(P, spre, spost, ev, cert) is a deterministic boolean checker (implemented in the reference implementation and axiomatised in Coq). A receipts list is replay_ok if for each consecutive receipt the checker accepts the step and the pre-state equals the replayed state.

5. The µ-bits Cost Model

Define the total µ-bits consumed by a trace tr as

µ(tr) := ∑_{(_, obs) ∈ tr} obs.mu_delta.

We formalize two related quantities used in proofs:

- certificate_bits(tr) := ∑_{(_, obs) ∈ tr} bitsize(obs.cert).  (total certificate size paid)
- ledger_charge(tr) := µ(tr).  (what the machine actually charged)

The NUSD axiom establishes a lower bound:

µ(tr) ≥ certificate_bits(tr).

In complexity statements we make resource claims of the following form:

"There exists a family of instances I_n such that any Blinded Thiele Machine (one that is forbidden from using non-trivial partitions) requires µ(I_n) super-polynomial in n, while a Sighted Thiele Machine that chooses an appropriate partition π_n achieves µ(I_n) polynomial in n." 

6. Formal Declaration (Cost, not Power)

The Thiele Machine does not claim to compute functions beyond Turing-computable ones. Instead it introduces µ-bits as a first-class complexity resource. The principal thesis is:

- µ-bits are a robust resource: they compose additively across steps and are subject to lower bounds enforced by certificate sizes; they can be used in complexity statements analogously to time and space.

- Architectural sight (access to partitions) changes the µ-bit complexity of natural families of problems (e.g., Tseitin formulas on expanders). This is a separation in cost, not in computability.

7. Relationship to Coq Formalization

The Coq development in this repository formalizes the components above. The module type THIELE_ABSTRACT presents the abstract types Instr, State, Event, Cert and exposes the predicate step and the checker check_step together with the key axioms (check_step_sound, mu_lower_bound, check_step_complete). The reader is encouraged to consult the Coq sources for the fully formalized statements and machine-checked proofs.

8. Minimal Notation Summary

- T = (S, Π, A, R, L)
- step(P, s, s', obs)  —  s --a/ obs --> s' for some instruction a in P
- receipts_ok(P, s0, receipts)  —  deterministic re-checker for receipts
- µ(tr) = ∑ obs.mu_delta  and  bitsize(cert) ≤ obs.mu_delta for each step

End of formal model (target length: two pages). This document should be treated as the canonical specification referenced by all proofs and by the one-click auditor script.