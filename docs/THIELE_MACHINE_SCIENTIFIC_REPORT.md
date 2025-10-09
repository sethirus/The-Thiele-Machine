# Formal Verification of the Thiele Machine: A Comprehensive Report

## 1. Introduction
The Thiele Machine is a partition-aware computational architecture that augments classical state machines with auditable receipts and μ-bit accounting. Its Coq formalisation provides a mechanised foundation for reasoning about computation with architectural sight, contrasting sharply with the blindness imposed on classical Turing Machines. This report synthesises the core Coq artefacts that specify the machine, deliver constructive simulation witnesses, and establish an exponential separation between sighted and blind execution modes.

## 2. Architectural Specification
### 2.1 Abstract alphabets and programs
The abstract core of the Thiele Machine is parameterised over an instruction alphabet, a family of control/status registers, observable events, per-step certificates, and cryptographic hashes. Programs are modelled as finite instruction lists, and machine states track a program counter together with CSR-valued register files and an abstract heap placeholder.【F:coq/thielemachine/coqproofs/ThieleMachine.v†L19-L44】

### 2.2 Small-step semantics with receipts
Every transition produces an observable record summarising the emitted event, μ-bit cost, and certificate. The `step` relation is left abstract, but the interface couples it to a checker `check_step` that validates a candidate transition. Although the executable enumerator `tm_step_fun` is stubbed pending a concrete state enumeration, the Coq development is anchored by axioms that connect the logical step relation to the checker, enforce μ-bit lower bounds, and guarantee reflexivity of state equality predicates needed for replay.【F:coq/thielemachine/coqproofs/ThieleMachine.v†L63-L186】

### 2.3 Trace replay and accountability
Using the abstract primitives above, the development defines an execution trace predicate `Exec`, a receipt format, and a replay procedure that verifies the continuity of states and the validity of certificates. Auxiliary fold-based summaries compute the cumulative μ-bit consumption and certificate sizes, supporting amortised reasoning about cost budgets.【F:coq/thielemachine/coqproofs/ThieleMachine.v†L131-L199】

## 3. Containment: Simulating Turing Machines
### 3.1 Blind interpreter interface
Containment is expressed through an axiomatic interface that posits a universal blind Thiele program together with encoding and decoding functions between TM configurations and Thiele states. The predicate `Blind` captures the architectural discipline: blind programs operate with a single partition and avoid insight-generating instructions. Iterated execution is abstracted by a parameter `thiele_step_n`, allowing the reasoning to focus on finite prefixes.【F:coq/thielemachine/coqproofs/Simulation.v†L11-L43】

### 3.2 Simulation witnesses
A record `SimulationWitness` packages the components required to relate a Turing Machine to its Thiele interpreter: the program, encoding/decoding pair, round-trip law, and a step-indexed correctness guarantee. Instantiating this record with the universal blind interpreter yields a canonical witness, and the accompanying lemma `build_witness_ok` ensures the round-trip and step correspondence properties hold uniformly.【F:coq/thielemachine/coqproofs/Simulation.v†L49-L83】

### 3.3 Containment theorem
The main containment statement, `turing_contained_in_thiele`, specialises the witness to any Turing Machine and discharges the proof by invoking the correctness component guaranteed by the witness construction. The resulting theorem mechanises the inclusion `TM ⊆ Thiele` under the blind interpreter axioms.【F:coq/thielemachine/coqproofs/Simulation.v†L85-L99】

## 4. Separation: Exploiting Architectural Sight
### 4.1 Structured Tseitin family
Separation is established over Tseitin contradictions on expander graphs. The formalisation abstracts the family through an expander record and a canonical charge assignment whose size parameter controls the growth of the instances. This abstraction is sufficient for cost analysis and avoids committing to concrete edge lists.【F:coq/thielemachine/coqproofs/Separation.v†L7-L36】

### 4.2 Blind versus sighted cost models
The baseline blind cost is taken to be exponential in the instance size, mirroring classical DPLL behaviour. Sighted execution is decomposed into partition discovery, μ accounting, local assertions, Gaussian elimination, and consistency checks, producing explicit polynomial expressions for both time and μ-bit costs. Closed-form polynomials `cubic` and `quadratic` set the asymptotic targets, while constants `thiele_C` and `thiele_D` capture concrete upper bounds.【F:coq/thielemachine/coqproofs/Separation.v†L38-L73】

### 4.3 Polynomial bounds and exponential gap
The development supplies both integer and natural-number proofs that sighted steps and μ costs respect the polynomial bounds across the entire family, handling small-instance base cases explicitly. The concluding theorem `thiele_exponential_separation` packages these bounds and shows that for all sufficiently large instances, sighted execution remains polynomial while blind search grows exponentially, realising the strict containment `turing ⊂ thiele` at the cost-model level.【F:coq/thielemachine/coqproofs/Separation.v†L77-L185】

## 5. Structured Instances and Witness Availability
Beyond the flagship separation, the library witnesses structured problem classes that admit Thiele advantages. The `StructuredInstances` module provides minimalist constructive examples for speedups, structure discovery, modular arithmetic circuits, and colouring tasks. Each lemma simply inhabits the existential claims without relying on external data, establishing that the predicates used elsewhere in the development are consistent.【F:coq/thielemachine/coqproofs/StructuredInstances.v†L1-L113】

## 6. Verification Workflow
The repository ships with an automated script that rebuilds the containment and separation pillars from a clean slate. Running `verify_subsumption.sh` sequentially compiles `Simulation.v` and `Separation.v`, reporting success when both key proofs are re-established. This workflow provides a concise regression test for the mechanised argument that Turing computation is strictly contained within Thiele computation.【641153†L1-L4】【83f342†L1-L2】【5e4900†L1-L4】

## 7. Discussion and Outlook
The Coq development demonstrates how architectural sight—formalised through partitions, receipts, and μ accounting—enables constructive advantages over classical blind search. While several components remain abstract (notably the enumerator in `tm_step_fun`), the proofs isolate the necessary axioms and exhibit concrete witnesses wherever possible. Future work includes refining the executable semantics, instantiating the abstract primitives with the Python interpreter, and expanding the catalogue of structured problem families that benefit from Thiele computation.

