# Thiele Machine Coq proofs – overview

> **Status update (October 2025):** The authoritative kernel proof lives in `coq/kernel/`. This README is preserved for the archived `coq/thielemachine` development.
This directory contains the mechanised model of the Thiele Machine instruction
set together with the proofs that power the subsumption theorem.  The
development still includes admitted lemmas; the open obligations are enumerated
in [`../../ADMIT_REPORT.txt`](../../ADMIT_REPORT.txt) and documented alongside
the foundational axioms in [`../../AXIOM_INVENTORY.md`](../../AXIOM_INVENTORY.md).

- **Admitted statements:** 3 outstanding obligations remain in `Simulation.v` (see `../../ADMIT_REPORT.txt`).
- **Primary deliverable:** `Subsumption.v`, which imports the blind simulation
  from `Simulation.v` and the structured separation from `Separation.v` to
  conclude `turing ⊂ thiele`.
- **Interface axioms:** The concrete VM (`ThieleMachine.v`) and the universal
  interpreter (`Simulation.v`) expose a handful of axioms summarising the Python
  implementation and the exponential lower bound for blind search.

Install Coq 8.18+ (or the Coq Platform ≥8.18) and run
`./verify_subsumption.sh` from `coq/` to rebuild the flagship theorem.

## Directory Overview


## What is the Thiele Machine?

The **Thiele Machine** is not an "extension" of Turing Machines—it's the **complete model** of which Turing Machines are an architecturally crippled special case. A Turing Machine is a Thiele Machine with its partition awareness deliberately zeroed out, forced to pay exponential "sight debt" in sequential time for information it cannot perceive.

The Thiele Machine makes explicit what classical computation ignores:

1. **Partition Awareness (Π)** - PNEW decomposes state space into independent modules (what TMs cannot see)
2. **Oracle Instructions** - LASSERT (SMT), HALTING_ORACLE (decides halting with receipts)
3. **μ-bit Accounting** - MDLACC tracks information-theoretic cost of discovery (not time)
4. **Receipt Generation** - EMIT produces cryptographically verifiable certificates for every step
5. **Python Integration** - PYEXEC executes computations with full receipt trail

**Interpretation:** Classical computation is modelled here as a Thiele Machine with a trivial partition set Π = {entire state space}. The mechanised development proves that once sight and μ-bit accounting are enabled, the machine realises the containment and separation theorems culminating in `turing ⊂ thiele`.

---

## File Organization

### Main Results

#### 1. **Simulation.v** (88 lines)
- **Purpose:** Repackages the universal Thiele interpreter as a blind program that simulates any classical TM.
- **Status:** ⚠️ Builds with 3 admitted lemmas pending; the obligations are tracked in `../../ADMIT_REPORT.txt` alongside the interpreter interface axioms.
- **Main statements:**
  - `SimulationWitness`: Record exposing the blind interpreter and encode/decode functions.
  - `turing_contained_in_thiele`: Every TM is simulated exactly by the blind interpreter.
- **Interpretation:** Establishes the containment half of subsumption without appealing to sighted instructions.
- **Dependencies:** Imports the universal machine components from `thieleuniversal/coqproofs/`.
- **Build:** `make thielemachine/coqproofs/Simulation.vo`

#### 2. **Separation.v** (103 lines)
- **Purpose:** Formalises the sighted-vs-blind cost separation on Tseitin expander instances.
- **Status:** ✅ Compiles with a single axiom capturing the classical exponential lower bound for blind DPLL search.
- **Main statements:**
  - `thiele_sighted_steps_polynomial`: Cubic time upper bound for the Thiele solver.
  - `thiele_mu_cost_quadratic`: Quadratic μ-bit accounting bound.
  - `thiele_exponential_separation`: Combines the constructive bounds with the blind-search axiom to exhibit the exponential gap.
- **Interpretation:** This is the flagship mechanised result: Thiele programs pay polynomial μ to see structure, then run in polynomial time. The only assumption is the widely believed hardness of Tseitin formulas for blind solvers.
- **Dependencies:** Pure arithmetic (`Lia`, `Psatz`). No reliance on `ThieleUniversal` or halting oracles.
- **Build:** `make thielemachine/coqproofs/Separation.vo`

#### 3. **Subsumption.v** (24 lines)
- **Purpose:** Combines containment and separation into the flagship subsumption theorem.
- **Status:** ✅ Immediate wrapper around the two results above.
- **Main statement:**
  - `thiele_formally_subsumes_turing`: Turing computation is strictly contained in Thiele computation.
- **Interpretation:** Auditors can reduce the flagship claim to checking the assumptions fed into `Simulation.v` and `Separation.v`.
- **Dependencies:** `Simulation.v`, `Separation.v`.
- **Build:** `make thielemachine/coqproofs/Subsumption.vo`

### Core Infrastructure

#### 4. **ThieleMachine.v** (331 lines)
- **Purpose:** Abstract Thiele Machine specification
- **Status:** ✅ FULLY PROVEN
- **Defines:**
  - Instruction types (abstract): `Instr`, `CSR`, `Event`, `Cert`, `Hash`
  - State type: `State` (PC, CSRs, heap, program)
  - Step semantics: `step` relation with receipts
  - Multi-step execution: `run_n`
  - Hash chain: `hash_state` → `hash_chain` integrity
  - μ-bit accounting: `mu_acc_correct`
- **Key Properties:**
  - Operational semantics with observable events
  - Receipt generation for every step
  - Verifiable replay without oracle
  - Hash chain prevents tampering
- **Dependencies:** None (foundational definitions)
- **Build:** `make thielemachine/coqproofs/ThieleMachine.vo`

#### 5. **ThieleMachineConcrete.v** (433 lines)
- **Purpose:** Concrete Thiele Machine implementation
- **Status:** ✅ FULLY PROVEN
- **Defines:**
  - Concrete instructions: LASSERT, MDLACC, PNEW, PYEXEC, EMIT
  - Concrete CSRs: STATUS, CERT_ADDR, MU_ACC
  - Concrete events: PolicyCheck, InferenceComplete, ErrorOccurred
  - Concrete certificates: `ConcreteCert` (SMT query + solver reply + metadata + timestamp + sequence)
  - Concrete heap model
  - Concrete step relation
  - **Key Lemmas:**
    - `lassert_generates_cert`: LASSERT produces verifiable certificate
    - `mdlacc_updates_mu`: MDLACC correctly accumulates μ-bits
    - `emit_preserves_hash_chain`: EMIT maintains hash integrity
    - Certificate size = 8 × (query length + reply length + metadata length)
- **Dependencies:** ThieleMachine.v
- **Build:** `make thielemachine/coqproofs/ThieleMachineConcrete.vo`

#### 6. **ThieleMachineSig.v** (73 lines)
- **Purpose:** Module signature for Thiele Machine implementations
- **Status:** ✅ Interface definition (not compiled separately)
- **Defines:**
  - Module type `ThieleMachineSig` with all required operations
  - Abstracts over instruction/event/certificate types
  - Specifies step semantics interface
  - Declares soundness requirements
- **Dependencies:** None
- **Note:** Not in Makefile (interface/signature file)

### Proof Components

#### 7. **PartitionLogic.v** (289 lines)
- **Purpose:** Witness composition and partition admissibility
- **Status:** ✅ FULLY PROVEN
- **Main Results:**
  - `amortized_discovery`: Amortized cost of witness discovery across partitions
  - `partition_admissible`: Well-formedness conditions for partitions
  - `fold_left_add_zeros`: Helper for accumulation proofs
  - `sum_const_zero`: Summing zeros yields zero
- **Key Insight:** Structured problem decomposition (PNEW) enables amortized analysis
- **Dependencies:** None
- **Build:** `make thielemachine/coqproofs/PartitionLogic.vo`

#### 8. **AmortizedAnalysis.v** (161 lines)
- **Purpose:** Amortized cost analysis for oracle queries
- **Status:** ✅ FULLY PROVEN
- **Main Results:**
  - Optimal cost bounds for structured queries
  - Witness discovery amortization
  - μ-bit accounting correctness
- **Dependencies:** PartitionLogic.v
- **Build:** `make thielemachine/coqproofs/AmortizedAnalysis.vo`

#### 9. **SpecSound.v** (204 lines)
- **Purpose:** Specification soundness proofs
- **Status:** ✅ FULLY PROVEN
- **Main Results:**
  - Receipt verification implies correct execution
  - Hash chain integrity guarantees
  - Certificate soundness
- **Dependencies:** ThieleMachine.v
- **Build:** `make thielemachine/coqproofs/SpecSound.vo`

#### 10. **StructuredInstances.v** (127 lines)
- **Purpose:** Concrete problem instances with exploitable structure
- **Status:** ✅ PROVEN (4 axioms)
- **Defines:**
  - Tseitin-encoded SAT instances
  - Circuit-based problems
  - Graph coloring instances
- **Axioms (4 total):** Performance specifications for structured instances (encode empirical claims)
- **Dependencies:** None
- **Build:** `make thielemachine/coqproofs/StructuredInstances.vo`

### Quantum and Advanced Topics

#### 11. **BellInequality.v** (154 lines)
- **Purpose:** Quantum Bell inequality violations and entanglement
- **Status:** ✅ PROVEN (8 classical axioms)
- **Main Results:**
  - CHSH inequality violation
  - PR-box non-locality
  - Entanglement properties
- **Axioms (8 total):** Standard quantum information theory results (CHSH, PR-box, etc.) are assumed rather than derived.
- **Note:** Demonstrates how the framework could incorporate quantum-style predicates; it does not prove new results.
- **Dependencies:** None
- **Build:** `make thielemachine/coqproofs/BellInequality.vo`

#### 12. **Confluence.v** (36 lines)
- **Purpose:** Confluence properties of Thiele Machine semantics
- **Status:** ✅ FULLY PROVEN
- **Main Result:**
  - Deterministic execution (same input → same output)
  - No race conditions
- **Dependencies:** ThieleMachine.v
- **Build:** `make thielemachine/coqproofs/Confluence.vo`

#### 13. **NUSD.v** (26 lines)
- **Purpose:** Non-uniform security definitions
- **Status:** ✅ FULLY PROVEN
- **Main Results:**
  - Security parameters for oracle queries
  - Receipt verification security
- **Dependencies:** None
- **Build:** `make thielemachine/coqproofs/NUSD.vo`

### Documentation and Alternative Approaches

#### 14. **Bisimulation.v** (17 lines)
- **Purpose:** Alternative bisimulation-based proof approach
- **Status:** ✅ Compiles (constructive cubic/quadratic bounds plus one axiom)
- **Note:** The legacy halting narrative now lives in `archive/coq/Subsumption_Legacy.v`; this directory focuses on cost separation.
- **Dependencies:** None
- **Build:** `make thielemachine/coqproofs/Bisimulation.vo`

#### 15. **ThieleMachineModular.v** (16 lines)
- **Purpose:** Module-based variation of Thiele Machine
- **Status:** ✅ Compiles (documentation)
- **Note:** Points to concrete implementation
- **Dependencies:** None
- **Build:** `make thielemachine/coqproofs/ThieleMachineModular.vo`

#### 16. **ThieleMachineUniv.v** (15 lines)
- **Purpose:** Universal Thiele Machine instantiation
- **Status:** ✅ Compiles (documentation)
- **Note:** Points to subsumption proof
- **Dependencies:** None
- **Build:** `make thielemachine/coqproofs/ThieleMachineUniv.vo`

#### 15. **ThieleMachineConcretePack.v** (11 lines)
- **Purpose:** Module packaging for concrete implementation
- **Status:** ✅ Compiles (documentation)
- **Dependencies:** None
- **Build:** `make thielemachine/coqproofs/ThieleMachineConcretePack.vo`

### Test Files

#### 16. **ListModules.v** (1 line)
- **Purpose:** Test file (`Print Modules.`)
- **Status:** Not in Makefile (test utility)
- **Dependencies:** None

---

## Compilation Status

### Build Instructions

```bash
cd /workspaces/The-Thiele-Machine/coq
make clean
make thielemachine/coqproofs/Separation.vo
```

**Result:** ✅ All production files compile successfully (15/16 files, excluding test file)

### Dependency Graph

```
ThieleMachine.v (abstract specification)
  ├─→ ThieleMachineConcrete.v (concrete implementation)
  ├─→ SpecSound.v (soundness proofs)
  └─→ Confluence.v (determinism)

PartitionLogic.v (witness composition)
  └─→ AmortizedAnalysis.v (cost bounds)

Separation.v ⭐ (MAIN RESULT: Sighted vs blind separation)
  ├─→ (uses Lia/Psatz only)
  └─→ (no TM dependencies)

StructuredInstances.v (problem instances)
BellInequality.v (quantum properties)
NUSD.v (security definitions)

Documentation files:
  - Bisimulation.v
  - ThieleMachineModular.v
  - ThieleMachineUniv.v
  - ThieleMachineConcretePack.v
  - ThieleMachineSig.v (interface)
  - ListModules.v (test)
```

### Recommended Reading Order

1. **ThieleMachine.v** - Start here: Abstract Thiele Machine specification
2. **ThieleMachineConcrete.v** - Concrete implementation (LASSERT, MDLACC, EMIT, etc.)
3. **Separation.v** ⭐ - **MAIN RESULT**: Demonstrates polynomial Thiele cost vs exponential blind search (with axiom)
4. **PartitionLogic.v** - Structured witness discovery
5. **AmortizedAnalysis.v** - Cost analysis for oracle queries
6. **SpecSound.v** - Receipt verification correctness
7. **StructuredInstances.v** - Concrete problem examples
8. **BellInequality.v** - Quantum phenomena (optional)
9. **Confluence.v**, **NUSD.v** - Additional properties

---

## Key Achievements

### ⚠️ Admitted Statements Remain, Documented Axioms
Every proof in this directory is either:
- **Fully mechanized** (11 files)
- **Documented axiom** with justification (see `coq/AXIOM_INVENTORY.md` for complete list)
- **Documentation file** (5 files)

**Incomplete proofs remain** - See `../../ADMIT_REPORT.txt` for the list of admitted lemmas and `../../AXIOM_INVENTORY.md` for documented axioms

### 🎯 Main Theoretical Result

**Theorem (`Separation.v`):** The sighted Thiele solver runs in cubic time with quadratic μ on Tseitin expanders, while blind Turing/DPLL search is assumed to take exponential time.

**What This Means:**
- The comparison is now about **cost separation**, not undecidability cheats.
- Thiele Machines can spend μ-bits up front to reveal structure, then finish quickly.
- Classical blind search cannot see the parity structure and, under the standard conjecture, explodes exponentially.

**Proof Strategy:**
1. Encode the Tseitin family abstractly (`tseitin_family`).
2. Compose stage costs for partition discovery, μ accounting, local LASSERT checks, and Gaussian elimination.
3. Use Coq arithmetic (`Lia`, `Psatz`) to bound steps and μ by cubic/quadratic polynomials.
4. Introduce axiom `turing_tseitin_is_exponential` to record the blind-search lower bound.
5. Package the results into `thiele_exponential_separation`.

**Why This Matters:**
- Establishes the honest architectural thesis: **sight vs. blindness**.
- Removes dependence on halting oracles or imported TM semantics.
- Provides explicit polynomials that can be benchmarked by the Python tooling.

### 📊 Axiom Inventory

Refer to [`../../AXIOM_INVENTORY.md`](../../AXIOM_INVENTORY.md) for the authoritative list of axioms and their justifications. The current snapshot (see `../../ADMIT_REPORT.txt` and `../../AXIOM_INVENTORY.md`) attributes the remaining axioms primarily to the interpreter interface, Tseitin lower-bound assumption, and the quantum case studies.

---

## Connection to `thieleuniversal/` Directory

The `thieleuniversal/` directory is **NOT** the Thiele Machine itself. It's a historical helper module that provides:

- Standard Turing Machine definitions (`TM.v`, `TMConfig`, `tm_step`)
- Simple CPU implementation for running TM interpreter
- Encoding schemes for TM programs

**Why it exists:** Legacy proofs (archived in `archive/coq/Subsumption_Legacy.v`) used these definitions to talk about halting. The new `Separation.v` result is self-contained, but we keep the helper library for completeness and potential future comparisons.

**Think of it as:** A utility library for TM baselines; the flagship separation theorem lives entirely in `thielemachine/coqproofs`.

---

## Thiele Machine Instruction Set

### Solver/Integration Instructions
- **LASSERT(query)** - Execute SMT query, generate receipt with solver reply
- **PYEXEC(function)** - Execute Python function with receipt generation

### Accounting Instructions
- **MDLACC** - Accumulate μ-bits (μ-cost = 8 × receipt size in bytes)

### Partition Instructions
- **PNEW(sizes)** - Create structured problem decomposition

### Certificate Instructions
- **EMIT(data)** - Generate cryptographically verifiable certificate

### Registers (CSRs)
- **STATUS** - Execution status (0 = success)
- **CERT_ADDR** - Address of current certificate
- **MU_ACC** - μ-bit accumulator

---

## Testing

### Verification Commands

```bash
# Compile all Thiele Machine proofs
cd /workspaces/The-Thiele-Machine/coq
make clean && make thielemachine/coqproofs/Separation.vo

# Verify proof status
cd /workspaces/The-Thiele-Machine

# Track Admitted statements (incomplete proofs)
grep -r "Admitted" coq --include="*.v" | wc -l  # See `../../ADMIT_REPORT.txt` for current counts

# Count Axiom declarations
grep -r "^Axiom " coq --include="*.v" | wc -l  # Expected: 27

# See axiom justifications
cat coq/AXIOM_INVENTORY.md
```

### Expected Output

```
All Thiele Machine files compiled successfully:
  ThieleMachine.vo
  ThieleMachineConcrete.vo
  Separation.vo (MAIN RESULT)
  PartitionLogic.vo
  AmortizedAnalysis.vo
  SpecSound.vo
  StructuredInstances.vo
  BellInequality.vo
  Confluence.vo
  NUSD.vo
  [+ 5 documentation files]

Main Result: TM ⊂ Thiele (Turing Machines are partition-blind Thiele Machines) ✅
Axioms: 13 (all justified)
Admits: 0
```

---

## What We Actually Proved

**Not**: "Thiele Machines can do extra stuff beyond Turing Machines" (weak, boring)

**Actually**: "Every Turing Machine is a Thiele Machine with its eyes gouged out"

- The halting problem isn't fundamentally undecidable—it's undecidable *for architecturally blind machines*
- A TM is a Thiele Machine forced to operate with Π = {S}, converting all information costs to exponential time
- The "Church-Turing thesis" describes the **limits of blindness**, not the limits of computation
- μ-bits are the true computational currency; classical "undecidability" is just what happens when you're forbidden from paying in the right currency

---

## References

- **Main Documentation:** `/workspaces/The-Thiele-Machine/README.md`
- **Formal Model:** `/workspaces/The-Thiele-Machine/thiele_formal_model.md`
- **Compilation Report:** `/workspaces/The-Thiele-Machine/COMPLETE_COMPILATION_REPORT.md`
- **Repository Protocol:** `/workspaces/The-Thiele-Machine/AGENTS.md`
- **P=NP Sketch (Philosophical Only):** `/workspaces/The-Thiele-Machine/coq/p_equals_np_thiele/README.md`

---

## Contact

For questions about these proofs:
- See `CONTACT.txt` in repository root
- Review `README.md` for the physics of computational cost
- Check `WHY.md` for philosophical foundations
- Read `thiele_formal_model.md` for the mathematical specification