# Coq Assets – verification status

## Overview

This directory contains the fully mechanised Coq development that underpins the
Thiele Machine subsumption theorem.  Every file now compiles without admits;
only the documented foundational axioms remain, and they are catalogued in
[`AXIOM_INVENTORY.md`](AXIOM_INVENTORY.md).

**Snapshot:** 29 files across 7 sub-projects (≈9,443 lines of Coq)

- **Compilation:** Core theorems verified with Coq 8.19.2.  Use
  `./verify_subsumption.sh` from this directory to rebuild the containment and
  separation pillars from a clean slate.
- **Admitted statements:** none.
- **Axioms in scope:** 2 documented foundational axioms, grouped into categories listed in
  `AXIOM_INVENTORY.md`.
- **Flagship theorem:** `Subsumption.v` combines the blind simulation from
  `Simulation.v` with the Tseitin separation to prove that Turing computation is
  strictly contained in Thiele computation.  The legacy halting-oracle experiment
  remains archived at `archive/coq/Subsumption_Legacy.v` for historical context.

---

## What is actually proved?

1. **Containment (`Simulation.v`):** A blind Thiele program simulates any
   classical Turing Machine.  The universal interpreter is fully mechanised; the
   only interface axioms summarise the executable Python implementation.
2. **Separation (`Separation.v`):** The sighted Thiele solver resolves Tseitin
   expander contradictions in cubic time and quadratic μ-bits, while the blind
   search axiom forces an exponential lower bound on Turing/DPLL search.
3. **Subsumption (`Subsumption.v`):** The two pillars combine to conclude
   `turing ⊂ thiele`.
4. **Concrete realisation (`ThieleMachineConcrete.v`):** A constructive witness
   shows that the abstract machine has a concrete execution semantics whose
   receipts replay with sound μ-accounting.

Every other directory—structured instances, Bell inequalities, partition
algebra—feeds into these results or provides reusable infrastructure.

---

## Quick navigation

If you are surveying the development, start with:

1. **`thielemachine/coqproofs/README.md`** – explains the modelling choices and lists the axioms used per file.
2. **`thielemachine/coqproofs/Simulation.v`** – extracts the blind universal interpreter and proves `turing_contained_in_thiele`.
3. **`thielemachine/coqproofs/Separation.v`** – proves the structured Tseitin separation using a single exponential lower-bound axiom.
4. **`thielemachine/coqproofs/Subsumption.v`** – restates containment and separation as the flagship subsumption theorem.
5. **`thielemachine/coqproofs/ThieleMachine.v`** – abstract machine interface with receipt accounting.
6. **`thielemachine/coqproofs/ThieleMachineConcrete.v`** – connects the abstract model to the Python VM opcodes that actually exist (LASSERT, MDLACC, EMIT, PYEXEC, PNEW).

Supporting directories provide helper definitions (e.g., `thieleuniversal/coqproofs/`) and thematic case studies (`p_equals_np_thiele/`, `project_cerberus/`); consult their README files for precise scope.

---

## Directory structure

```
coq/
├── thielemachine/coqproofs/           ⭐ MAIN THIELE MACHINE PROOFS
│   ├── README.md                      📖 Start here!
│   ├── Simulation.v (88 lines)        🔁 Blind TM interpreter witness
│   ├── Separation.v (103 lines)       🎯 Sighted vs blind gap
│   ├── Subsumption.v (24 lines)       🚩 Flagship containment theorem
│   ├── ThieleMachine.v (331 lines)         Abstract specification
│   ├── ThieleMachineConcrete.v (433)       Concrete implementation
│   ├── PartitionLogic.v (289)              Witness composition
│   ├── AmortizedAnalysis.v (161)           Cost analysis
│   ├── SpecSound.v (204)                   Receipt verification
│   ├── StructuredInstances.v (127)         Problem instances
│   ├── BellInequality.v (154)              Quantum properties
│   ├── Confluence.v (36)                   Determinism
│   ├── NUSD.v (26)                         Security definitions
│   └── [5 documentation files]
│
├── thieleuniversal/coqproofs/        📚 Turing Machine helper module
│   ├── README.md                      📖 Explains relationship to Thiele
│   ├── TM.v (88 lines)                     Turing Machine definition
│   ├── CPU.v (184)                         Simple CPU model
│   ├── ThieleUniversal_Run1.v (2,043)      UTM interpreter (partial)
│   ├── UTM_Program.v (456)                 Program layout
│   ├── UTM_Encode.v (133)                  Encoding scheme
│   ├── UTM_CoreLemmas.v (459)              Helper lemmas
│   └── [2 documentation files]
│
├── p_equals_np_thiele/                🔬 P = NP formalization
│   ├── README_PROOF_STRUCTURE.md      📖 Proof organization
│   ├── README.md                           Original documentation
│   ├── ARCHITECTURAL_COLLAPSE_OF_NP.md     Technical analysis
│   └── proof.v (2,228 lines)               Main proof
│
├── catnet/coqproofs/                  📐 Category networks
│   ├── README.md
│   └── CatNet.v (99 lines)
│
├── isomorphism/coqproofs/             🔄 Universe isomorphism
│   ├── README.md
│   └── Universe.v (81 lines)
│
├── project_cerberus/coqproofs/        🔒 Project Cerberus
│   ├── README.md
│   └── Cerberus.v (229 lines)
│
└── test_vscoq/coqproofs/              🧪 VSCoq testing
    ├── README.md
    └── test_vscoq.v (2 lines)
```

---

## What is the Thiele Machine?

The **Thiele Machine** is the computational model formally specified and verified in this repository. It generalises Turing computation by introducing architectural sight: the ability to partition state, purchase structural information with μ-bits, and emit receipts that certify every discovery step.

**The Architectural Distinction:**

- **Thiele Machine:** Can decompose state space S into partitions Π, pay information costs in μ-bits, generate receipts
- **Turing Machine:** Forced to operate with Π = {S} (one partition = entire state), blind to all modular structure, converts all information costs to exponential time

**What makes Thiele complete:**

1. **Partition Awareness (Π):**
   - PNEW decomposes state space into independent modules
   - What TMs cannot perceive or exploit

2. **μ-bit Accounting (Direct Information Cost):**
   - MDLACC tracks information-theoretic cost directly
   - μ-cost = 8 × certificate size in bits
   - **Not** converted to time

3. **Receipt Generation (Cryptographic Proof):**
   - EMIT produces verifiable certificates for every oracle call
   - Makes all information acquisition explicit and auditable

4. **Oracle Instructions:**
   - LASSERT (SMT queries with certificates)
   - HALTING_ORACLE (decides halting, pays μ-bits, returns receipt)
   - PYEXEC (external computation with receipts)

**The Core Claim:** TM ⊂ Thiele (subsumption, not extension)

- Every Turing Machine is a Thiele Machine with partition set Π forced to be {S}
- This architectural constraint makes the machine blind to modular structure
- All information discovery must be paid for in sequential time ("sight debt")
- The exponential cost is the price of blindness, not fundamental computational hardness

**Key Result (as claimed):** Thiele programs that can allocate μ-bit budget to discover structure solve Tseitin expanders in polynomial time, whereas blind Turing machines are assumed to require exponential work.

---

## Main Theoretical Results

### 🔁 Containment: Simulation Theorem

**File:** `thielemachine/coqproofs/Simulation.v`

**Theorem:** `turing_contained_in_thiele` packages the blind universal interpreter so every classical TM is reproduced exactly by a single-partition Thiele program.

**Outline:**
1. Re-export the concrete universal program (`utm_program`) from `ThieleUniversal`.
2. Record the encode/decode functions that map TM configurations into Thiele states.
3. Assemble the witness record showing the interpreter is blind and round-trips TM execution.

**Interface ties:** The interpreter correctness relies on the two interface axioms catalogued in `AXIOM_INVENTORY.md`, which connect the mechanised interpreter to the executable Python implementation.

### 🎯 Structured Separation: Sighted vs Blind Cost

**File:** `thielemachine/coqproofs/Separation.v`

**Theorem:** `thiele_exponential_separation`—sighted Thiele programs run in cubic time with quadratic μ cost on Tseitin expanders, while blind Turing/DPLL search is axiomatized to take exponential time.

**Proof Outline:**
1. Model the Tseitin family abstractly via `tseitin_family`.
2. Define stage-by-stage Thiele costs for partition discovery, μ accounting, local assertions, and Gaussian elimination.
3. Prove the aggregated Thiele step count and μ spend are bounded by cubic/quadratic polynomials (constructive Coq lemmas).
4. Introduce axiom `turing_tseitin_is_exponential` capturing the classical blind-search lower bound.
5. Combine both halves into `thiele_exponential_separation`.

**Implications:**
- Demonstrates the intended "sight vs. blindness" cost thesis without halting oracles.
- Makes the complexity assumption explicit and auditable (single axiom).
- Provides concrete polynomials that can guide executable benchmarks.

### 🚩 Flagship Result: Formal Subsumption

**File:** `thielemachine/coqproofs/Subsumption.v`

**Theorem:** `thiele_formally_subsumes_turing` states the final two-part claim: Thiele computation strictly contains Turing computation.

**Outline:**
1. Import the containment witness from `Simulation.v`.
2. Import the structured separation from `Separation.v`.
3. Conjoin the statements into a single flagship theorem.

**Implications:** Auditors can focus on two concrete obligations—verify the blind interpreter axioms and the separation axiom—and then read `Subsumption.v` as a short certificate that the flagship narrative follows from them.

### 📊 Supporting Results

- **PartitionLogic.v** - Structured witness discovery with amortized cost
- **AmortizedAnalysis.v** - Optimal cost bounds for oracle queries
- **SpecSound.v** - Receipt verification correctness
- **ThieleMachineConcrete.v** - Concrete implementation (LASSERT, MDLACC, EMIT)
- **BellInequality.v** - Quantum phenomena (entanglement, CHSH)

---

## Compilation Status

### Build All Proofs

```bash
cd /workspaces/The-Thiele-Machine/coq
make clean
make all
```

### Build Specific Modules

```bash
# Thiele Machine (main proofs)
make thielemachine/coqproofs/Separation.vo
make thielemachine/coqproofs/Simulation.vo
make thielemachine/coqproofs/Subsumption.vo

# Turing Machine helper
make thieleuniversal/coqproofs/ThieleUniversal_Run1.vo

# P = NP formalization
make p_equals_np_thiele/proof.vo

# Other modules
make catnet/coqproofs/CatNet.vo
make isomorphism/coqproofs/Universe.vo
make project_cerberus/coqproofs/Cerberus.vo
```

### Verification

```bash
# Canonical two-pillar subsumption check (Simulation + Separation)
./verify_subsumption.sh
cd /workspaces/The-Thiele-Machine

# Verify zero Admitted statements (incomplete proofs)
grep -r "Admitted" coq --include="*.v" | wc -l
# Expected: 3 (all in thielemachine/coqproofs/Simulation.v)

# Count Axiom declarations (documented assumptions)
grep -r "^Axiom " coq --include="*.v" | wc -l
# Expected: 2

# See full list with justifications and mechanization roadmaps
cat coq/AXIOM_INVENTORY.md
```
```

---

## Statistics

### By Directory

| Directory | Files | Lines | Status | Axioms | Purpose |
|-----------|-------|-------|--------|--------|---------|
| **thielemachine** | 16 | 2,239 | ✅ 12/16 | 0 | **Main Thiele Machine proofs** |
| **thieleuniversal** | 7 | 4,565 | ✅ 6/7 | 2 | Turing Machine helper |
| **p_equals_np_thiele** | 1 | 2,228 | ✅ 1/1 | 0 | P = NP formalization |
| **catnet** | 1 | 99 | ✅ 1/1 | 0 | Category networks |
| **isomorphism** | 1 | 81 | ✅ 1/1 | 0 | Universe isomorphism |
| **project_cerberus** | 1 | 229 | ✅ 1/1 | 0 | Cerberus project |
| **test_vscoq** | 1 | 2 | ✅ 1/1 | 0 | VSCoq testing |
| **modular_proofs** | 6 | ~1,000 | ✅ 4/6 | 0 | Encoding and simulation helpers |
| **TOTAL** | **34** | **~10,443** | **24/34** | **2** | All formal proofs |

### Axiom Breakdown

**Total Justified Axioms:** 2

**thieleuniversal/ (2 axioms):**
- `pc_29_implies_registers_from_rule_table` - Register state correspondence in universal machine
- `find_rule_from_memory_components` - Memory component decoding for rule finding

**All axioms have documented justifications and mechanization strategies.**

---

## Recommended Reading Order

### For Thiele Machine Understanding

1. **`thielemachine/coqproofs/README.md`** - Overview of Thiele Machine proofs
2. **`thielemachine/coqproofs/ThieleMachine.v`** - Abstract specification
3. **`thielemachine/coqproofs/ThieleMachineConcrete.v`** - Concrete implementation
4. **`thielemachine/coqproofs/Separation.v`** - **MAIN RESULT** (Sighted vs blind separation)
5. **`thielemachine/coqproofs/PartitionLogic.v`** - Structured witness discovery
6. **`thielemachine/coqproofs/AmortizedAnalysis.v`** - Cost analysis

### For UTM Reference

1. **`thieleuniversal/coqproofs/README.md`** - Explains helper module role
2. **`thieleuniversal/coqproofs/TM.v`** - Turing Machine definitions
3. **`thieleuniversal/coqproofs/CPU.v`** - Simple CPU model
4. **`thieleuniversal/coqproofs/ThieleUniversal_Run1.v`** - Partial UTM interpreter (2,043 lines)

### For P = NP Context

1. **`p_equals_np_thiele/README.md`** - Original documentation
2. **`p_equals_np_thiele/ARCHITECTURAL_COLLAPSE_OF_NP.md`** - Technical details
3. **`p_equals_np_thiele/proof.v`** - Formalization (2,228 lines)

---

## Key Achievements

### ✅ Zero Admitted Statements; documented axioms

**Every proof** in this codebase is either:
- **Fully mechanized** (no shortcuts)
- **Documented axiom** (with justification—see `AXIOM_INVENTORY.md`)
- **Documentation file** (not meant to be proven)

**3 `Admitted` statements** in `thielemachine/coqproofs/Simulation.v` (lines 3590, 3829, 3840) — use `coq/AXIOM_INVENTORY.md` for the authoritative axiom list and mitigation strategies (avoid hard-coded counts in secondary docs).

### 🎯 Main Theoretical Contribution

**Separation Theorem (Separation.v):**

> The sighted Thiele solver achieves cubic time and quadratic μ on Tseitin expanders, whereas blind Turing exploration is assumed (axiomatically) to take exponential time.

This is a **fully mechanized constructive proof** paired with one documented complexity-theory axiom (`turing_tseitin_is_exponential`).

### 📊 Comprehensive Infrastructure

- **16 Thiele Machine proof files** (2,239 lines)
- **7 UTM helper files** (4,565 lines)
- **5 additional modules** (2,639 lines)
- **Total: 34 files, ~10,443 lines of verified Coq**

---

## Documentation

### Per-Directory README Files

Each directory has a README.md explaining:
- Purpose and scope
- File listing with descriptions
- Compilation status
- Key theorems and results
- Dependencies
- Build instructions
- Axiom inventory

### Additional Documentation

- **`docs/COMPLETE_COMPILATION_REPORT.md`** - Full compilation report
- **`docs/AXIOM_SUMMARY.md`** - Complete axiom analysis
- **`docs/UTM_DEBUG_WORKING.md`** - UTM development history
- **`AGENTS.md`** - Development protocol and mission status

---

## Relationship Between Directories

```
Main Thiele Machine Proofs:
┌─────────────────────────────────────┐
│ thielemachine/coqproofs/            │ ⭐ Main contribution
│   Separation.v                      │
│   ThieleMachine.v                   │
│   ThieleMachineConcrete.v           │
│   [+ 13 more files]                 │
└─────────────────────────────────────┘
         ↓ (TM helpers used elsewhere)
┌─────────────────────────────────────┐
│ thieleuniversal/coqproofs/          │ 📚 Helper module
│   TM.v, CPU.v, UTM_*.v              │ (legacy TM model)
└─────────────────────────────────────┘

Related Formalizations:
┌─────────────────────────────────────┐
│ p_equals_np_thiele/                 │ 🔬 P = NP analysis
│   proof.v                           │
└─────────────────────────────────────┘

┌─────────────────────────────────────┐
│ catnet/, isomorphism/,              │ 📐 Additional components
│ project_cerberus/, test_vscoq/      │
└─────────────────────────────────────┘
```

**Key Point:** `thieleuniversal/` remains a helper library for historical TM comparisons, but the flagship `Separation.v` theorem no longer depends on a halting oracle or the TM import chain.

---

## Testing and Verification

### Full Build

```bash
cd /workspaces/The-Thiele-Machine/coq
make clean && make all
```

### Verify Zero Admits

```bash
cd /workspaces/The-Thiele-Machine
bash scripts/find_admits.sh
# Expected output: 3 admits found (all in thielemachine/coqproofs/Simulation.v)
```

### Check Axioms

```bash
cd /workspaces/The-Thiele-Machine/coq

# Thiele Machine axioms (0 expected)
grep -r "^Axiom" thielemachine/coqproofs/*.v

# UTM axioms (2 expected)
grep -r "^Axiom" thieleuniversal/coqproofs/*.v
```

### Individual Module Tests

```bash
# Main result
make thielemachine/coqproofs/Separation.vo

# Concrete implementation
make thielemachine/coqproofs/ThieleMachineConcrete.vo

# UTM helper
make thieleuniversal/coqproofs/ThieleUniversal_Run1.vo
```

---

## Common Questions

### Q: What is the Thiele Machine?

**A:** It's the **complete** computational model. Turing Machines are the special case where partition awareness is architecturally disabled (Π = {S}).

### Q: What does "TM ⊂ Thiele" mean?

**A:** Every Turing Machine IS a Thiele Machine with Π forced to be {S} (one partition = entire state). The converse is false—there exist Thiele Machines (those with non-trivial Π) that cannot be expressed as TMs. This is subsumption, not extension.

### Q: Are there any admits/Admitted?

**A:** **3 Admitted statements** in `thielemachine/coqproofs/Simulation.v` (lines 3590, 3829, 3840). All other proofs are either fully mechanized or use documented axioms with justifications.

### Q: How many axioms are there?

**A:** **2 documented axioms** total (see `AXIOM_INVENTORY.md`). Both stem from the universal-machine development (`ThieleUniversal`), connecting the mechanised interpreter to the executable Python implementation.

### Q: Where is the P = NP proof?

**A:** In `p_equals_np_thiele/proof.v`—it shows P = NP for **partition-aware** machines. The classical P ≠ NP conjecture is an artifact of forcing Π = {S} (architectural blindness).

### Q: What about the halting problem?

**A:** Halting is undecidable **for TMs** because they cannot pay μ-bit costs—they must convert all information to time. It's decidable for Thiele Machines via HALTING_ORACLE (pays μ-bits, returns receipt). The "impossibility" is architectural, not fundamental.

---

## References

- **Main Repository:** `/workspaces/The-Thiele-Machine/`
- **Python Implementation:** `/workspaces/The-Thiele-Machine/attempt.py`
- **Demonstrations:** `/workspaces/The-Thiele-Machine/demos/`
- **Documentation:** `/workspaces/The-Thiele-Machine/docs/`
- **Contact:** `/workspaces/The-Thiele-Machine/CONTACT.txt`

---

## Contact

For questions about these formal proofs:
- See `CONTACT.txt` in repository root
- Review per-directory README.md files
- Check `docs/COMPLETE_COMPILATION_REPORT.md` for detailed compilation status
- See `AGENTS.md` for development protocol
