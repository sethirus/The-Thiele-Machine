# ThieleUniversalBridge Iterative Proof Development Guide

## Overview

This directory contains the infrastructure for iterative development and analysis of the ThieleUniversalBridge proof. The goal is to break down the large monolithic proof (2876 lines) into manageable, analyzable modules to identify bottlenecks and proof term explosion points.

## Quick Start

### 1. Extract Modules

```bash
cd /home/runner/work/The-Thiele-Machine/The-Thiele-Machine/coq/thielemachine/verification
python3 analysis/extract_modules.py
```

This creates 14 separate module files in the `modular/` directory, each representing a logical section of the original proof.

### 2. Compile Individual Modules

```bash
# Using the Makefile
make -f Makefile.modular core      # Compile just the core module
make -f Makefile.modular length    # Compile the critical length preservation module
make -f Makefile.modular all       # Compile all modules
```

### 3. Profile Compilation

```bash
python3 analysis/profile_proofs.py
```

This generates:
- `analysis/profiling_results.json` - Detailed timing data
- `analysis/PROFILING_REPORT.md` - Human-readable report

## Module Structure

The proof has been broken down into 14 modules:

| Module | Lines | Description | Status |
|--------|-------|-------------|--------|
| **BridgeHeader** | 1-50 | File header and documentation | ✓ Complete |
| **BridgeCore** | 51-200 | Core definitions (run1, run_n, state_eqb) | ✓ Complete |
| **ProgramEncoding** | 201-350 | Program encoding and padding helpers | ✓ Complete |
| **SetupState** | 351-530 | Setup state and tape window definitions | ✓ Complete |
| **Invariants** | 531-700 | Core invariants and helper lemmas | ✓ Complete |
| **BasicLemmas** | 701-900 | Basic helper lemmas (nth, firstn, skipn) | ✓ Complete |
| **LengthPreservation** | 901-920 | **CRITICAL**: `length_run_n_eq_bounded` lemma | ⚠ Has TODO |
| **RegisterLemmas** | 921-1200 | Register tracking infrastructure | ✓ Complete |
| **StepLemmas** | 1201-1400 | Individual instruction step lemmas | ✓ Complete |
| **TransitionFetch** | 1401-1650 | Fetch to FindRule transition | ✓ Complete |
| **TransitionFindRuleNext** | 1651-1950 | FindRule loop - non-match case | ✓ Complete |
| **LoopIterationNoMatch** | 1951-2100 | Loop iteration when no match | ✓ Complete |
| **LoopExitMatch** | 2101-2300 | Loop exit when match found | ✓ Complete |
| **MainTheorem** | 2301-2876 | Main transition theorem | ✓ Complete |

## Key Issues Identified

### 1. Critical Blocker: `length_run_n_eq_bounded` (Line 907-919)

**What it proves**: Register list length preservation through execution steps

**Why it's critical**: Many register tracking lemmas depend on knowing the register count stays at 10

**Current status**: Has a TODO marker, requires analysis of all instructions

**Impact**: Blocks 4+ downstream lemmas in the loop iteration proofs

### 2. Compilation Timeout Issues

From `docs/BRIDGE_DIAGNOSIS.md`:
- 120s timeout during FindRule loop lemmas
- `transition_FindRule_Next` hangs during replay
- Even with `read_mem` opaque, proof scripts don't complete

### 3. Proof Term Explosion

- Large proof terms cause memory issues during Qed
- Checkpoint method used to mitigate (seal sub-proofs)
- Some checkpoints still cause term expansion

## Analysis Tools

### 1. `extract_modules.py`

**Purpose**: Split ThieleUniversalBridge.v into logical modules

**Usage**:
```bash
python3 analysis/extract_modules.py
```

**Output**:
- Creates 14 `.v` files in `modular/`
- Generates `modular/README.md` with module index
- Prints analysis of each module (defs, lemmas, admits, TODOs)

**What it analyzes**:
- Definition counts
- Lemma/theorem counts
- Qed vs Admitted ratio
- TODO markers
- Dependencies between modules

### 2. `profile_proofs.py`

**Purpose**: Measure compilation time and proof term sizes

**Usage**:
```bash
python3 analysis/profile_proofs.py
```

**Output**:
- `analysis/profiling_results.json` - Machine-readable timing data
- `analysis/PROFILING_REPORT.md` - Human-readable analysis

**What it measures**:
- Individual module compilation times
- Per-lemma proof times (when Coq reports them)
- .vo file sizes (indicator of proof term size)
- Compilation warnings and errors
- Identifies slowest modules and proofs

### 3. `analyze_proof_terms.sh`

**Purpose**: Batch analysis and compilation

**Usage**:
```bash
bash analysis/analyze_proof_terms.sh
```

**What it does**:
- Analyzes structure of all modules
- Compiles each module with timeout
- Measures .vo file sizes
- Identifies large proof term warnings
- Logs compilation output

### 4. `Makefile.modular`

**Purpose**: Build system for modular development

**Key targets**:
```bash
make -f Makefile.modular help       # Show all targets
make -f Makefile.modular extract    # Run extraction
make -f Makefile.modular analyze    # Run structure analysis
make -f Makefile.modular profile    # Run profiling
make -f Makefile.modular length     # Compile just length module
make -f Makefile.modular all        # Compile all modules
make -f Makefile.modular clean      # Clean generated files
```

## Iterative Development Workflow

### Phase 1: Initial Analysis (DONE)

1. ✓ Install Coq 8.18.0
2. ✓ Extract modules from monolithic proof
3. ✓ Identify critical blockers and TODOs
4. ✓ Create analysis infrastructure

### Phase 2: Module-by-Module Compilation

```bash
# Compile modules in order, measuring each
make -f Makefile.modular core
make -f Makefile.modular encoding
make -f Makefile.modular setup
# ... etc
```

For each module:
1. Compile and measure time
2. Check for warnings/errors
3. Note any timeouts
4. Identify slow proofs

### Phase 3: Bottleneck Identification

```bash
# Run full profiling
python3 analysis/profile_proofs.py
```

Review report to find:
- Modules taking >10s to compile
- Proofs taking >1s individually
- Modules with large .vo files
- Patterns in slow proofs

### Phase 4: Targeted Optimization

For identified bottlenecks:

1. **For slow proofs**:
   - Break into smaller lemmas
   - Use more opaque definitions
   - Apply checkpoint method
   - Consider proof by reflection

2. **For large proof terms**:
   - Seal intermediate results
   - Use `abstract` tactic
   - Avoid `simpl` on large terms
   - Use `vm_compute` for concrete values

3. **For timeouts**:
   - Increase opacity boundaries
   - Pre-compute concrete values
   - Break into smaller steps
   - Cache intermediate states

### Phase 5: Complete Critical Lemmas

Priority order:

1. **`length_run_n_eq_bounded`** (Module: LengthPreservation)
   - Enumerate all program instructions
   - Prove each preserves length
   - Apply inductively

2. **Loop iteration TODOs** (Module: LoopIterationNoMatch)
   - Use infrastructure lemmas
   - Apply register tracking
   - Complete 4 blocked subgoals

3. **Checkpoint helpers** (Module: TransitionFindRuleNext)
   - Extract and seal sub-proofs
   - Reduce term expansion

## Measuring Progress

### Key Metrics to Track

1. **Compilation Times**:
   - Total time for all modules
   - Per-module times
   - Per-proof times

2. **Proof Term Sizes**:
   - .vo file sizes
   - Large term warnings
   - Qed time vs proof script time

3. **Completion Status**:
   - Number of Qed vs Admitted
   - Number of TODOs resolved
   - Critical path unblocked

4. **Build Health**:
   - Modules that compile successfully
   - Modules that timeout
   - Modules with errors

### Expected Outcomes

**Short term (immediate)**:
- All modules compile (some with admits)
- Profiling data identifies top 3-5 bottlenecks
- Clear priority list for optimization

**Medium term (iterative work)**:
- Critical `length_run_n_eq_bounded` proved
- Loop iteration TODOs completed
- Compilation times reduced 20-50%

**Long term (completion)**:
- All admits resolved to Qed
- No compilation timeouts
- Full bridge proof compiles in <5 minutes
- Clear documentation of proof structure

## Understanding the Proof Structure

### Execution Model

The proof shows a CPU simulating a Turing machine:

1. **Fetch** (PC=0-2): Load symbol from tape
2. **FindRule** (PC=3-11): Loop through rules to find match
3. **ApplyRule** (PC=12+): Apply matched rule transition

### Key Invariants

- **Register count**: Always 10 registers (REG_PC through REG_TEMP2)
- **Memory layout**: Program | Rules | Tape
- **Program encoding**: Concrete encoded UTM program
- **Tape window**: Tape properly positioned in memory

### Proof Strategy

1. **Setup**: Show initial state satisfies invariants
2. **Transitions**: Prove each phase transition preserves invariants
3. **Loops**: Prove loop iterations maintain invariants
4. **Composition**: Chain transitions to show full simulation

## Troubleshooting

### Module won't compile

```bash
# Check dependencies
grep "Require Import" modular/Bridge_YourModule.v

# Try compiling dependencies first
make -f Makefile.modular core encoding setup
```

### Timeout during compilation

```bash
# Identify which proof is slow
coqc -time -Q ../../.. "" modular/Bridge_YourModule.v 2>&1 | grep "Time"

# Look for proofs taking >5s
```

### Large proof term warnings

```bash
# Check .vo file size
ls -lh modular/Bridge_YourModule.vo

# Files >100KB indicate large proof terms
# Consider applying checkpoint method
```

## Next Steps

1. **Run initial profiling**:
   ```bash
   python3 analysis/profile_proofs.py
   ```

2. **Review results**:
   - Check `analysis/PROFILING_REPORT.md`
   - Identify top 3 bottleneck modules
   - Note any compilation failures

3. **Create optimization plan**:
   - List specific lemmas to optimize
   - Prioritize by impact
   - Assign time estimates

4. **Iterate**:
   - Fix one bottleneck
   - Re-profile
   - Measure improvement
   - Repeat

## References

- **Original proof**: `ThieleUniversalBridge.v` (2876 lines)
- **Diagnosis doc**: `docs/BRIDGE_DIAGNOSIS.md`
- **Status doc**: `coq/BRIDGE_LEMMA_STATUS.md`
- **Continuation plan**: `coq/CONTINUATION_PLAN.md`

## Contact & Contribution

This infrastructure enables systematic analysis and improvement of the bridge proof. Contributions should:

1. Use the analysis tools to identify issues
2. Work on one module at a time
3. Measure before/after compilation times
4. Document optimizations applied
5. Update this guide with findings
