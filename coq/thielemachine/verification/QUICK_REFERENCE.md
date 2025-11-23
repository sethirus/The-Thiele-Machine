# ThieleUniversalBridge Modular Proof System - Quick Reference

## Quick Commands

```bash
# Navigate to verification directory
cd /home/runner/work/The-Thiele-Machine/The-Thiele-Machine/coq/thielemachine/verification

# Extract modules (first time only)
python3 analysis/extract_modules.py

# Compile a single module
make -f Makefile.modular core

# Compile all modules
make -f Makefile.modular all

# Run complete analysis workflow
bash analysis/run_all.sh

# Profile proof compilation
python3 analysis/profile_proofs.py

# Clean generated files
make -f Makefile.modular clean
```

## File Organization

```
coq/thielemachine/verification/
├── ThieleUniversalBridge.v          # Original monolithic proof (2876 lines)
├── ITERATIVE_DEVELOPMENT_GUIDE.md   # Comprehensive development guide
├── QUICK_REFERENCE.md               # This file
├── Makefile.modular                 # Build system for modules
│
├── analysis/                        # Analysis and profiling tools
│   ├── extract_modules.py          # Extract modules from main file
│   ├── profile_proofs.py           # Measure compilation times
│   ├── analyze_proof_terms.sh      # Batch analysis script
│   ├── run_all.sh                  # Master orchestration script
│   ├── profiling_results.json      # Generated timing data
│   └── PROFILING_REPORT.md         # Generated analysis report
│
└── modular/                         # Extracted module files
    ├── README.md                   # Module index
    ├── Bridge_BridgeHeader.v       # File header (lines 1-50)
    ├── Bridge_BridgeCore.v         # Core definitions (51-200)
    ├── Bridge_ProgramEncoding.v    # Encoding helpers (201-350)
    ├── Bridge_SetupState.v         # Setup state (351-530)
    ├── Bridge_Invariants.v         # Invariants (531-700)
    ├── Bridge_BasicLemmas.v        # Helper lemmas (701-900)
    ├── Bridge_LengthPreservation.v # CRITICAL (901-920)
    ├── Bridge_RegisterLemmas.v     # Register tracking (921-1200)
    ├── Bridge_StepLemmas.v         # Step lemmas (1201-1400)
    ├── Bridge_TransitionFetch.v    # Fetch transition (1401-1650)
    ├── Bridge_TransitionFindRuleNext.v  # FindRule loop (1651-1950)
    ├── Bridge_LoopIterationNoMatch.v    # Loop no-match (1951-2100)
    ├── Bridge_LoopExitMatch.v      # Loop exit (2101-2300)
    └── Bridge_MainTheorem.v        # Main theorem (2301-2876)
```

## Module Compilation Order

1. BridgeHeader - Header and instrumentation
2. BridgeCore - run1, run_n, state_eqb
3. ProgramEncoding - Program encoding helpers
4. SetupState - Initial state setup
5. Invariants - Core invariants
6. BasicLemmas - List manipulation helpers
7. **LengthPreservation** ⚠ CRITICAL - Register count preservation
8. RegisterLemmas - Register tracking infrastructure
9. StepLemmas - Individual instruction lemmas
10. TransitionFetch - Fetch phase
11. TransitionFindRuleNext - FindRule loop
12. LoopIterationNoMatch - Loop iteration
13. LoopExitMatch - Loop exit
14. MainTheorem - Final composition

## Key Issues to Watch

### 1. `length_run_n_eq_bounded` (Module: LengthPreservation)
- **Line**: 907-919
- **Status**: Has TODO
- **Impact**: Blocks 4+ lemmas in loop proofs
- **Priority**: CRITICAL

### 2. Compilation Timeouts
- **Module**: TransitionFindRuleNext
- **Issue**: 120s+ hangs during FindRule loop
- **Mitigation**: Opaque read_mem, checkpoint method

### 3. Proof Term Explosion
- **Symptoms**: Large .vo files (>100KB), Qed hangs
- **Mitigation**: Seal checkpoints, use abstract tactic

## Typical Workflow

### Initial Setup
```bash
cd coq/thielemachine/verification
python3 analysis/extract_modules.py
```

### Iterative Development
```bash
# Edit a module
vim modular/Bridge_RegisterLemmas.v

# Compile just that module
make -f Makefile.modular registers

# If successful, profile it
python3 analysis/profile_proofs.py

# Review results
cat analysis/PROFILING_REPORT.md
```

### Finding Bottlenecks
```bash
# Run full profiling
python3 analysis/profile_proofs.py

# Check the report
less analysis/PROFILING_REPORT.md

# Look for:
# - Modules taking >10s
# - Proofs taking >1s
# - Large .vo files (>50KB)
```

### Optimizing a Slow Proof
```bash
# Compile with detailed timing
coqc -time -Q ../../.. "" modular/Bridge_YourModule.v 2>&1 | grep "Time"

# Identify slow lemma
# Edit to add checkpoints or opacity
vim modular/Bridge_YourModule.v

# Recompile and verify improvement
make -f Makefile.modular yourmodule
```

## Interpretation Guide

### Compilation Times
- **<1s**: Excellent
- **1-5s**: Good
- **5-10s**: Acceptable
- **10-30s**: Slow, consider optimization
- **30-60s**: Very slow, needs attention
- **>60s or timeout**: CRITICAL, major bottleneck

### .vo File Sizes
- **<10KB**: Small, efficient proofs
- **10-50KB**: Normal
- **50-100KB**: Large proof terms
- **100-500KB**: Very large, potential issue
- **>500KB**: CRITICAL, proof term explosion

### Proof Counts
- **Qed > Admitted**: Healthy progress
- **Admitted > Qed**: Needs work
- **TODOs**: Markers for incomplete work

## Common Issues & Solutions

### Module won't compile
```bash
# Check dependencies
grep "Require Import" modular/Bridge_YourModule.v

# Ensure dependencies compiled first
make -f Makefile.modular core encoding setup
```

### Timeout during compilation
```bash
# Increase timeout in Makefile
# Or break proof into smaller pieces
# Or add more opacity
```

### "Error: No such file or directory"
```bash
# Ensure you're in the right directory
cd /home/runner/work/The-Thiele-Machine/The-Thiele-Machine/coq/thielemachine/verification

# Check Coq path
coqc -Q ../../.. "" -where
```

### Large .vo file
```bash
# Check file size
ls -lh modular/Bridge_YourModule.vo

# If >100KB:
# 1. Identify large proofs
# 2. Apply checkpoint method
# 3. Use abstract tactic
# 4. Increase opacity
```

## Next Steps After Setup

1. **Run initial profiling**:
   ```bash
   python3 analysis/profile_proofs.py
   ```

2. **Review results**:
   ```bash
   cat analysis/PROFILING_REPORT.md
   ```

3. **Identify priorities**:
   - Find slowest modules
   - Find largest .vo files
   - Check admitted lemmas

4. **Start optimization**:
   - Work on highest-impact item
   - Measure before/after
   - Document changes

## Resources

- **Main Guide**: `ITERATIVE_DEVELOPMENT_GUIDE.md`
- **Original Proof**: `ThieleUniversalBridge.v`
- **Bridge Diagnosis**: `../../../docs/BRIDGE_DIAGNOSIS.md`
- **Lemma Status**: `../../../coq/BRIDGE_LEMMA_STATUS.md`

## Getting Help

See `ITERATIVE_DEVELOPMENT_GUIDE.md` for:
- Detailed workflow explanations
- Understanding proof structure
- Advanced optimization techniques
- Troubleshooting guides
