# Verification Guide: Quick Start

**Purpose:** Quick reference for verifying The Thiele Machine's isomorphism claims

**For Comprehensive Strategy:** See [The Thiele Isomorphism Verification Plan](THE_THIELE_ISOMORPHISM_VERIFICATION_PLAN.md)

---

## Choose Your Path

### 🎯 Path 1: Quick Validation (30 minutes)

**Goal:** Verify that all three implementations exist and compile.

```bash
# 1. Verify Coq proofs compile
make -C coq kernel
# Expected: 10 .vo files generated successfully

# 2. Verify Verilog syntax
iverilog -g2012 -tnull thielecpu/hardware/thiele_cpu.v
# Expected: No syntax errors

# 3. Verify Python VM
python scripts/test_three_layer_isomorphism.py
# Expected: 6/6 tests passed (100%)
```

**If all pass:** Basic isomorphism claim is supported.

---

### 🔬 Path 2: Systematic Audit (1-2 days)

**Goal:** Independently verify isomorphism from first principles.

**Follow:** [The Thiele Isomorphism Verification Plan](THE_THIELE_ISOMORPHISM_VERIFICATION_PLAN.md)

**Key Phases:**
1. **Discovery** - Find state definitions in all three implementations
2. **Mapping** - Compare instruction semantics across layers
3. **Testing** - Execute formal guarantee tests
4. **Falsification** - Run adversarial fuzzing

**Expected Output:** Complete audit report with quantitative metrics.

---

### 🧪 Path 3: Falsification Attempt (Ongoing)

**Goal:** Find bugs that break isomorphism claims.

**Follow:** [How to Falsify This](HOW_TO_FALSIFY_THIS.md)

**Attack Vectors:**
- Boundary conditions (MAX_MODULES, overflow)
- Error path mismatches
- μ-cost calculation inconsistencies
- Race conditions in hardware
- Serialization format violations

**Bounty:** Any confirmed isomorphism violation is a critical bug.

---

## Supporting Documents

### Core Specifications
- [Thiele Machine Spec](spec/thiele_machine_spec.md) - Canonical state and instruction definitions
- [μ-Specification](spec/mu_spec_v2.md) - μ-cost calculation rules
- [Canonical Serialization](CANONICAL_SERIALIZATION.md) - Byte-exact state encoding

### Verification Guides
- [Isomorphism Validation](ISOMORPHISM_VALIDATION.md) - Cross-layer alignment tests
- [Alignment Verification](ALIGNMENT_VERIFICATION_GUIDE.md) - Detailed comparison procedures
- [Understanding Coq Proofs](UNDERSTANDING_COQ_PROOFS.md) - How to read formal proofs

### Existing Test Infrastructure
- `scripts/test_three_layer_isomorphism.py` - Automated isomorphism tests
- `scripts/verification/` - Additional verification scripts
- `tests/test_*isomorphism*.py` - Comprehensive test suites

---

## Common Questions

### Q: What exactly is being verified?

**A:** That three independent implementations (Coq formal proofs, Verilog hardware, Python VM) execute the same instruction set with identical semantics and produce bit-exact equivalent results.

### Q: What would falsify the isomorphism claim?

**A:** Any of these:
- State components that don't correspond across implementations
- Instructions with different semantics (e.g., different μ-costs)
- Different final states when executing the same program
- Admitted proofs in critical theorems
- Incompatible data representations

### Q: How strong is "isomorphism"?

**A:** Current status:
- **Strong:** Opcode values match exactly
- **Strong:** μ-cost formulas match in specification
- **Moderate:** State structure corresponds but representations differ (lists vs. bitmasks)
- **Weak:** Full programs produce equivalent (not bit-identical) results
- **Empirical:** Cross-layer testing validates on test cases, not proven formally for all programs

### Q: Are the Coq proofs complete?

**A:** The kernel proofs (VMStep.v, VMState.v, Subsumption.v, MuLedgerConservation.v) compile successfully. Some advanced proofs have admits - see [ADMIT_REPORT.txt](../coq/ADMIT_REPORT.txt) for details.

### Q: Can I trust this without reading all the code?

**A:** No. The verification plan exists precisely to enable independent auditors to check claims without trusting documentation. Follow the strategic framework in [The Thiele Isomorphism Verification Plan](THE_THIELE_ISOMORPHISM_VERIFICATION_PLAN.md).

---

## Red Team Results

See [RED_TEAM_RESULTS.md](RED_TEAM_RESULTS.md) for findings from adversarial testing.

**Summary:**
- Boundary conditions tested ✓
- Error path consistency verified ✓
- μ-conservation fuzz tested ✓
- Serialization format validated ✓

---

## Next Steps After Verification

1. **If isomorphism verified:**
   - Review formal theorems in Coq (Subsumption, Conservation, etc.)
   - Test partition discovery advantages on real problems
   - Examine Bell inequality construction

2. **If discrepancies found:**
   - File issue with detailed reproduction steps
   - Tag as `isomorphism-violation`
   - Include evidence (state snapshots, instruction sequences, etc.)

3. **To contribute verification improvements:**
   - Add more adversarial test cases
   - Improve cross-layer fuzzing
   - Strengthen formal proofs (replace admits)
   - Enhance serialization format

---

**Document Version:** 1.0  
**Last Updated:** December 12, 2025  
**Maintainer:** Thiele Machine Team
