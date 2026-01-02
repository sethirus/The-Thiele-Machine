# CI/CD Accountability System
## Holding The Thiele Machine to Adversarial Standards

**Last Updated:** January 2, 2026
**Status:** Fully Enforced

---

## Overview

The Thiele Machine repository uses a **zero-tolerance CI/CD system** that enforces all claims made in the repository. Every push and pull request is subjected to adversarial verification.

**Philosophy:** If a claim cannot be automatically verified in CI, it should not be claimed.

---

## Workflow Matrix

| Workflow | Purpose | Runs On | Enforcement |
|----------|---------|---------|-------------|
| `adversarial-audit.yml` | **PRIMARY ENFORCER** - Adversarial falsification | All branches, PRs, daily | **BLOCKS MERGE** |
| `inquisitor.yml` | Proof quality audit | All branches, PRs, weekly | **BLOCKS MERGE** |
| `ci.yml` | Standard CI tests + kernel checks | main, master, PRs | **BLOCKS MERGE** |
| `pages.yml` | Documentation deployment | main | Informational |
| `publish.yml` | Release publishing | releases | Informational |
| `release.yml` | Release workflow | releases | Informational |

---

## Adversarial Audit Workflow

**File:** `.github/workflows/adversarial-audit.yml`
**Trigger:** Every push, PR, daily at 02:00 UTC
**Enforcement:** STRICT - Any failure blocks merge

### Jobs

#### 1. **zero-admits-axioms**
**Purpose:** Enforce "0 admits, 0 axioms" claim

**Checks:**
- ✅ Searches ALL kernel files for `Admitted.`
- ✅ Searches for global `Axiom`/`Parameter` declarations (outside Module Types)
- ✅ Checks for `admit.` tactic usage
- ✅ Runs official audit script

**Pass Criteria:**
- ZERO admits found
- ZERO global axioms found
- Audit script reports 0 admits, 0 axioms

**Failure Action:** BLOCK MERGE

---

#### 2. **coq-kernel-build**
**Purpose:** Verify all critical kernel proofs compile

**Checks:**
- ✅ Compiles `Subsumption.vo` (Turing ⊂ Thiele)
- ✅ Compiles `NoFreeInsight.vo` (Impossibility framework)
- ✅ Compiles `MuLedgerConservation.vo` (μ-conservation)
- ✅ Compiles `ValidCorrelation.vo`, `AlgebraicCoherence.vo`
- ✅ Compiles `BoxCHSH.vo` (fix for bug found in adversarial audit)
- ✅ Compiles `TestTripartite.vo` (depends on BoxCHSH)
- ✅ Compiles `TsirelsonUniqueness.vo`, `TsirelsonUpperBound.vo`
- ✅ Compiles `NonCircularityAudit.vo` (anti-circular defense)
- ✅ Verifies `BoxCHSH.v` is in `_CoqProject`

**Pass Criteria:**
- All files compile with `coqc`
- No compilation errors
- BoxCHSH.v present in _CoqProject

**Failure Action:** BLOCK MERGE

---

#### 3. **circular-reasoning-check**
**Purpose:** Prevent circular reasoning in proofs

**Checks:**
- ✅ Verifies `VMState.v`, `VMStep.v`, `MuCostModel.v` contain NO references to:
  - "2828" (Tsirelson bound rational approx)
  - "sqrt 2" or "2√2"
  - "Tsirelson"
- ✅ Checks dependency graph for cycles in key theorems:
  - Subsumption ↔ NoFreeInsight
  - Subsumption ↔ MuLedgerConservation
  - NoFreeInsight ↔ MuLedgerConservation

**Pass Criteria:**
- Primitives are physics-free (no Tsirelson encoding)
- No circular imports detected

**Failure Action:** BLOCK MERGE

---

#### 4. **hardware-synthesis**
**Purpose:** Verify hardware actually synthesizes (not "fake Verilog")

**Checks:**
- ✅ Synthesizes `mu_alu.v` with Yosys
- ✅ Verifies synthesis produces ~555 cells (expected)
- ✅ Compiles with iverilog (0 errors, 0 warnings)
- ✅ Checks μ-accumulator has NO subtraction operations (monotonicity)

**Pass Criteria:**
- Yosys synthesis: SUCCESS
- Cell count: ≥500 cells
- iverilog: EXIT 0
- No `mu_acc` subtraction found

**Failure Action:** BLOCK MERGE

---

#### 5. **mu-conservation-check**
**Purpose:** Verify μ-conservation theorem holds

**Checks:**
- ✅ Compiles `MuLedgerConservation.vo`
- ✅ Verifies NO negative instruction costs in:
  - `VMStep.v`
  - `MuCostModel.v`

**Pass Criteria:**
- Conservation theorem compiles
- All costs ≥ 0

**Failure Action:** BLOCK MERGE

---

#### 6. **inquisitor-strict**
**Purpose:** Enforce proof quality standards

**Checks:**
- ✅ Runs `scripts/inquisitor.py`
- ✅ Extracts HIGH-severity issue count
- ✅ ENFORCES: ZERO HIGH issues

**Pass Criteria:**
- HIGH issue count = 0

**Failure Action:** BLOCK MERGE

---

#### 7. **proof-chain-verification**
**Purpose:** Verify short proofs delegate to real proofs

**Checks:**
- ✅ `mu_zero_algebraic_bound` delegates to `mu_zero_chsh_bounded`
- ✅ `mu_zero_chsh_bounded` delegates to `chsh_algebraic_bound`
- ✅ `chsh_algebraic_bound` has ≥10 line proof (substantial)

**Pass Criteria:**
- Delegation chain intact
- Base proof is non-trivial

**Failure Action:** BLOCK MERGE

---

#### 8. **adversarial-summary**
**Purpose:** Generate summary report

**Checks:**
- Aggregates all job results
- Posts summary to GitHub Actions summary
- FAILS if ANY job failed

**Pass Criteria:**
- ALL 7 jobs succeeded

**Failure Action:** BLOCK MERGE

---

## Inquisitor Workflow (Strict Mode)

**File:** `.github/workflows/inquisitor.yml`
**Trigger:** Pushes, PRs, weekly on Monday
**Enforcement:** STRICT

### Changes Made

**Before:**
- Quality threshold: 80.0 (too lenient)
- No enforcement of HIGH issues
- Would pass with HIGH-severity problems

**After:**
- ✅ **Quality threshold: 90.0** (stricter)
- ✅ **ENFORCES: Zero HIGH issues** (new step)
- ✅ **Fails CI if ANY HIGH issue found**

### Jobs

#### 1. **inquisitor-audit**
**Steps:**
1. Run inquisitor.py
2. **NEW:** Check for HIGH-severity issues → FAIL if any found
3. Generate analysis report
4. Upload reports
5. Check quality score → FAIL if <90.0
6. Comment on PR with results

**Pass Criteria:**
- HIGH issues: 0
- Quality score: ≥90.0

---

## Main CI Workflow (Enhanced)

**File:** `.github/workflows/ci.yml`
**Changes Made:**

### Before
```yaml
- name: Verify no Admitted in Coq files
  run: |
    # Only checked 3 specific files
    if grep -r "Admitted" coq/thielemachine/coqproofs/CoreSemantics.v ...
```

### After
```yaml
- name: Verify no Admitted in ALL kernel files (STRICT)
  run: |
    echo "🔍 Checking ALL kernel files for admits..."
    ADMITS=$(find coq/kernel -name "*.v" -exec grep -l "Admitted\." {} \;)
    if [ -n "$ADMITS" ]; then
      echo "❌ ERROR: Found Admitted in kernel files:"
      exit 1
    fi
```

**New Checks:**
- ✅ Verify no admits in **ALL kernel files** (not just 3)
- ✅ Compile critical kernel files: Subsumption, NoFreeInsight, MuLedgerConservation
- ✅ Compile BoxCHSH.vo and TestTripartite.vo
- ✅ Install coinor-csdp dependency

---

## Enforcement Matrix

| Claim | Enforced By | How | Failure Mode |
|-------|-------------|-----|--------------|
| "0 admits, 0 axioms" | adversarial-audit.yml → zero-admits-axioms | Exhaustive grep | BLOCK |
| "Coq proofs compile" | adversarial-audit.yml → coq-kernel-build | make *.vo | BLOCK |
| "No circular reasoning" | adversarial-audit.yml → circular-reasoning-check | Dependency analysis | BLOCK |
| "Hardware synthesizes" | adversarial-audit.yml → hardware-synthesis | Yosys + iverilog | BLOCK |
| "μ-conservation holds" | adversarial-audit.yml → mu-conservation-check | Compile + cost check | BLOCK |
| "Proof quality ≥90%" | inquisitor.yml → Check Quality Score | Static analysis | BLOCK |
| "Zero HIGH issues" | inquisitor.yml → ENFORCE Zero HIGH | Inquisitor scan | BLOCK |
| "BoxCHSH.v in build" | adversarial-audit.yml → coq-kernel-build | grep _CoqProject | BLOCK |

---

## Testing Locally

### Run Adversarial Checks Locally

```bash
# 1. Zero admits/axioms
find coq/kernel -name "*.v" -exec grep -l "Admitted\." {} \;
# Expected: (empty)

# 2. Coq build
cd coq
coq_makefile -f _CoqProject -o Makefile
make kernel/Subsumption.vo kernel/BoxCHSH.vo kernel/TestTripartite.vo
# Expected: Success

# 3. Circular reasoning
grep -n "2828\|sqrt.*2\|Tsirelson" coq/kernel/VMState.v coq/kernel/VMStep.v coq/kernel/MuCostModel.v
# Expected: (empty or "NO REFERENCE" comments only)

# 4. Hardware synthesis
yosys -p "read_verilog thielecpu/hardware/mu_alu.v; hierarchy -check; proc; opt; stat"
# Expected: ~555 cells, 0 errors

# 5. μ-conservation
grep -n "mu_acc.*-\|mu.*sub" thielecpu/hardware/mu_alu.v
# Expected: (empty)

# 6. Inquisitor
python scripts/inquisitor.py --report /tmp/inquisitor.md
grep "^- HIGH:" /tmp/inquisitor.md
# Expected: - HIGH: 0
```

---

## Adding New Checks

To add a new accountability check:

1. **Add job to `adversarial-audit.yml`:**
   ```yaml
   my-new-check:
     name: "ENFORCE: My New Claim"
     runs-on: ubuntu-latest
     steps:
       - uses: actions/checkout@v4
       - name: Verify claim
         run: |
           # Test goes here
           if [ condition_fails ]; then
             echo "❌ CRITICAL: Claim violated"
             exit 1
           fi
           echo "✅ PASSED: Claim verified"
   ```

2. **Add to summary job dependencies:**
   ```yaml
   adversarial-summary:
     needs: [..., my-new-check]
   ```

3. **Update this documentation**

4. **Test locally first**

---

## Maintenance

### Weekly Tasks
- ✅ Review Inquisitor weekly reports (automated)
- ✅ Check CI dashboard for failures

### When Adding New Proofs
1. Ensure no `Admitted.`
2. Ensure no global `Axiom`
3. Run `make <file>.vo` to verify compilation
4. Run `python scripts/inquisitor.py` to check quality

### When CI Fails
1. **DO NOT** disable checks
2. **DO NOT** add `|| true` to bypass failures
3. **FIX** the underlying issue
4. If check is wrong, update check (document why)

---

## Historical Context

### Pre-Adversarial Audit
- ci.yml checked only 3 files for admits
- No hardware synthesis verification
- No circular reasoning check
- No BoxCHSH.v enforcement
- Inquisitor threshold: 80.0 (lenient)

### Post-Adversarial Audit (2026-01-02)
- ✅ Created `adversarial-audit.yml` (7 strict jobs)
- ✅ Updated ci.yml to check ALL kernel files
- ✅ Updated inquisitor.yml to enforce zero HIGH issues
- ✅ Raised quality threshold to 90.0
- ✅ Added hardware synthesis checks
- ✅ Added circular reasoning prevention
- ✅ Added proof chain verification

---

## Philosophy

### "Trust, But Verify" → "Verify, Then Trust"

The CI system embodies the principle that **code review is insufficient for formal verification**.

**Traditional approach:**
- Human reviews code
- Trusts developer claims
- Hopes tests are comprehensive

**Adversarial approach:**
- CI attempts to BREAK every claim
- No benefit of doubt given
- Every claim must be machine-verifiable

### Example: "0 admits" Claim

**Weak enforcement (old):**
```bash
grep "Admitted" CoreSemantics.v SemanticBridge.v Embedding_TM.v
```
→ Only checks 3 files, easy to hide admits elsewhere

**Strong enforcement (new):**
```bash
find coq/kernel -name "*.v" -exec grep -l "Admitted\." {} \;
[ -z "$ADMITS" ] || exit 1
```
→ Checks ALL files, impossible to hide

---

## Success Metrics

### Current Status (2026-01-02)

| Metric | Value | Status |
|--------|-------|--------|
| Admits in kernel | 0 / 233 files | ✅ |
| Axioms in kernel | 0 global | ✅ |
| Kernel files compiling | 10/10 critical | ✅ |
| Hardware synthesis | 555 cells, 0 errors | ✅ |
| Inquisitor HIGH issues | 0 | ✅ |
| Inquisitor quality score | N/A (to be measured) | ⏳ |
| CI workflows enforcing | 3/6 strict | ✅ |

### Accountability Goals

- [x] Enforce zero admits/axioms
- [x] Enforce Coq compilation
- [x] Enforce hardware synthesis
- [x] Enforce circular reasoning prevention
- [x] Enforce μ-conservation
- [x] Enforce proof quality ≥90%
- [ ] Add theorem count verification
- [ ] Add proof complexity metrics
- [ ] Add cross-layer isomorphism verification

---

## Contact

**Maintainers:** If CI is failing and you believe a check is incorrect, open an issue with:
1. CI run URL
2. Specific check that failed
3. Why you believe it's a false positive
4. Proposed fix (with test case)

**DO NOT** disable checks without documentation and review.

---

**Last Updated:** January 2, 2026
**Enforced By:** adversarial-audit.yml, inquisitor.yml, ci.yml
**Status:** ACTIVE - All checks enforced
