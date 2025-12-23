# Inquisitor Guide: Comprehensive Coq Proof Auditing

## Overview

The Inquisitor is a scorched-earth static analysis system for Coq proofs that detects proof shortcuts, hidden assumptions, vacuous statements, and quality issues. This guide covers all three components:

1. **Base Inquisitor** (`inquisitor.py`) - Core auditing engine
2. **Advanced Inquisitor** (`inquisitor_advanced.py`) - Extended analysis modules
3. **Inquisitor Analyzer** (`inquisitor_analyze.py`) - Report analysis and insights

---

## Quick Start

### Run Basic Audit

```bash
python scripts/inquisitor.py --strict
```

This generates `INQUISITOR_REPORT.md` with all findings.

### Generate Analysis Report

```bash
python scripts/inquisitor_analyze.py
```

This generates `INQUISITOR_ANALYSIS.md` with insights and recommendations.

### Run Enhanced Audit (with advanced analysis)

```bash
python scripts/inquisitor_enhanced.py --only-coq-roots --coq-root coq/kernel
```

---

## Base Inquisitor Rules

The base Inquisitor detects 20+ categories of proof issues:

### FORBIDDEN (HIGH Severity - CI Fails)

| Rule | Description | Example |
|------|-------------|---------|
| `ADMITTED` | Incomplete proof | `Theorem foo : P. Proof. ... Admitted.` |
| `ADMIT_TACTIC` | Proof shortcut | `Proof. admit. Qed.` |
| `GIVE_UP_TACTIC` | Proof abandonment | `... give_up ...` |
| `AXIOM_OR_PARAMETER` | Unproven global assumption | `Axiom magic : forall P, P.` |
| `PROP_TAUTOLOGY` | Statement is literally True | `Theorem foo : True.` |
| `IMPLIES_TRUE_STMT` | Vacuous implication | `Theorem foo : P -> True.` |
| `LET_IN_TRUE_STMT` | Hidden vacuity | `Theorem foo : let x := ... in True.` |
| `EXISTS_TRUE_STMT` | Vacuous existence | `Theorem foo : exists x, True.` |
| `TRUE_CONST` | Trivial constant | `Definition foo := True.` |
| `CONST_Q_FUN` | Constant probability witness | `Definition p := fun _ => 1%Q.` |
| `EXISTS_CONST_Q` | Constant witness in proof | `exists (fun _ => 0%Q)` |
| `PHYSICS_ANALOGY_CONTRACT` | Physics theorem lacks invariance | Missing Noether lemma for symmetry claim |

### FLAGGED (MEDIUM Severity - Reviewed)

| Rule | Description | Example |
|------|-------------|---------|
| `COST_IS_LENGTH` | Cost defined as list length | `Definition cost := length trace.` |
| `EMPTY_LIST` | Trivial empty list | `Definition results := [].` |
| `ZERO_CONST` | Constant zero | `Definition min_cost := 0.` |
| `CLAMP_OR_TRUNCATION` | Uses clamps/truncations | `Z.to_nat`, `Z.abs`, `Nat.min` |
| `Z_TO_NAT_BOUNDARY` | Z.to_nat without guard | Missing `>= 0` check |
| `COMMENT_SMELL` | TODO/FIXME/WIP markers | `(* TODO: prove this *)` |
| `UNUSED_HYPOTHESIS` | Introduced but not used | `intros H. reflexivity.` (H unused) |
| `DEFINITIONAL_INVARIANCE` | Trivial invariance lemma | Proved by `reflexivity` |
| `HYPOTHESIS_ASSUME` | Local assumption | Escalates to HIGH for suspicious names |

### DETECTED (LOW Severity - Informational)

| Rule | Description |
|------|-------------|
| `CIRCULAR_INTROS_ASSUMPTION` | Tautology proved by intros; assumption |
| `TRIVIAL_EQUALITY` | X = X proved by reflexivity |
| `SECTION_BINDER` | Context/Variable declarations |
| `MODULE_SIGNATURE_DECL` | Module Type requirements |

---

## Advanced Inquisitor Features

### 1. Proof Complexity Analysis

Detects overly long or complex proofs:

**Rules:**

| Rule | Threshold | Severity |
|------|-----------|----------|
| `PROOF_TOO_LONG` | > 100 lines | MEDIUM |
| `PROOF_TOO_COMPLEX` | > 50 tactics | MEDIUM |
| `PROOF_DEEP_NESTING` | > 5 depth | LOW |

**Configurable:**

```bash
python scripts/inquisitor_enhanced.py --max-proof-lines 80 --max-tactics 40
```

**Why it matters:** Long/complex proofs are:
- Hard to maintain
- Fragile to changes
- Difficult to understand
- Potential hiding bugs

### 2. Tactic Anti-Patterns

Detects suspicious proof tactic usage:

**Rules:**

| Rule | Description | Example |
|------|-------------|---------|
| `EXCESSIVE_AUTOMATION` | Proof is just automation | `Proof. auto. Qed.` |
| `REPEATED_TACTIC_PATTERN` | Copy-paste proof pattern | 4+ identical tactics in sequence |
| `ADMIT_THEN_TACTICS` | Tactics after admit | `admit. apply H.` (suspicious!) |

**Why it matters:**
- Excessive automation makes proofs fragile
- Repeated patterns suggest need for Ltac abstraction
- Tactics after `admit` indicate likely errors

### 3. Dead Code Detection

Finds potentially unused definitions, lemmas, theorems:

**Rule:** `POTENTIALLY_DEAD_DEF`

**Heuristic:** Scans entire repo for references. If a definition appears only once (its own definition), flags as potentially dead.

**Limitations:**
- May miss dynamic references
- Expensive (scans all files for each definition)
- Run selectively with `--enable-dead-code`

**Why it matters:** Dead code:
- Clutters the development
- Creates maintenance burden
- May indicate incomplete refactoring

### 4. Import/Dependency Analysis

Analyzes module imports:

**Rules:**

| Rule | Description |
|------|-------------|
| `POTENTIALLY_UNUSED_IMPORT` | Module imported but not used |
| `DUPLICATE_IMPORT` | Same module imported multiple times |

**Why it matters:**
- Unused imports slow compilation
- Duplicates suggest disorganization
- Helps identify circular dependencies

### 5. Naming Convention Validation

Checks adherence to naming standards:

**Rules:**

| Rule | Description | Example |
|------|-------------|---------|
| `INCONSISTENT_NAMING` | Mixed camelCase and snake_case | `myTheorem_With_Underscores` |
| `ALL_CAPS_THEOREM` | Theorem in ALL_CAPS | `Theorem MAIN_RESULT : ...` |

**Why it matters:** Consistent naming improves readability and maintainability.

### 6. Proof Obligation Tracking

Tracks completion rate of proofs:

**Rule:** `LOW_PROOF_COMPLETION`

**Metric:** `(Qed count) / (Qed + Admitted count) * 100%`

**Threshold:** < 80% completion rate

**Why it matters:** Tracks progress on proof obligations systematically.

---

## Inquisitor Analyzer

The analyzer generates actionable insights from Inquisitor reports.

### Features

1. **Executive Summary**
   - Total findings count
   - Severity breakdown
   - Quality score (0-100)
   - Letter grade (A-F)

2. **Key Insights**
   - Categorized findings with recommendations
   - Prioritized by severity and impact

3. **Top Issues by Category**
   - Ranked list of most common issues
   - Files affected count

4. **Highest Impact Files**
   - Files with most findings
   - Refactoring candidates

5. **Vacuity Analysis**
   - Files with placeholder/incomplete proofs
   - Scored by severity

6. **Prioritized Remediation Plan**
   - Phase 1: Critical issues (HIGH)
   - Phase 2: Code quality (MEDIUM)
   - Phase 3: Maintenance (LOW)

### Quality Score Formula

```
quality_score = 100 - min(100, (HIGH_count * 2 + MEDIUM_count) / scanned_files)
```

### Grading Scale

| Score | Grade | Meaning |
|-------|-------|---------|
| 90-100 | A | Excellent |
| 80-89 | B | Good |
| 70-79 | C | Fair |
| 60-69 | D | Needs Improvement |
| 0-59 | F | Critical Issues |

---

## Configuration

### Manifest File: `coq/INQUISITOR_ASSUMPTIONS.json`

The manifest configures:

1. **Assumption Audits** - Verify axioms via `Print Assumptions`
2. **Paper Symbol Map** - Map paper notation to Coq symbols
3. **Symmetry Contracts** - Require equivariance lemmas for symmetries

Example:

```json
{
  "coqproject": "coq/_CoqProject",
  "allow_axioms": [
    "functional_extensionality",
    "proof_irrelevance"
  ],
  "targets": [
    {
      "require": "Kernel.NoFreeInsight",
      "symbol": "no_free_insight_general"
    }
  ],
  "paper_map": [
    {
      "require": "Kernel.MuLedger",
      "symbol": "mu_conservation_kernel"
    }
  ],
  "symmetry_contracts": [
    {
      "file_regex": ".*Noether.*",
      "must_contain_regex": [".*equivariance.*", ".*gauge.*"],
      "tag": "gauge symmetry"
    }
  ]
}
```

### Allowlisting

Use `--allowlist` to skip findings in:
- `/archive/` - Deprecated code
- `/scratch/` - Experimental work
- `/WIP/` - Work in progress
- Files marked `OPTIONAL_VO` in `coq/Makefile.local`

```bash
python scripts/inquisitor.py --allowlist --allowlist-makefile-optional
```

---

## CI Integration

### GitHub Actions Example

```yaml
- name: Run Inquisitor
  run: |
    python scripts/inquisitor.py --strict --build
    python scripts/inquisitor_analyze.py

- name: Upload Reports
  uses: actions/upload-artifact@v3
  with:
    name: inquisitor-reports
    path: |
      INQUISITOR_REPORT.md
      INQUISITOR_ANALYSIS.md
```

### Exit Codes

| Code | Meaning |
|------|---------|
| 0 | Success (or findings only in allowlisted paths) |
| 1 | HIGH findings in protected files (`--strict` mode) |
| 2 | Configuration error (missing coq root, etc.) |

---

## Best Practices

### 1. Run Regularly

- Pre-commit: `inquisitor.py --only-coq-roots --coq-root <changed-files>`
- CI: `inquisitor.py --strict --build`
- Weekly: `inquisitor_enhanced.py` with full analysis

### 2. Track Trends

Keep historical reports to track:
- Reduction in HIGH findings
- Improvement in quality score
- Proof completion rate

### 3. Address Critical First

Prioritize:
1. `ADMITTED` proofs
2. Vacuous statements (`IMPLIES_TRUE_STMT`, etc.)
3. Undocumented axioms
4. Physics contracts without invariance

### 4. Don't Over-Optimize

LOW severity findings are informational. Focus on:
- Correctness (HIGH)
- Maintainability (MEDIUM)
- Ignore LOW unless cleaning up

### 5. Document Exceptions

When allowlisting:
- Add comments explaining why
- Create tracking issues
- Set deadlines for resolution

---

## Extending the Inquisitor

### Adding New Rules

1. **Edit `inquisitor_advanced.py`:**

```python
def scan_my_new_rule(path: Path) -> list[Finding]:
    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_coq_comments(raw)
    findings = []

    # Your detection logic here
    pattern = re.compile(r"...")
    for m in pattern.finditer(text):
        findings.append(Finding(...))

    return findings
```

2. **Integrate in `inquisitor_enhanced.py`:**

```python
all_findings.extend(scan_my_new_rule(vf))
```

3. **Document in Rules section above**

### Adding New Insights

Edit `inquisitor_analyze.py`:

```python
def generate_insights(data: Dict) -> List[AnalysisInsight]:
    insights = []

    # Your insight logic
    if "MY_RULE" in findings_by_rule:
        insights.append(AnalysisInsight(...))

    return insights
```

---

## Troubleshooting

### "coqtop not found"

The manifest-based assumption audits require `coqtop`. Install Coq or disable:

```bash
python scripts/inquisitor.py --manifest /dev/null
```

### "Inquisitor crashed scanning file"

Check `INTERNAL_ERROR` findings in report. Usually caused by:
- Malformed Coq syntax
- Non-UTF8 encoding
- Extremely large proofs (>10000 lines)

### Slow Performance

Dead code detection is expensive. Skip it:

```bash
# Advanced analysis without dead code detection
python scripts/inquisitor_enhanced.py --no-dead-code
```

Or scan subset:

```bash
python scripts/inquisitor.py --only-coq-roots --coq-root coq/kernel
```

---

## Examples

### Full Audit Pipeline

```bash
# 1. Run base audit
python scripts/inquisitor.py --strict --build

# 2. Generate analysis
python scripts/inquisitor_analyze.py

# 3. Review outputs
cat INQUISITOR_ANALYSIS.md

# 4. Create issues for HIGH findings
grep "🔴 \*\*HIGH" INQUISITOR_ANALYSIS.md
```

### Custom Thresholds

```bash
# More lenient (for large legacy codebases)
python scripts/inquisitor_enhanced.py \
    --max-proof-lines 200 \
    --max-tactics 100

# Stricter (for new developments)
python scripts/inquisitor_enhanced.py \
    --max-proof-lines 50 \
    --max-tactics 30
```

### Focused Analysis

```bash
# Just the kernel
python scripts/inquisitor.py \
    --only-coq-roots \
    --coq-root coq/kernel \
    --report KERNEL_AUDIT.md

# Just physics proofs
python scripts/inquisitor.py \
    --only-coq-roots \
    --coq-root coq/physics \
    --report PHYSICS_AUDIT.md
```

---

## Summary

The Inquisitor suite provides:

✅ **Comprehensive auditing** - 20+ rule categories
✅ **Advanced analysis** - Complexity, dead code, tactics
✅ **Actionable insights** - Prioritized recommendations
✅ **Quality scoring** - Objective metrics (0-100)
✅ **Flexible configuration** - Manifests, allowlists, thresholds
✅ **CI-ready** - Exit codes, reports, automation

**Goal:** Maintain the highest standard of proof correctness and code quality in the Thiele Machine development.

---

*For questions or issues, see the main project README or open a GitHub issue.*
