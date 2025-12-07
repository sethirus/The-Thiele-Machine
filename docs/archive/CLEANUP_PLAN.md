# Repository Cleanup Plan
**Author**: Devon Thiele  
**Date**: December 7, 2025  
**Status**: Planning Phase

## 🎯 Goal
Transform the repository from a messy development workspace into a clean, organized, professional project structure.

---

## 📊 Current State Analysis

### ✅ Essential Files (Keep & Organize)
```
Core Documentation:
├── README.md (main entry point)
├── ARCHITECTURE_AND_ALGORITHMS.md (technical deep dive)
├── LICENSE (Apache 2.0)
├── CONTRIBUTING.md (contributor guide)
├── CITATION.cff (academic citation)
└── CHANGELOG.md (version history)

Security & Trust:
├── SECURITY.md
├── SIGNING_AND_TRUST.md
├── GPG_PUBLIC_KEY.asc
└── CONTACT.txt

User Guides:
├── for-users-quickstart.md
├── for-maintainers-quickstart.md
├── REPLICATION_GUIDE.md
└── RECEIPT_GUIDE.md
```

### 🗑️ Redundant Documentation (Delete/Merge)
```
OLD STATUS REPORTS (outdated progress tracking):
❌ AUDIT_CONCLUSION_20251107.md
❌ AUDIT_STATUS_20251107_UPDATED.md  
❌ BELL_INEQUALITY_VERIFIED_RESULTS.md
❌ BELL_MILESTONES.md
❌ CLAIMS_VERIFICATION.md
❌ COMPILATION_NOTES.md
❌ COMPLETE_COMPILATION_REPORT.md
❌ COMPLETE_ISOMORPHISM_REPORT.md
❌ COQ_COMPILATION_STATUS.md
❌ DEPLOYMENT_READY.md
❌ FINAL_COMPLETION_SUMMARY.md
❌ Final_Audit_Report.md
❌ ISOMORPHISM_VERIFICATION.md
❌ ISOMORPHISM_VERIFICATION_REPORT.md
❌ MAXIMUM_COMPLETION_ACHIEVED.md
❌ PHASE_IMPLEMENTATION_SUMMARY.md
❌ PROJECT_COMPLETION_REPORT.md
❌ PROOF_COMPLETION_ROADMAP.md
❌ PROOF_PROGRESS_SUMMARY.md
❌ SECURITY_FIXES.md
❌ SUPRA_QUANTUM_VERIFICATION_SUMMARY.md
❌ THIELE_MACHINE_COMPREHENSIVE_REPORT.md
❌ VERIFICATION_REPORT.md
❌ VERIFICATION_SUMMARY.md

REDUNDANT BACKUPS:
❌ README_OLD_BACKUP.md
❌ ADMIT_REPORT.txt
❌ RECEIPT_CHANGELOG.md
❌ REORGANIZATION.md
❌ RESEARCH_PROGRAM_MASTER_PLAN.md

NEW BUT QUESTIONABLE:
⚠️ DEMO_EXPLANATIONS.md (merge into README?)
⚠️ FINAL_RIGOROUS_VERIFICATION.md (merge into docs?)
⚠️ RSA_DESTRUCTION_PROOF.txt (move to docs/theory/?)
⚠️ UNDENIABLE_DEMONSTRATION.txt (user guide or delete?)
```

### 📁 Directory Clutter (Consolidate)
```
EXPERIMENT OUTPUT DIRECTORIES:
├── random_3sat_vm_50/       ⚠️ Old experiment data
├── random_3sat_vm_100/      ⚠️ Old experiment data
├── random_3sat_vm_150/      ⚠️ Old experiment data
├── structured_tseitin_20/   ⚠️ Old experiment data
├── structured_tseitin_50/   ⚠️ Old experiment data
├── shor_demo_2047/          ⚠️ Old Shor demo results
├── shor_demo_10007/         ⚠️ Old Shor demo results
├── shor_demo_output/        ⚠️ Current Shor output
├── graph_demo_output/       ⚠️ Old demo output
├── shape_of_truth_out/      ⚠️ Unknown experiment
├── thesis_output/           ⚠️ Old academic work
├── stress_test_results/     ⚠️ Old test results
├── test_output/             ⚠️ Old test results
├── full_output/             ⚠️ Old comprehensive test
├── outputs/                 ⚠️ Generic output directory
├── tmp_vm_test/             ⚠️ Temporary test files
└── tsp_work/                ⚠️ TSP problem work

→ ACTION: Consolidate into results/archive/ or delete

DUPLICATE DIRECTORIES:
├── demo/ vs demos/          ⚠️ Which is current?
├── hardware/ vs thielecpu/hardware/  ⚠️ Duplicate Verilog?
├── experiments/ vs benchmarks/       ⚠️ Overlap?
├── archive/ vs strategies_backup/    ⚠️ Multiple archives?

→ ACTION: Merge duplicates

UNCLEAR PURPOSE:
├── catnet/                  ⚠️ What is this?
├── epoch_demo/              ⚠️ Demo or experiment?
├── forge/                   ⚠️ Build tool or misc?
├── grammar/                 ⚠️ Parser grammar?
├── kernel_public.key        ⚠️ What kernel?
├── kernel_secret.key        ⚠️ Should NOT be in repo!
├── liar_test/               ⚠️ Test or game?
├── objectives/              ⚠️ Old planning docs?
├── ouroboros/               ⚠️ Self-referential code?
├── packaging/               ⚠️ PyPI packaging?
├── problems/                ⚠️ Test problems or docs?
├── proof-of-thiele/         ⚠️ Original prototype?
├── proofpacks/              ⚠️ Proof bundles?
├── roadmap-enhancements/    ⚠️ Old feature planning?
├── sandboxes/               ⚠️ Experiments?
├── spec/                    ⚠️ Specifications?
├── supplementary_proofs/    ⚠️ Extra Coq proofs?
├── theory/                  ⚠️ Mathematical background?
├── verifier/                ⚠️ Receipt verification?

→ ACTION: Document purpose or delete
```

### 🔧 Build Artifacts (Delete/Gitignore)
```
Python Build:
├── __pycache__/             ❌ Delete (.gitignore)
├── .pytest_cache/           ❌ Delete (.gitignore)
├── .mypy_cache/             ❌ Delete (.gitignore)
├── .hypothesis/             ❌ Delete (.gitignore)
├── thiele_replay.egg-info/  ❌ Delete (.gitignore)
└── thiele_verify.egg-info/  ❌ Delete (.gitignore)

Coq Build:
├── .lia.cache               ❌ Delete (.gitignore)
├── .nra.cache               ❌ Delete (.gitignore)
└── build/                   ❌ Verify contents first

Logs:
├── sim.log                  ❌ Delete
├── sim_min.log              ❌ Delete
├── tmp_vm.log               ❌ Delete
├── derivation_log.txt       ❌ Delete
├── terminal_output.md       ❌ Delete
└── logs/                    ⚠️ Check if needed
```

### 📜 Standalone Scripts (Organize)
```
Root-level scripts:
├── create_receipt.py                    → Move to tools/
├── deep_audit_isomorphism.py           → Move to tools/audit/
├── demonstrate_isomorphism.py          → Move to demos/
├── demonstrate_phase2_composition.py   → Move to demos/
├── generate_phase3_receipt.py          → Move to tools/
├── run_ai_assistant.sh                 → Move to scripts/
├── run_experiment.py                   → Move to scripts/
├── run_phase2_actual_search.py         → Move to scripts/
├── stress_test_isomorphism.py          → Move to tests/
├── test_supra_quantum_complete.py      → Move to tests/
├── the_final_instrument.py             → Keep or move to tools/?
├── the_final_proof.py                  → Keep or move to tools/?
├── the_isomorphism.py                  → Keep or move to tools/?
├── thiele_verifier_min.py              → Move to tools/
├── verify_alu_integrity.py             → Move to tests/
├── verify_bell.sh                      → Move to scripts/
├── verify_complete_component_isomorphism.py → Move to tests/
├── verify_complete_isomorphism.py      → Move to tests/
├── verify_deep_isomorphism.py          → Move to tests/
├── verify_full_compilation.py          → Move to tests/
├── verify_rsa_destruction.py           → Move to demos/ or tools/
├── verify_web_pages.py                 → Move to scripts/
├── demo_complete_system.sh             → Move to scripts/
├── run_composition_experiments.py      → Move to scripts/
└── run_partition_experiments.py        → Move to scripts/
```

### 📦 Data Files (Consolidate)
```
JSON Data:
├── adaptive_hunt_history.json          → Move to results/
├── massive_hunt_results.json           → Move to results/
├── mu_bit_correlation_data.json        → Move to results/
├── protocol.json                       → Move to configs/
├── security_log.json                   → Move to logs/ (or delete)
└── tseitin_receipts.json              → Move to results/

CSV/Log Files:
├── tmp_vm.csv                          → Delete (temporary)
├── hello.txt                           → Delete (test file)
├── gitdiff.diff                        → Delete (temporary)
└── the_final_proof.sha256             → Keep with the_final_proof.py

Archives:
└── thiele_dossier.zip                 → Move to archive/releases/
```

---

## 🏗️ Proposed New Structure

```
The-Thiele-Machine/
│
├── README.md                           # Main entry point
├── LICENSE                             # Apache 2.0
├── ARCHITECTURE.md                     # Technical deep dive (renamed)
├── CHANGELOG.md                        # Version history
├── CONTRIBUTING.md                     # Contributor guide
├── CITATION.cff                        # Academic citation
├── pyproject.toml                      # Python packaging
├── requirements.txt                    # Python dependencies
├── Makefile                            # Build automation
├── .gitignore                          # Git ignore rules
│
├── docs/                               # All documentation
│   ├── quickstart/
│   │   ├── users.md                    # For users
│   │   └── maintainers.md              # For maintainers
│   ├── guides/
│   │   ├── replication.md              # Scientific replication
│   │   ├── receipts.md                 # Receipt system
│   │   └── demos.md                    # Demo explanations
│   ├── security/
│   │   ├── SECURITY.md                 # Security policy
│   │   ├── signing-and-trust.md        # GPG signing
│   │   └── GPG_PUBLIC_KEY.asc          # Public key
│   ├── theory/
│   │   ├── partition-computing.md      # Core theory
│   │   ├── supra-quantum.md            # Bell inequality
│   │   └── rsa-destruction.md          # Shor's algorithm
│   └── reference/
│       ├── instruction-set.md          # VM opcodes
│       ├── receipt-schema.md           # Receipt format
│       └── api.md                      # Python API
│
├── demos/                              # Executable demonstrations
│   ├── demo_impossible_logic.py        # 6 impossible demos
│   ├── demo_chsh_game.py               # CHSH game
│   ├── demo_isomorphism.py             # Tri-layer isomorphism
│   └── demo_shor_rsa.py                # RSA destruction
│
├── thielecpu/                          # Core VM implementation
│   ├── vm.py                           # Virtual machine
│   ├── state.py                        # State management
│   ├── instructions.py                 # Instruction set
│   ├── shor_oracle.py                  # Period finding
│   ├── hardware/                       # Verilog HDL
│   │   ├── thiele_cpu.v                # Main CPU
│   │   ├── mu_core.v                   # μ-Core enforcement
│   │   ├── mu_alu.v                    # μ-bit ALU
│   │   ├── testbenches/                # Test benches
│   │   └── synthesis/                  # FPGA synthesis
│   └── README.md                       # VM documentation
│
├── coq/                                # Formal proofs
│   ├── thielemachine/                  # Core semantics
│   ├── verification/                   # Hardware verification
│   └── README.md                       # Proof documentation
│
├── scripts/                            # Automation scripts
│   ├── experiments/
│   │   ├── run_partition_experiments.py
│   │   ├── run_composition_experiments.py
│   │   └── run_bell_experiments.py
│   ├── verification/
│   │   ├── verify_isomorphism.py
│   │   ├── verify_compilation.py
│   │   └── verify_bell.sh
│   └── build/
│       ├── build_verilog.sh
│       └── package_release.sh
│
├── tests/                              # Test suite
│   ├── test_vm.py                      # VM tests
│   ├── test_instructions.py            # Instruction tests
│   ├── test_supra_quantum.py           # CHSH tests
│   ├── test_isomorphism.py             # Tri-layer tests
│   ├── hardware/                       # Verilog tests
│   └── conftest.py                     # Pytest config
│
├── tools/                              # Utility tools
│   ├── receipt_generator.py            # Receipt creation
│   ├── thiele_verifier.py              # Receipt verification
│   ├── audit_tools.py                  # Security audit
│   └── benchmarks/                     # Performance tests
│
├── results/                            # Experimental results
│   ├── bell/                           # Bell inequality results
│   ├── partition/                      # Partition experiments
│   ├── shor/                           # Shor's algorithm results
│   └── archive/                        # Old experiment data
│       ├── 2025-11/                    # Archived by date
│       └── 2025-12/
│
├── configs/                            # Configuration files
│   ├── experiment_configs/             # Experiment parameters
│   └── vm_configs/                     # VM settings
│
├── artifacts/                          # Build artifacts
│   ├── receipts/                       # Generated receipts
│   ├── proofpacks/                     # Proof bundles
│   └── releases/                       # Release packages
│
├── web/                                # GitHub Pages website
│   └── (current structure)
│
└── .github/                            # GitHub config
    ├── workflows/                      # CI/CD
    └── ISSUE_TEMPLATE/                 # Issue templates
```

---

## 📋 Cleanup Action Plan

### Phase 1: Backup & Safety (Completed ✓)
1. [x] Git commit all current changes
2. [x] Create cleanup plan document
3. [ ] Create backup branch: `git checkout -b backup-before-cleanup`

### Phase 2: Delete Build Artifacts
```bash
# Delete Python build artifacts
rm -rf __pycache__/ .pytest_cache/ .mypy_cache/ .hypothesis/
rm -rf thiele_replay.egg-info/ thiele_verify.egg-info/

# Delete Coq caches
rm -f .lia.cache .nra.cache

# Delete temporary logs
rm -f sim.log sim_min.log tmp_vm.log derivation_log.txt terminal_output.md
rm -f tmp_vm.csv hello.txt gitdiff.diff
```

### Phase 3: Consolidate Documentation
```bash
# Create docs/ structure
mkdir -p docs/{quickstart,guides,security,theory,reference}

# Move existing docs
mv for-users-quickstart.md docs/quickstart/users.md
mv for-maintainers-quickstart.md docs/quickstart/maintainers.md
mv REPLICATION_GUIDE.md docs/guides/replication.md
mv RECEIPT_GUIDE.md docs/guides/receipts.md
mv SECURITY.md docs/security/
mv SIGNING_AND_TRUST.md docs/security/signing-and-trust.md
mv GPG_PUBLIC_KEY.asc docs/security/
mv receipt_schema.md docs/reference/receipt-schema.md
mv trs-spec-v1.md docs/reference/

# Merge and delete redundant docs
cat DEMO_EXPLANATIONS.md >> docs/guides/demos.md
rm DEMO_EXPLANATIONS.md
mv FINAL_RIGOROUS_VERIFICATION.md docs/theory/verification.md
mv RSA_DESTRUCTION_PROOF.txt docs/theory/rsa-destruction.md
mv UNDENIABLE_DEMONSTRATION.txt docs/theory/demonstrations.md

# Delete old status reports (all information in git history)
rm -f AUDIT_CONCLUSION_20251107.md AUDIT_STATUS_20251107_UPDATED.md
rm -f BELL_INEQUALITY_VERIFIED_RESULTS.md BELL_MILESTONES.md
rm -f CLAIMS_VERIFICATION.md COMPILATION_NOTES.md
rm -f COMPLETE_COMPILATION_REPORT.md COMPLETE_ISOMORPHISM_REPORT.md
rm -f COQ_COMPILATION_STATUS.md DEPLOYMENT_READY.md
rm -f FINAL_COMPLETION_SUMMARY.md Final_Audit_Report.md
rm -f ISOMORPHISM_VERIFICATION.md ISOMORPHISM_VERIFICATION_REPORT.md
rm -f MAXIMUM_COMPLETION_ACHIEVED.md PHASE_IMPLEMENTATION_SUMMARY.md
rm -f PROJECT_COMPLETION_REPORT.md PROOF_COMPLETION_ROADMAP.md
rm -f PROOF_PROGRESS_SUMMARY.md SECURITY_FIXES.md
rm -f SUPRA_QUANTUM_VERIFICATION_SUMMARY.md
rm -f THIELE_MACHINE_COMPREHENSIVE_REPORT.md
rm -f VERIFICATION_REPORT.md VERIFICATION_SUMMARY.md
rm -f README_OLD_BACKUP.md ADMIT_REPORT.txt
rm -f RECEIPT_CHANGELOG.md REORGANIZATION.md
rm -f RESEARCH_PROGRAM_MASTER_PLAN.md
```

### Phase 4: Organize Scripts
```bash
# Organize root-level scripts
mkdir -p scripts/{experiments,verification,build}
mv run_experiment.py scripts/experiments/
mv run_composition_experiments.py scripts/experiments/
mv run_partition_experiments.py scripts/experiments/
mv verify_bell.sh scripts/verification/
mv verify_complete_isomorphism.py scripts/verification/
mv verify_full_compilation.py scripts/verification/
mv demo_complete_system.sh scripts/
mv run_ai_assistant.sh scripts/

# Move demo scripts
mv demonstrate_isomorphism.py demos/demo_isomorphism.py
mv demonstrate_phase2_composition.py demos/demo_composition.py
mv verify_rsa_destruction.py demos/demo_shor_rsa.py

# Move test scripts
mkdir -p tests/hardware
mv stress_test_isomorphism.py tests/
mv test_supra_quantum_complete.py tests/
mv verify_alu_integrity.py tests/hardware/
mv verify_complete_component_isomorphism.py tests/
mv verify_deep_isomorphism.py tests/

# Move tool scripts
mkdir -p tools/audit
mv create_receipt.py tools/receipt_generator.py
mv generate_phase3_receipt.py tools/
mv deep_audit_isomorphism.py tools/audit/
mv thiele_verifier_min.py tools/thiele_verifier.py
```

### Phase 5: Consolidate Experiment Data
```bash
# Create results archive structure
mkdir -p results/archive/2025-11

# Move old experiment directories
mv random_3sat_vm_50/ results/archive/2025-11/
mv random_3sat_vm_100/ results/archive/2025-11/
mv random_3sat_vm_150/ results/archive/2025-11/
mv structured_tseitin_20/ results/archive/2025-11/
mv structured_tseitin_50/ results/archive/2025-11/
mv shor_demo_2047/ results/archive/2025-11/
mv shor_demo_10007/ results/archive/2025-11/
mv graph_demo_output/ results/archive/2025-11/
mv shape_of_truth_out/ results/archive/2025-11/
mv thesis_output/ results/archive/2025-11/
mv stress_test_results/ results/archive/2025-11/
mv test_output/ results/archive/2025-11/
mv full_output/ results/archive/2025-11/
mv tmp_vm_test/ results/archive/2025-11/

# Keep current experiment outputs
mv shor_demo_output/ results/shor/
mv outputs/ results/current/

# Move data files
mv adaptive_hunt_history.json results/archive/
mv massive_hunt_results.json results/archive/
mv mu_bit_correlation_data.json results/
mv tseitin_receipts.json results/archive/
mv security_log.json logs/ || rm security_log.json
mv protocol.json configs/
```

### Phase 6: Investigate & Document Unclear Directories
```bash
# For each unclear directory, document its purpose or delete
# This requires manual inspection:
ls -la catnet/          # Document or delete
ls -la epoch_demo/      # Document or delete
ls -la forge/           # Document or delete
ls -la grammar/         # Document or delete
ls -la liar_test/       # Document or delete
ls -la objectives/      # Document or delete
ls -la ouroboros/       # Document or delete
ls -la proof-of-thiele/ # Document or delete
ls -la sandboxes/       # Document or delete
ls -la spec/            # Document or delete
ls -la theory/          # Document or delete
```

### Phase 7: Merge Duplicate Directories
```bash
# demo/ vs demos/ - keep demos/
if [ -d demo/ ]; then
    cp -r demo/* demos/ 2>/dev/null || true
    rm -rf demo/
fi

# hardware/ vs thielecpu/hardware/ - keep thielecpu/hardware/
if [ -d hardware/ ]; then
    # Check for differences first
    diff -r hardware/ thielecpu/hardware/ || echo "Differences found!"
    # Merge manually if needed
fi

# experiments/ vs benchmarks/ - check overlap
if [ -d experiments/ ] && [ -d benchmarks/ ]; then
    # Manual inspection needed
    ls experiments/
    ls benchmarks/
fi
```

### Phase 8: Update .gitignore
```bash
# Add to .gitignore:
echo "
# Python
__pycache__/
*.py[cod]
*$py.class
.pytest_cache/
.mypy_cache/
.hypothesis/
*.egg-info/

# Coq
.lia.cache
.nra.cache
*.vo
*.vok
*.vos
*.glob
*.aux

# Logs
*.log
sim*.log
tmp_*.log

# Temporary files
tmp_*/
*.tmp
*.bak

# Build artifacts
build/
dist/
*.o
*.so

# Results (keep structure, ignore data)
results/archive/*/
results/*/output/
results/*/*.json
results/*/*.csv

# Secrets (should never be committed!)
*_secret.key
*.pem
*.key
!GPG_PUBLIC_KEY.asc
" >> .gitignore
```

### Phase 9: Update All Documentation Links
```bash
# Update references in README.md, docs/, and scripts
# This requires find/replace:
# - for-users-quickstart.md → docs/quickstart/users.md
# - REPLICATION_GUIDE.md → docs/guides/replication.md
# - etc.

# Semi-automated with sed:
find . -type f -name "*.md" -exec sed -i 's|for-users-quickstart.md|docs/quickstart/users.md|g' {} +
find . -type f -name "*.md" -exec sed -i 's|REPLICATION_GUIDE.md|docs/guides/replication.md|g' {} +
# ... etc for all moved files
```

### Phase 10: Final Verification
```bash
# Run all tests
python -m pytest tests/

# Check demos still work
python demos/demo_impossible_logic.py --demo 1

# Verify Coq compilation (if applicable)
make -C coq/

# Check for broken links
# (use a tool like markdown-link-check)

# Verify git status
git status
```

---

## 🚨 High-Priority Items

### Security Issues
1. **CRITICAL**: `kernel_secret.key` - Should NEVER be in repo!
   - If this is a real secret key, it's compromised
   - Remove immediately and regenerate
   - Add `*.key` to .gitignore
   - Check git history: `git log --all --full-history -- kernel_secret.key`
   - If committed, need to purge from history or rotate keys

2. **Verify**: Check all JSON/log files for secrets
   - `security_log.json` - any sensitive data?
   - `protocol.json` - any API keys?
   - `*.json` in root - check contents

### Critical Decisions Needed
1. **What to do with `the_final_*.py` files?**
   - Are these essential tools or old experiments?
   - Keep in root or move to tools/?

2. **Hardware directory duplication:**
   - Is `hardware/` a duplicate of `thielecpu/hardware/`?
   - Which is canonical?

3. **Unclear directories purpose:**
   - Need to inspect each and document or delete

---

## ✅ Success Criteria

After cleanup, the repository should:
1. ✓ Have clear directory structure (docs/, demos/, thielecpu/, tests/, etc.)
2. ✓ No build artifacts in repo (all in .gitignore)
3. ✓ No duplicate directories
4. ✓ All scripts organized by purpose
5. ✓ Old experiment data archived or deleted
6. ✓ Documentation links all work
7. ✓ All tests pass
8. ✓ No secrets in repo
9. ✓ README points to correct paths
10. ✓ CI/CD still works

---

## 📝 Notes

- **Before executing**: Review each phase carefully
- **Backup**: Keep `backup-before-cleanup` branch
- **Test frequently**: Run tests after each phase
- **Git commit**: Commit after each successful phase
- **Reversible**: Use `git mv` instead of `mv` to preserve history

---

## 🤝 Next Steps

1. Review this plan
2. Get approval for deletions
3. Create backup branch
4. Execute Phase 2 (safe deletions)
5. Commit and test
6. Continue phase by phase
7. Final verification
8. Update README with new structure
