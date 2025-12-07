# Complete Directory Audit & Source Mapping
**Date**: December 7, 2025  
**Purpose**: Map every directory to its source, analyze contents, and fix output paths

## 🔍 Audit Methodology
1. Identify directory contents
2. Search codebase for creation source
3. Verify current usage
4. Document fix needed (if any)
5. Proposed action (keep/archive/delete)

---

## 📊 Status Legend
- 🟢 **CLEAN** - Properly organized, no action needed
- 🟡 **AUDIT** - Needs investigation
- 🟠 **FIX** - Source code needs output path fix
- 🔴 **DELETE** - Old/temporary data, safe to remove
- 🔵 **ARCHIVE** - Historical data, move to archive/

---

## 📁 Directory Analysis

### Core Directories (Keep)

#### `thielecpu/` 🟢 CLEAN
**Contents**: VM implementation (vm.py, state.py, instructions.py, shor_oracle.py)  
**Source**: Core package, manually maintained  
**Usage**: Active - imported by all demos and tests  
**Fix Needed**: None  
**Action**: ✅ Keep as-is

#### `coq/` 🟢 CLEAN
**Contents**: Formal proofs (115 .v files, 54,773 lines)  
**Source**: Manual proof development  
**Usage**: Active - proof compilation via Makefile  
**Fix Needed**: None  
**Action**: ✅ Keep as-is

#### `demos/` 🟢 CLEAN
**Contents**: 
- demo_impossible_logic.py (6 demos, 1,997 lines)
- demo_chsh_game.py
**Source**: Recently created/organized  
**Usage**: Active - main demonstration suite  
**Fix Needed**: None  
**Action**: ✅ Keep as-is

#### `tests/` 🟢 CLEAN
**Contents**: pytest suite  
**Source**: Test infrastructure  
**Usage**: Active - CI/CD pipeline  
**Fix Needed**: None  
**Action**: ✅ Keep as-is

#### `scripts/` 🟢 CLEAN
**Contents**: Automation scripts  
**Source**: Manual organization  
**Usage**: Active  
**Fix Needed**: None  
**Action**: ✅ Keep as-is

---

### Output Directories (Need Source Mapping)

#### ✅ FIXED: `stress_test_results/` → `results/stress_tests/`
**Contents**: 17 files, 72K (created Dec 1, 2025 - RECENT)
**Source**: stress_test_isomorphism.py:455  
**Status**: ✅ **FIXED** - Updated to use `results/stress_tests/`  
**Action**: Archive old data after testing fix

#### ✅ FIXED: `shor_demo_output/` → `results/shor/`
**Contents**: 6 files, 40K (created Oct 19, 2025)
**Source**: scripts/shor_on_thiele_demo.py (default arg)  
**Status**: ✅ **FIXED** - Updated default to `results/shor/`  
**Action**: Archive old data after testing fix

#### ✅ FIXED: `graph_demo_output/` → `results/graphs/`
**Contents**: 35 files, 312K (created Oct 19, 2025)
**Source**: scripts/graph_coloring_demo.py (default arg)  
**Status**: ✅ **FIXED** - Updated default to `results/graphs/`  
**Action**: Archive old data after testing fix

#### ✅ FIXED: `shape_of_truth_out/` → `results/proofs/`
**Contents**: 9 files, 84K (created Oct 10, 2025)
**Source**: demos/research-demos/problem-solving/attempt.py (10 occurrences)  
**Status**: ✅ **FIXED** - All 10 references updated to `results/proofs/`  
**Action**: Archive old data after testing fix

#### 🟠 FIX NEEDED: `tsp_work/`
**Contents**: 2 subdirs (test5, test_8cities) - created Dec 3, 2025
**Source**: scripts/tsp_optimizer.py:505 - `work_base = Path("tsp_work") / tsp_file.stem`  
**Status**: 🟠 **NEEDS FIX**  
**Fix**: Change to `Path("results/tsp") / tsp_file.stem`  
**Action**: Fix source, then archive old data

#### 🔵 ARCHIVE: `random_3sat_vm_50/`, `random_3sat_vm_100/`, `random_3sat_vm_150/`
**Contents**: 1 file each (trace.log), 2.6K-7.3K (created Nov 2, 2025)
**Source**: demos/research-demos/architecture/populate_observatory.py (dynamic naming via CLI args)  
**Last Modified**: Nov 2, 2025  
**Status**: OLD - No hardcoded paths found, uses --output-dir CLI arg  
**Fix**: None needed - script already parameterized  
**Action**: 🔵 Archive to `results/archive/2025-11/`

#### 🔵 ARCHIVE: `structured_tseitin_20/`, `structured_tseitin_50/`
**Contents**: 1 file each (trace.log), 1.5K-4.8K (created Nov 2, 2025)
**Source**: demos/research-demos/architecture/populate_observatory.py (same as random_3sat_vm_*)  
**Status**: OLD - Script already uses CLI args properly  
**Action**: 🔵 Archive to `results/archive/2025-11/`

#### 🟡 INVESTIGATE: `outputs/`
**Contents**: 2 files (rtl_log.log, vm_receipt.json) - created Oct 25, 2025
**Source**: Old VM/RTL comparison data (compare_vm_rtl.py reads these)  
**Status**: OLD - comparison artifacts from October  
**Action**: 🔵 Archive to `results/archive/2025-10/`

#### 🔵 ARCHIVE: `tmp_vm_test/`
**Contents**: 1 subdir (Final.thiele.modules4...) - created Nov 25, 2025
**Source**: Test/temporary directory (likely from VM tests)  
**Status**: TEMPORARY - safe to clean up  
**Action**: 🔵 Archive or delete

#### 🔵 ARCHIVE: `thesis_output/` (39MB!)
**Contents**: 49 files including experiments/ subdir with receipts, plots, CSVs
**Source**: LaTeX thesis compilation + partition experiments  
**Last Modified**: Nov 12, 2025  
**Status**: OLD - thesis experiment artifacts  
**Action**: 🔵 Archive to `results/archive/2025-11/thesis_output/`

#### 🔵 ARCHIVE: `shor_demo_2047/`, `shor_demo_10007/`
**Contents**: Empty except for "act_ii" file  
**Source**: Old shor_on_thiele_demo.py runs (same script now fixed)  
**Status**: OLD - from before output path fix  
**Action**: 🔵 Archive to `results/archive/2025-10/`

#### 🟢 KEEP: `forge/`
**Contents**: Grammar-guided equation discovery package (grammar_crawler.py, 643 lines)
**Source**: Manual development - proper Python package with __init__.py  
**Usage**: ACTIVE - equation discovery from atomic primitives  
**Status**: CORE PACKAGE - like thielecpu/  
**Action**: ✅ Keep as-is (not an output directory)

#### 🟡 INVESTIGATE: `catnet/`
**Contents**: Python package stub (__pycache__ only)  
**Source**: Unknown - no .py files found  
**Status**: Empty package directory  
**Action**: 🔴 DELETE (empty except pycache)

#### 🟡 INVESTIGATE: `epoch_demo/`
**Contents**: 2 files (side_by_side.png, table.csv)  
**Source**: Unknown demo output  
**Status**: OLD - needs source investigation  
**Action**: 🔵 Archive to `results/archive/2025-11/`
**Source Found**: [To be determined]  
**Fix Needed**: Update script to use `results/tseitin/` output  
**Action**: 🔵 Archive to `results/archive/2025-11/`

#### `structured_tseitin_50/` 🔴 DELETE
**Source**: Same as structured_tseitin_20  
**Action**: 🔵 Archive to `results/archive/2025-11/`

#### `shor_demo_2047/` 🔴 DELETE
**Contents**: Shor's algorithm demo output for N=2047  
**Source**: Likely `verify_rsa_destruction.py` or Shor demo script  
**Searching for source...**
```bash
grep -r "shor_demo" --include="*.py"
```
**Fix Needed**: Update to use `results/shor/N_2047/` pattern  
**Action**: 🔵 Archive to `results/archive/2025-11/`

#### `shor_demo_10007/` 🔴 DELETE
**Source**: Same as shor_demo_2047  
**Action**: 🔵 Archive to `results/archive/2025-11/`

#### `shor_demo_output/` 🟠 FIX
**Contents**: Current Shor demo output  
**Source**: Active Shor demonstrations  
**Usage**: CURRENT - recently used  
**Fix Needed**: Rename to `results/shor/current/`  
**Action**: 🟠 Move to `results/shor/current/` + fix source code

#### `graph_demo_output/` 🔴 DELETE
**Contents**: Graph partitioning demo results  
**Source**: [To be determined]  
**Fix Needed**: Update source to use `results/graphs/`  
**Action**: 🔵 Archive to `results/archive/2025-11/`

#### `shape_of_truth_out/` 🟡 AUDIT
**Contents**: [Need to check]  
**Source**: Unknown - needs investigation  
**Fix Needed**: TBD  
**Action**: 🟡 Investigate first

#### `thesis_output/` 🔴 DELETE
**Contents**: Academic thesis generation output  
**Source**: Old academic work  
**Fix Needed**: None (discontinued)  
**Action**: 🔵 Archive to `results/archive/2025-11/`

#### `stress_test_results/` 🔴 DELETE
**Contents**: Stress test data  
**Source**: `stress_test_isomorphism.py`  
**Fix Needed**: Update script to use `results/stress_tests/`  
**Action**: 🔵 Archive to `results/archive/2025-11/`

#### `test_output/` 🔴 DELETE
**Contents**: Generic test output  
**Source**: Various test scripts  
**Fix Needed**: Use pytest's built-in output capture  
**Action**: 🔵 Archive to `results/archive/2025-11/`

#### `full_output/` 🔴 DELETE
**Contents**: Comprehensive test suite output  
**Source**: [To be determined]  
**Fix Needed**: TBD  
**Action**: 🔵 Archive to `results/archive/2025-11/`

#### `outputs/` 🟠 FIX
**Contents**: Generic output directory  
**Source**: Multiple scripts using this as fallback  
**Fix Needed**: All scripts should use specific results/ subdirs  
**Action**: 🟠 Review contents, archive, fix all sources

#### `tmp_vm_test/` 🔴 DELETE
**Contents**: Temporary VM test files  
**Source**: Temporary test data  
**Fix Needed**: Use /tmp/ or pytest tmpdir  
**Action**: 🔴 Delete (temporary data)

#### `tsp_work/` 🟡 AUDIT
**Contents**: Traveling Salesman Problem work  
**Source**: TSP experiments  
**Fix Needed**: TBD  
**Action**: 🟡 Investigate - is this active research?

---

### Ambiguous/Unknown Directories (Need Investigation)

#### `catnet/` 🟡 AUDIT
**Checking contents...**
```bash
ls -la catnet/
find catnet/ -type f | head -10
```
**Purpose**: [Unknown - needs investigation]  
**Source**: [To be determined]  
**Action**: 🟡 INVESTIGATE FIRST

#### `epoch_demo/` 🟡 AUDIT
**Purpose**: [Unknown - demo or experiment?]  
**Action**: 🟡 INVESTIGATE FIRST

#### `forge/` 🟡 AUDIT
**Purpose**: [Build tool? Misc utilities?]  
**Action**: 🟡 INVESTIGATE FIRST

#### `grammar/` 🟡 AUDIT
**Purpose**: [Parser grammar? Language spec?]  
**Action**: 🟡 INVESTIGATE FIRST

#### `liar_test/` 🟡 AUDIT
**Purpose**: [Test or logical paradox demo?]  
**Action**: 🟡 INVESTIGATE FIRST

#### `objectives/` 🟡 AUDIT
**Purpose**: [Old planning docs?]  
**Action**: 🟡 INVESTIGATE FIRST

#### `ouroboros/` 🟡 AUDIT
**Purpose**: [Self-referential code?]  
**Action**: 🟡 INVESTIGATE FIRST

#### `packaging/` 🟡 AUDIT
**Purpose**: [PyPI packaging?]  
**Action**: 🟡 INVESTIGATE - may be needed for releases

#### `problems/` 🟡 AUDIT
**Purpose**: [Test problems or documentation?]  
**Action**: 🟡 INVESTIGATE FIRST

#### `proof-of-thiele/` 🟡 AUDIT
**Purpose**: [Original prototype?]  
**Action**: 🟡 INVESTIGATE - historical significance?

#### `proofpacks/` 🟡 AUDIT
**Purpose**: [Proof bundles?]  
**Action**: 🟡 INVESTIGATE FIRST

#### `roadmap-enhancements/` 🔴 DELETE
**Purpose**: Old feature planning  
**Action**: 🔴 DELETE (superseded by current roadmap)

#### `sandboxes/` 🟡 AUDIT
**Purpose**: [Experimental code?]  
**Action**: 🟡 INVESTIGATE - may contain useful experiments

#### `spec/` 🟡 AUDIT
**Purpose**: [Specifications?]  
**Action**: 🟡 INVESTIGATE - may be important docs

#### `supplementary_proofs/` 🟡 AUDIT
**Purpose**: Extra Coq proofs not in coq/?  
**Action**: 🟡 INVESTIGATE - merge into coq/ or keep separate?

#### `theory/` 🟡 AUDIT
**Purpose**: Mathematical background docs  
**Action**: 🟡 INVESTIGATE - merge into docs/theory/?

#### `verifier/` 🟡 AUDIT
**Purpose**: Receipt verification tools  
**Action**: 🟡 INVESTIGATE - merge into tools/?

---

### Duplicate Directories (Need Reconciliation)

#### `demo/` vs `demos/` 🟠 FIX
**Investigation needed**: Are they duplicates or different?
```bash
# Check if demo/ exists and compare
if [ -d demo/ ]; then
    diff -qr demo/ demos/ || echo "DIFFERENT"
    ls -la demo/
fi
```
**Action**: 🟠 Compare and merge

#### `hardware/` vs `thielecpu/hardware/` 🟠 FIX
**Investigation needed**: Which is canonical?
```bash
if [ -d hardware/ ]; then
    diff -qr hardware/ thielecpu/hardware/ || echo "DIFFERENT"
fi
```
**Action**: 🟠 Compare and merge

#### `experiments/` vs `benchmarks/` 🟠 FIX
**Investigation needed**: Overlap?
```bash
ls experiments/
ls benchmarks/
```
**Action**: 🟠 Define separation of concerns

---

## 🔧 Source Code Fix Registry

### Scripts Creating Output Directories

#### **Script**: `run_experiment.py`
**Current Output Path**: Various (random_3sat_vm_*, etc.)  
**Line Numbers**: [To be found]  
**Fix Required**:
```python
# OLD:
output_dir = f"random_3sat_vm_{problem_size}"

# NEW:
from pathlib import Path
output_dir = Path("results/partition") / f"random_3sat_vm_{problem_size}"
output_dir.mkdir(parents=True, exist_ok=True)
```
**Status**: 🔴 NOT FIXED YET

#### **Script**: `run_partition_experiments.py`
**Current Output Path**: [To be determined]  
**Fix Required**: Use `results/partition/` base directory  
**Status**: 🔴 NOT FIXED YET

#### **Script**: `run_composition_experiments.py`
**Current Output Path**: [To be determined]  
**Fix Required**: Use `results/composition/` base directory  
**Status**: 🔴 NOT FIXED YET

#### **Script**: `stress_test_isomorphism.py`
**Current Output Path**: `stress_test_results/`  
**Fix Required**: Use `results/stress_tests/`  
**Status**: 🔴 NOT FIXED YET

#### **Script**: `verify_rsa_destruction.py` or Shor demos
**Current Output Path**: `shor_demo_*/`  
**Fix Required**: Use `results/shor/N_{modulus}/`  
**Status**: 🔴 NOT FIXED YET

#### **Script**: VM receipt generation
**Current Output Path**: Various, check `thielecpu/vm.py`  
**Fix Required**: Consolidate to `artifacts/receipts/`  
**Status**: 🔴 NOT FIXED YET

---

## 📋 Investigation Checklist

### Phase 1: Map All Output Directories to Sources
- [ ] Run comprehensive grep for directory names
- [ ] Check each Python script for output path definitions
- [ ] Check shell scripts for directory creation
- [ ] Document findings in this file

### Phase 2: Inspect Unknown Directories
- [ ] `catnet/` - List contents, determine purpose
- [ ] `epoch_demo/` - List contents, check git history
- [ ] `forge/` - List contents, search for references
- [ ] `grammar/` - Check if it's parser definitions
- [ ] `liar_test/` - Determine if test or demo
- [ ] `objectives/` - Check dates, determine if outdated
- [ ] `ouroboros/` - Investigate self-referential code
- [ ] `packaging/` - Verify if needed for PyPI
- [ ] `problems/` - Categorize contents
- [ ] `proof-of-thiele/` - Historical significance?
- [ ] `proofpacks/` - Check structure and usage
- [ ] `sandboxes/` - Review experiments
- [ ] `spec/` - Check if important specifications
- [ ] `supplementary_proofs/` - Review proof contents
- [ ] `theory/` - Review mathematical docs
- [ ] `verifier/` - Compare with tools/

### Phase 3: Compare Duplicate Directories
- [ ] `demo/` vs `demos/` - Run diff, merge
- [ ] `hardware/` vs `thielecpu/hardware/` - Run diff, merge
- [ ] `experiments/` vs `benchmarks/` - Define roles
- [ ] `archive/` vs `strategies_backup/` - Consolidate

### Phase 4: Fix Source Code Output Paths
- [ ] Update `run_experiment.py`
- [ ] Update `run_partition_experiments.py`
- [ ] Update `run_composition_experiments.py`
- [ ] Update `stress_test_isomorphism.py`
- [ ] Update Shor demo scripts
- [ ] Update VM receipt paths
- [ ] Update any other scripts found

### Phase 5: Create Standardized Output Structure
- [ ] Create `results/` hierarchy
- [ ] Create `artifacts/` hierarchy
- [ ] Create `.gitignore` rules for output dirs
- [ ] Document output conventions

### Phase 6: Test All Fixed Scripts
- [ ] Run each script with new output paths
- [ ] Verify outputs go to correct locations
- [ ] Verify old paths no longer created

---

## 🎯 Action Items (Prioritized)

### IMMEDIATE (Do First)
1. **Search codebase for all directory creation**
   ```bash
   grep -r "mkdir\|makedirs\|Path.*mkdir" --include="*.py" | tee directory_creation.log
   grep -r "output.*=.*['\"]" --include="*.py" | grep -i "dir\|path" | tee output_paths.log
   ```

2. **Investigate unknown directories**
   - Run `ls -la` and `find` on each unknown directory
   - Check git log for creation date: `git log --diff-filter=A --follow -- dirname/`
   - Search for references: `grep -r "dirname" --include="*.py" --include="*.sh"`

3. **Compare duplicate directories**
   - Run `diff -r` on each pair
   - Document differences
   - Decide which is canonical

### SECONDARY (After Investigation)
4. **Create migration plan** for each directory
5. **Update source code** with new output paths
6. **Test each fix** to ensure no breakage
7. **Archive old data** to `results/archive/`
8. **Update documentation** with new conventions

### FINAL (After All Fixes)
9. **Clean up old directories** (only after sources fixed!)
10. **Update .gitignore** for new output structure
11. **Commit all changes** with detailed message
12. **Verify CI/CD** still works

---

## 📝 Research Log

### Investigation: Random 3SAT Output Directories
**Date**: [Pending]  
**Command**:
```bash
grep -r "random_3sat_vm" --include="*.py" -B 5 -A 5
```
**Findings**: [To be filled in]  
**Source File**: [To be determined]  
**Line Numbers**: [To be determined]  
**Fix Applied**: [Pending]

### Investigation: Shor Demo Output Directories  
**Date**: [Pending]  
**Command**:
```bash
grep -r "shor_demo" --include="*.py" -B 5 -A 5
```
**Findings**: [To be filled in]  
**Source File**: [To be determined]  
**Line Numbers**: [To be determined]  
**Fix Applied**: [Pending]

### Investigation: Unknown Directory - catnet/
**Date**: [Pending]  
**Commands**:
```bash
ls -la catnet/
git log --follow --diff-filter=A -- catnet/
grep -r "catnet" --include="*.py" --include="*.sh" --include="*.md"
```
**Findings**: [To be filled in]  
**Purpose**: [To be determined]  
**Action**: [To be decided]

[... Continue for each directory ...]

---

## ✅ Completion Criteria

This audit is complete when:
1. ✓ Every directory has been mapped to its source
2. ✓ Every source has been updated to use proper output paths
3. ✓ All scripts tested with new paths
4. ✓ Unknown directories investigated and categorized
5. ✓ Duplicate directories merged
6. ✓ Documentation updated
7. ✓ .gitignore updated
8. ✓ CI/CD verified working
9. ✓ Old directories archived/deleted
10. ✓ Future output will stay organized

**Only then can we proceed with cleanup!**

---

## 📊 Progress Tracking

**Phase 1: Source Mapping** - 🔴 Not Started  
**Phase 2: Unknown Dir Investigation** - 🔴 Not Started  
**Phase 3: Duplicate Dir Comparison** - 🔴 Not Started  
**Phase 4: Source Code Fixes** - 🔴 Not Started  
**Phase 5: Output Structure Creation** - 🔴 Not Started  
**Phase 6: Testing** - 🔴 Not Started  

**Overall Progress**: 0% Complete

---

## 🤝 Next Steps

1. **Run Phase 1 investigation commands** (see "IMMEDIATE" section)
2. **Fill in "Research Log"** with findings
3. **Update each directory entry** with source information
4. **Create fix tickets** for each script
5. **Test fixes** one by one
6. **Only after ALL sources fixed** → proceed with cleanup

**Remember**: No directory is touched until its source is fixed! ✋
