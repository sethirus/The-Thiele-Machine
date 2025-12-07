## Source Fixes Completed

### ✅ Fixed Scripts (5 total)

1. **stress_test_isomorphism.py** (line 455)
   - OLD: output_dir = Path('stress_test_results')
   - NEW: output_dir = Path('results/stress_tests')
   - Added: output_dir.mkdir(parents=True, exist_ok=True)

2. **scripts/shor_on_thiele_demo.py** (default arg)
   - OLD: default=Path('shor_demo_output')
   - NEW: default=Path('results/shor')

3. **scripts/graph_coloring_demo.py** (default arg)
   - OLD: default=Path('graph_demo_output')
   - NEW: default=Path('results/graphs')

4. **demos/research-demos/problem-solving/attempt.py** (10 occurrences)
   - OLD: os.makedirs('shape_of_truth_out', ...)
   - NEW: os.makedirs('results/proofs', ...)
   - Fixed all proof file paths and VN subdirectory

5. **scripts/tsp_optimizer.py** (line 505)
   - OLD: work_base = Path('tsp_work') / tsp_file.stem
   - NEW: work_base = Path('results/tsp') / tsp_file.stem
   - Added: work_base.mkdir(parents=True, exist_ok=True)

---

## 📦 Repository Organization Summary

### ✅ CORE PACKAGES (Keep as-is)
- **thielecpu/** - VM implementation (2,200+ lines)
- **coq/** - Formal proofs (115 files, 54,773 lines)
- **demos/** - Demonstration suite (6 demos)
- **tests/** - pytest suite
- **scripts/** - Automation scripts
- **tools/** - Utility scripts
- **forge/** - Grammar-guided equation discovery package
- **verifier/** - Receipt verification utilities (28 files)
- **examples/** - Example code
- **benchmarks/** - Performance benchmarks
- **experiments/** - Experiment configurations
- **archive/** - Historical code (intentional)

### 🔀 DUPLICATE DIRECTORIES (Resolve)
1. **hardware/** (root) vs **thielecpu/hardware/**
   - Root: 5 Verilog files, 4MB
   - thielecpu/: Proper location with README
   - **ACTION**: Merge root hardware/ → thielecpu/hardware/, delete root

2. **demo/** vs **demos/**
   - demo/: 2 files only
   - demos/: Main suite (1,997 lines)
   - **ACTION**: Check demo/ files, merge if needed, delete

### 📊 OUTPUT DIRECTORIES (Archive/Delete)

#### High Priority (Recent/Active - Archive to results/archive/2025-11/)
- stress_test_results/ (17 files, 72K) ✅ Source fixed
- shor_demo_output/ (6 files, 40K) ✅ Source fixed
- graph_demo_output/ (35 files, 312K) ✅ Source fixed
- shape_of_truth_out/ (9 files, 84K) ✅ Source fixed
- tsp_work/ (2 subdirs) ✅ Source fixed
- **thesis_output/** (49 files, **39MB!**) - LaTeX + experiments
- full_output/ (188 files, 1.4M)
- test_output/ (15 files, 72K)

#### Medium Priority (Old experiments - Archive to results/archive/2025-11/)
- random_3sat_vm_50/ (1 file, 2.6K)
- random_3sat_vm_100/ (1 file, 7.3K)
- random_3sat_vm_150/ (1 file, 7.3K)
- structured_tseitin_20/ (1 file, 1.5K)
- structured_tseitin_50/ (1 file, 4.8K)
- shor_demo_2047/ (empty)
- shor_demo_10007/ (empty)
- outputs/ (2 files, Oct 2025)
- epoch_demo/ (2 files: png, csv)

#### Low Priority (Empty/Small - Safe to delete)
- tmp_vm_test/ (temp data)
- temp_receipts/ (0 files)
- liar_test/ (0 files)
- catnet/ (only __pycache__)

### 📁 DATA/CONFIG DIRECTORIES (Keep organized)
- **artifacts/** (1,028 files, 13M) - Experiment artifacts (KEEP)
- **audit_logs/** (43 files, 868K) - Audit history (KEEP)
- **bootstrap_receipts/** (1 file) - Bootstrap data
- **checksums/** (1 file) - Verification data
- **configs/** (3 files) - Configuration files
- **data/** (9 files, 44K) - Input data
- **sight_logs/** (5 files, 32K) - Sight logging output
- **logs/** (2 files) - General logs
- **build/** (2 files) - Build artifacts (regenerable)

### 📚 DOCUMENTATION/SPEC DIRECTORIES (Keep)
- **docs/** - Documentation
- **documents/** (9 files, 168K) - Additional docs
- **spec/** (27 files, 124K) - Specifications
- **theory/** (51 files, 320K) - Theoretical work
- **supplementary_proofs/** (5 files)
- **web/** (20 files, 248K) - Web assets

### 🎯 ALGORITHM DIRECTORIES (Keep)
- **strategies/** (7 files)
- **strategies_backup/** (7 files) - Backup copy
- **evolved_strategies/** (1 file)
- **objectives/** (3 files)
- **grammar/** (1 file)

### 📁 NEW Results Structure Created
```
results/
├── stress_tests/    ✅ Created
├── shor/            ✅ Created
├── graphs/          ✅ Created
├── partition/       ✅ Created
├── tsp/             ✅ Created
├── proofs/          ✅ Created
│   └── vn_proofs/   ✅ Created
└── archive/         ✅ Created
    ├── 2025-10/     ✅ Created
    └── 2025-11/     ✅ Created
```

---

## 🎯 Next Actions

### Phase 1: Test Fixed Scripts ⏭️ CURRENT
```bash
# Test each fixed script to verify new paths work
python stress_test_isomorphism.py --quick
python scripts/shor_on_thiele_demo.py --help
python scripts/graph_coloring_demo.py --help
python scripts/tsp_optimizer.py --help
```

### Phase 2: Resolve Duplicates
1. Compare hardware/ with thielecpu/hardware/
2. Merge unique files → thielecpu/hardware/
3. Delete root hardware/
4. Check demo/ contents, merge → demos/ if needed

### Phase 3: Archive Old Outputs
```bash
# Move to results/archive/2025-11/
mv stress_test_results results/archive/2025-11/
mv shor_demo_output results/archive/2025-11/
mv graph_demo_output results/archive/2025-11/
mv shape_of_truth_out results/archive/2025-11/
mv tsp_work results/archive/2025-11/
mv thesis_output results/archive/2025-11/
mv full_output results/archive/2025-11/
mv test_output results/archive/2025-11/
mv random_3sat_vm_* results/archive/2025-11/
mv structured_tseitin_* results/archive/2025-11/
mv epoch_demo results/archive/2025-11/

# Move to results/archive/2025-10/
mv outputs results/archive/2025-10/
mv shor_demo_2047 results/archive/2025-10/
mv shor_demo_10007 results/archive/2025-10/
```

### Phase 4: Delete Empty/Temp Directories
```bash
rm -rf tmp_vm_test temp_receipts liar_test catnet
```

### Phase 5: Update .gitignore
Add proper ignores for results/ outputs:
```
results/stress_tests/
results/shor/
results/graphs/
results/partition/
results/tsp/
results/proofs/
!results/archive/
```

