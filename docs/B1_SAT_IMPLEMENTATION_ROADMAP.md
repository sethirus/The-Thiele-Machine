# B1: SAT Killer App - Implementation Roadmap

**Status**: IN PROGRESS  
**Priority**: ⚡ PRIORITY 2  
**Goal**: Demonstrate μ+partitions gives SAT solver speedups  
**Evidence for**: H2 (structural advantage on CNF/SAT)

---

## Overview

This document provides the detailed implementation roadmap for Track B1 from the Research Program Master Plan. The goal is to create the "first killer app" that demonstrates the Thiele Machine's structural advantage on SAT solving through partition-based preprocessing.

**Key Hypothesis (H2)**: μ + partitions yields lower work than blind baselines, scaling with information discovered.

**Falsification Criterion**: If no consistent speedup is observed on structured SAT instances, H2 is falsified.

---

## Task Breakdown

### B1.1: Build CNF Analyzer ✅ **COMPLETE**

**Status**: SKELETON COMPLETE (2025-12-05)

**Deliverable**: `tools/cnf_analyzer.py` (300-400 lines)

**What's Implemented**:
- ✅ DIMACS parser for CNF files
- ✅ Variable interaction graph builder
- ✅ Graph density computation
- ✅ Partition metrics data structure
- ✅ CLI interface with JSON output
- ✅ Basic testing on example CNF files

**What's TODO**:
- [ ] **Integration with thielecpu.discovery module**
  - Current: Placeholder trivial partition
  - Target: Use `EfficientPartitionDiscovery` class from `thielecpu/discovery.py`
  - Algorithm: Spectral clustering on interaction graph
  
- [ ] **Real partition discovery implementation**
  ```python
  from thielecpu.discovery import EfficientPartitionDiscovery, Problem
  
  # Convert interaction graph to Problem format
  problem = Problem(
      num_variables=num_vars,
      interactions=edges
  )
  
  # Discover partitions
  discovery = EfficientPartitionDiscovery()
  candidate = discovery.discover_partition(problem, max_mu_budget=1000.0)
  
  # Extract metrics
  modules = candidate.modules
  mu_discovery = candidate.discovery_cost_mu
  ```

- [ ] **μ-cost calculation according to μ-spec v2.0**
  - Current: Placeholder values (mu_discovery=100, mu_operational=10)
  - Target: Actual computation using `thielecpu/mu.py`
  - Formula: μ_total = 8|canon(q)| + log₂(N/M)
  
- [ ] **Visualization support**
  - Graph rendering using networkx + matplotlib
  - Color-code modules
  - Display μ-costs and structural metrics
  
- [ ] **Comprehensive testing**
  - Unit tests for each component
  - Integration tests with various CNF types
  - Regression tests for μ-cost calculations

**Estimated Effort**: 4-6 hours to complete TODO items

**Success Criteria**:
- ✅ Parses DIMACS CNF files correctly
- ✅ Builds interaction graph
- ⚠️ Discovers meaningful partitions (not just trivial)
- ⚠️ Computes accurate μ-costs
- ⚠️ Outputs structured metrics

---

### B1.2: Integrate with SAT Solver ⏳ **NOT STARTED**

**Status**: NOT STARTED

**Deliverable**: `tools/sat_benchmark.py` (400-500 lines)

**Requirements**:

1. **SAT Solver Integration**
   - Choose solver: MiniSat (via pycosat) or Z3 (via z3-solver)
   - Recommendation: Z3 for better Python integration
   - Install: `pip install z3-solver`

2. **Two Execution Modes**
   
   a) **Baseline (Blind)**:
      - Run SAT solver directly on CNF
      - No preprocessing
      - Collect metrics: runtime, conflicts, decisions
      - Track μ_blind (cost of blind search)
   
   b) **Preprocessed (Sighted)**:
      - Run CNF analyzer to discover partitions
      - Split CNF into sub-problems per module
      - Solve each module independently
      - Compose results
      - Collect metrics: runtime, conflicts, decisions, μ-costs
      - Track μ_sighted (cost of discovery + sighted solving)

3. **Metrics Collection**
   ```python
   class SATMetrics:
       runtime: float          # Wall-clock time (seconds)
       conflicts: int          # Number of conflicts
       decisions: int          # Number of decisions
       restarts: int           # Number of restarts
       mu_operational: float   # Operational μ-cost
       mu_information: float   # Information revelation cost
       mu_total: float         # Total μ-cost
       solved: bool            # Whether SAT/UNSAT determined
       result: Optional[str]   # "SAT" or "UNSAT"
   ```

4. **Comparison Framework**
   ```python
   class BenchmarkResult:
       instance_name: str
       baseline_metrics: SATMetrics
       sighted_metrics: SATMetrics
       speedup: float          # baseline_runtime / sighted_runtime
       mu_ratio: float         # mu_baseline / mu_sighted
       advantage: bool         # True if sighted < baseline
   ```

**Implementation Steps**:

1. **Setup** (1 hour)
   - Install Z3: `pip install z3-solver`
   - Create `tools/sat_benchmark.py` skeleton
   - Define data structures (SATMetrics, BenchmarkResult)

2. **Baseline Mode** (2 hours)
   - Parse CNF with Z3
   - Run solver, collect metrics
   - Compute μ_blind = blind_solve_cost(num_vars)
   - Output results

3. **Sighted Mode** (4 hours)
   - Call `cnf_analyzer.py` to get partitions
   - Split CNF by modules
   - Solve each module with Z3
   - Compose solutions (check consistency)
   - Compute μ_sighted = μ_discovery + Σ μ_module_solve
   - Output results

4. **Comparison** (2 hours)
   - Run both modes on same instance
   - Compute speedup and μ-ratio
   - Generate comparison report
   - Visualize results

**Estimated Effort**: 8-10 hours

**Success Criteria**:
- Runs both baseline and sighted modes
- Collects complete metrics
- Produces comparison reports
- Handles edge cases (UNSAT, timeout)

---

### B1.3: Benchmark on SATLIB ⏳ **NOT STARTED**

**Status**: NOT STARTED

**Deliverable**: `benchmarks/sat_results.csv` (100+ instances)

**Test Sets**:

1. **Synthetic Structured** (30 instances)
   - Multiplier circuits (size 4, 8, 16, 32)
   - Pigeonhole (php-5, php-6, php-7, ...)
   - Parity learning (par8, par16, par32)
   - Expected: High speedup (structured problems)

2. **SATLIB Benchmarks** (50 instances)
   - Hardware verification (barrel, longmult)
   - Planning problems (logistics, blocks)
   - Graph coloring (flat, SW100)
   - Expected: Moderate speedup (semi-structured)

3. **Random 3-SAT** (20 instances)
   - Uniform random (uf50, uf100, uf200)
   - Phase transition region (ratio 4.2)
   - Expected: No speedup (no structure)

**Data Collection**:

```csv
instance,type,vars,clauses,density,baseline_time,sighted_time,speedup,mu_baseline,mu_sighted,mu_ratio,advantage
php-5.cnf,structured,25,160,0.85,2.31,0.47,4.91,350.2,89.4,3.92,TRUE
uf50-01.cnf,random,50,218,0.31,0.15,0.18,0.83,125.6,140.2,0.90,FALSE
...
```

**Automation**:

1. **Download SATLIB** (1 hour)
   ```bash
   wget http://www.cs.ubc.ca/~hoos/SATLIB/benchm.html
   # Or use curated collection from SAT Competition
   ```

2. **Run Batch Benchmark** (script) (2 hours)
   ```python
   # tools/run_sat_benchmarks.py
   for instance in instances:
       baseline = run_baseline(instance)
       sighted = run_sighted(instance)
       result = compare(baseline, sighted)
       results.append(result)
   
   save_csv(results, "benchmarks/sat_results.csv")
   ```

3. **Parallel Execution** (optional, 1 hour)
   - Use multiprocessing to run 4-8 instances in parallel
   - Respect timeout (e.g., 300 seconds per instance)

**Estimated Effort**: 4-6 hours + compute time

**Success Criteria**:
- 100+ instances benchmarked
- Structured instances show speedup
- Random instances show no advantage
- Results saved to CSV

---

### B1.4: Analyze Results ⏳ **NOT STARTED**

**Status**: NOT STARTED

**Deliverable**: `docs/SAT_BENCHMARK_ANALYSIS.md` + figures

**Analysis Tasks**:

1. **Statistical Analysis** (3 hours)
   - Compute mean/median speedup by category
   - T-test: structured vs random
   - Effect size (Cohen's d)
   - Correlation: structure_score vs speedup

2. **Visualization** (2 hours)
   - Scatter plot: density vs speedup
   - Box plot: speedup by category
   - Histogram: μ-cost distribution
   - Line plot: scaling with problem size

3. **Report Writing** (3 hours)
   - Introduction: Problem and hypothesis
   - Methods: Tools, datasets, metrics
   - Results: Tables and figures
   - Discussion: When/why partitions help
   - Conclusion: Evidence for/against H2

**Python Analysis Script**:

```python
import pandas as pd
import matplotlib.pyplot as plt
from scipy import stats

# Load results
df = pd.read_csv("benchmarks/sat_results.csv")

# Filter by type
structured = df[df['type'] == 'structured']
random = df[df['type'] == 'random']

# Compute statistics
print(f"Structured mean speedup: {structured['speedup'].mean():.2f}x")
print(f"Random mean speedup: {random['speedup'].mean():.2f}x")

# T-test
t_stat, p_value = stats.ttest_ind(structured['speedup'], random['speedup'])
print(f"T-test: t={t_stat:.3f}, p={p_value:.4f}")

# Plot
plt.figure(figsize=(10, 6))
plt.scatter(df['density'], df['speedup'], c=df['type'].map({'structured': 'blue', 'random': 'red'}))
plt.xlabel('Interaction Density')
plt.ylabel('Speedup (Sighted / Baseline)')
plt.title('Structure vs Speedup')
plt.savefig('docs/figures/sat_speedup_vs_density.png')
```

**Estimated Effort**: 8-10 hours

**Success Criteria**:
- Clear statistical evidence for/against H2
- Publication-quality figures
- Comprehensive analysis document
- Specific conclusions about when partitions help

---

## Summary Timeline

| Task | Status | Effort | Dependencies |
|------|--------|--------|--------------|
| B1.1 | ✅ Skeleton | 4-6h | None |
| B1.2 | ⏳ Not Started | 8-10h | B1.1 complete |
| B1.3 | ⏳ Not Started | 4-6h + compute | B1.2 complete |
| B1.4 | ⏳ Not Started | 8-10h | B1.3 complete |
| **Total** | **14% Complete** | **24-32h** | |

**Critical Path**: B1.1 → B1.2 → B1.3 → B1.4 (must be sequential)

**Estimated Calendar Time**: 2-3 weeks (with parallel compute for B1.3)

---

## Next Actions

**Immediate (Week 1)**:
1. ✅ Complete B1.1 TODOs (integrate discovery, implement μ-costs)
2. ⏳ Start B1.2 skeleton (setup Z3, define data structures)
3. ⏳ Download SATLIB benchmarks

**Week 2**:
1. Complete B1.2 implementation
2. Test on 10-20 instances manually
3. Start B1.3 automation script

**Week 3**:
1. Run full B1.3 benchmark suite
2. Analyze results (B1.4)
3. Write report and generate figures

---

## Falsification Strategy

**H2 is falsified if**:
- No statistically significant speedup on structured instances (p > 0.05)
- Speedup on structured instances < 1.5× (insufficient advantage)
- Blind solver consistently beats sighted solver
- μ-cost accounting shows negative return on discovery investment

**Evidence for H2**:
- Speedup on structured instances ≥ 2× (p < 0.01)
- Strong correlation between structure score and speedup (r > 0.7)
- μ-ratio shows discovery pays off (μ_sighted < μ_blind)

---

## References

- [RESEARCH_PLAN] RESEARCH_PROGRAM_MASTER_PLAN.md - Overall plan
- [MODEL_SPEC] docs/MODEL_SPEC.md - μ-cost formulas
- [DISCOVERY] thielecpu/discovery.py - Partition discovery
- [CNF] thielecpu/cnf.py - CNF utilities
- [SATLIB] http://www.cs.ubc.ca/~hoos/SATLIB/ - Benchmark library

---

## Contact

For questions or contributions:
- See CONTRIBUTING.md
- Open issue with tag `track-b1`
- Reference this roadmap in PRs

---

**Last Updated**: 2025-12-05  
**Author**: Thiele Machine Development Team  
**Status**: B1.1 Complete (Skeleton), B1.2-B1.4 Pending
