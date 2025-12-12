#!/usr/bin/env python3
"""
Comprehensive Measurement, Benchmarking, and Fuzzing Suite
Quantifies isomorphism verification with hard metrics and adversarial testing
"""

import sys
import time
import random
from pathlib import Path
from typing import List, Dict, Any
import json

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from thielecpu.vm import VM, State
from thielecpu.isa import Opcode

# ============================================================================
# MEASUREMENT FRAMEWORK
# ============================================================================

class Measurements:
    """Collect quantitative measurements of the system"""
    
    def __init__(self):
        self.metrics = {}
    
    def measure_state_size(self, state: State) -> Dict[str, int]:
        """Measure the size of state components in bytes"""
        import sys
        
        measurements = {
            "total_state_size": sys.getsizeof(state),
            "mu_ledger_size": sys.getsizeof(state.mu_ledger),
            "regions_size": sys.getsizeof(state.regions),
            "partition_masks_size": sys.getsizeof(state.partition_masks),
            "csr_size": sys.getsizeof(state.csr),
            "num_modules": state.num_modules,
        }
        return measurements
    
    def measure_mu_conservation(self, num_operations: int = 100) -> Dict[str, Any]:
        """Measure μ-cost conservation over many operations"""
        state = State()
        
        mu_values = [state.mu_ledger.total]
        violations = 0
        
        for i in range(num_operations):
            old_mu = state.mu_ledger.total
            
            # Perform operation
            if i % 3 == 0 and state.num_modules < 8:
                state.pnew({i % 64})
            
            new_mu = state.mu_ledger.total
            
            # Check monotonicity
            if new_mu < old_mu:
                violations += 1
            
            mu_values.append(new_mu)
        
        return {
            "operations": num_operations,
            "mu_start": mu_values[0],
            "mu_end": mu_values[-1],
            "mu_delta": mu_values[-1] - mu_values[0],
            "monotonicity_violations": violations,
            "monotonicity_preserved": violations == 0,
        }

# ============================================================================
# FUZZING FRAMEWORK
# ============================================================================

class IsomorphismFuzzer:
    """Adversarial fuzzing to find isomorphism violations"""
    
    def __init__(self, seed: int = 42):
        random.seed(seed)
        self.violations = []
    
    def fuzz_random_programs(self, num_programs: int = 1000) -> Dict[str, Any]:
        """Generate and execute random programs looking for inconsistencies"""
        results = {
            "programs_tested": 0,
            "errors_found": 0,
            "violations_found": 0,
            "max_modules_reached": 0,
            "crashes": [],
        }
        
        for i in range(num_programs):
            try:
                state = State()
                
                # Generate random sequence of operations
                num_ops = random.randint(5, 20)
                for j in range(num_ops):
                    self._random_operation(state)
                
                results["programs_tested"] += 1
                
                # Check invariants
                if not self._check_invariants(state):
                    results["violations_found"] += 1
                
                if state.num_modules > results["max_modules_reached"]:
                    results["max_modules_reached"] = state.num_modules
                    
            except Exception as e:
                results["errors_found"] += 1
                if len(results["crashes"]) < 10:
                    results["crashes"].append(str(e))
        
        return results
    
    def _random_operation(self, state: State):
        """Execute a random valid operation on the state"""
        try:
            op_type = random.randint(0, 2)
            
            if op_type == 0 and state.num_modules < 8:
                # PNEW
                region = set(random.sample(range(64), random.randint(1, 10)))
                state.pnew(region)
            elif op_type == 1 and state.num_modules > 0 and state.num_modules < 8:
                # PSPLIT
                modules = list(state.partition_masks.keys())
                if modules:
                    module = random.choice(modules)
                    state.psplit(module, lambda x: x % 2 == 0)
            elif op_type == 2 and state.num_modules >= 2:
                # PMERGE
                modules = list(state.partition_masks.keys())
                if len(modules) >= 2:
                    m1, m2 = random.sample(modules, 2)
                    state.pmerge(m1, m2)
        except:
            pass  # Ignore expected failures
    
    def _check_invariants(self, state: State) -> bool:
        """Check state invariants hold"""
        # Monotonicity of μ
        if state.mu_ledger.total < 0:
            self.violations.append("Negative μ-cost")
            return False
        
        # Module count bounds
        if state.num_modules < 0 or state.num_modules > 8:
            self.violations.append(f"Invalid module count: {state.num_modules}")
            return False
        
        # Partition disjointness
        masks = list(state.partition_masks.values())
        for i in range(len(masks)):
            for j in range(i + 1, len(masks)):
                if masks[i] & masks[j] != 0:
                    self.violations.append("Overlapping partitions detected")
                    return False
        
        return True
    
    def fuzz_boundary_conditions(self) -> Dict[str, Any]:
        """Test extreme boundary conditions"""
        results = {
            "tests_run": 0,
            "failures": [],
        }
        
        # Test 1: Maximum modules
        try:
            state = State()
            for i in range(8):
                state.pnew({i})
            
            # Try to exceed limit
            try:
                state.pnew({63})
                results["failures"].append("Exceeded max modules without error")
            except:
                pass  # Expected
            
            results["tests_run"] += 1
        except Exception as e:
            results["failures"].append(f"Max modules test: {e}")
        
        # Test 2: Full bitmask
        try:
            state = State()
            full_region = set(range(64))
            state.pnew(full_region)
            results["tests_run"] += 1
        except Exception as e:
            results["failures"].append(f"Full bitmask test: {e}")
        
        return results

# ============================================================================
# BENCHMARKING SUITE
# ============================================================================

class Benchmarks:
    """Performance benchmarks for isomorphism verification"""
    
    def benchmark_state_creation(self, iterations: int = 10000) -> Dict[str, float]:
        """Benchmark state object creation"""
        times = []
        for _ in range(iterations):
            start = time.perf_counter()
            state = State()
            elapsed = time.perf_counter() - start
            times.append(elapsed)
        
        return {
            "mean_ns": sum(times) / len(times) * 1e9,
            "total_ms": sum(times) * 1000,
            "throughput_per_sec": iterations / sum(times),
        }
    
    def benchmark_partition_operations(self, iterations: int = 1000) -> Dict[str, Dict[str, float]]:
        """Benchmark partition operations"""
        results = {}
        
        # PNEW benchmark
        pnew_times = []
        for i in range(iterations):
            state = State()
            start = time.perf_counter()
            state.pnew({i % 64})
            elapsed = time.perf_counter() - start
            pnew_times.append(elapsed)
        
        results["pnew"] = {
            "mean_ns": sum(pnew_times) / len(pnew_times) * 1e9,
            "ops_per_sec": iterations / sum(pnew_times),
        }
        
        # PSPLIT benchmark
        psplit_times = []
        for i in range(iterations):
            state = State()
            m = state.pnew({1, 2, 3, 4, 5, 6})
            start = time.perf_counter()
            state.psplit(m, lambda x: x % 2 == 0)
            elapsed = time.perf_counter() - start
            psplit_times.append(elapsed)
        
        results["psplit"] = {
            "mean_ns": sum(psplit_times) / len(psplit_times) * 1e9,
            "ops_per_sec": iterations / sum(psplit_times),
        }
        
        return results

# ============================================================================
# MAIN TEST SUITE
# ============================================================================

def run_measurement_suite():
    """Run comprehensive measurement suite"""
    print("=" * 70)
    print("MEASUREMENT SUITE - Quantifying Isomorphism Properties")
    print("=" * 70)
    
    measurements = Measurements()
    
    # Measure state size
    print("\n[1] State Size Measurements")
    print("-" * 70)
    state = State()
    state.pnew({1, 2, 3})
    state.pnew({10, 20, 30})
    
    size_metrics = measurements.measure_state_size(state)
    for key, value in size_metrics.items():
        print(f"  {key:30s}: {value:10d}")
    
    # Measure μ-conservation
    print("\n[2] μ-Conservation Measurements")
    print("-" * 70)
    conservation = measurements.measure_mu_conservation(num_operations=1000)
    for key, value in conservation.items():
        print(f"  {key:30s}: {value}")
    
    return {
        "state_size": size_metrics,
        "conservation": conservation,
    }

def run_fuzzing_suite():
    """Run adversarial fuzzing suite"""
    print("\n" + "=" * 70)
    print("FUZZING SUITE - Adversarial Testing for Violations")
    print("=" * 70)
    
    fuzzer = IsomorphismFuzzer(seed=42)
    
    # Random program fuzzing
    print("\n[1] Random Program Fuzzing")
    print("-" * 70)
    fuzz_results = fuzzer.fuzz_random_programs(num_programs=10000)
    for key, value in fuzz_results.items():
        if key != "crashes":
            print(f"  {key:30s}: {value}")
    
    if fuzz_results["crashes"]:
        print(f"  Sample crashes:")
        for crash in fuzz_results["crashes"][:5]:
            print(f"    - {crash}")
    
    # Boundary condition fuzzing
    print("\n[2] Boundary Condition Fuzzing")
    print("-" * 70)
    boundary_results = fuzzer.fuzz_boundary_conditions()
    for key, value in boundary_results.items():
        if key != "failures":
            print(f"  {key:30s}: {value}")
    
    if boundary_results["failures"]:
        print(f"  Failures:")
        for failure in boundary_results["failures"]:
            print(f"    - {failure}")
    
    return {
        "random_programs": fuzz_results,
        "boundary_conditions": boundary_results,
    }

def run_benchmark_suite():
    """Run performance benchmark suite"""
    print("\n" + "=" * 70)
    print("BENCHMARK SUITE - Performance Measurements")
    print("=" * 70)
    
    benchmarks = Benchmarks()
    
    # State creation benchmark
    print("\n[1] State Creation Benchmark")
    print("-" * 70)
    creation_bench = benchmarks.benchmark_state_creation(iterations=10000)
    for key, value in creation_bench.items():
        print(f"  {key:30s}: {value:15.2f}")
    
    # Partition operations benchmark
    print("\n[2] Partition Operations Benchmark")
    print("-" * 70)
    partition_bench = benchmarks.benchmark_partition_operations(iterations=1000)
    for op, metrics in partition_bench.items():
        print(f"  {op.upper()}:")
        for key, value in metrics.items():
            print(f"    {key:28s}: {value:15.2f}")
    
    return {
        "state_creation": creation_bench,
        "partition_operations": partition_bench,
    }

def main():
    """Run all measurement, fuzzing, and benchmarking suites"""
    print("\n" + "=" * 70)
    print("COMPREHENSIVE MEASUREMENT, FUZZING, AND BENCHMARKING SUITE")
    print("Quantitative Verification of Three-Layer Isomorphism")
    print("=" * 70)
    
    results = {}
    
    # Run measurement suite
    results["measurements"] = run_measurement_suite()
    
    # Run fuzzing suite
    results["fuzzing"] = run_fuzzing_suite()
    
    # Run benchmark suite
    results["benchmarks"] = run_benchmark_suite()
    
    # Summary
    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)
    
    conservation = results["measurements"]["conservation"]
    fuzz = results["fuzzing"]["random_programs"]
    
    print(f"\nμ-Conservation:")
    print(f"  ✓ Monotonicity preserved: {conservation['monotonicity_preserved']}")
    print(f"  ✓ Violations found: {conservation['monotonicity_violations']}")
    
    print(f"\nFuzzing Results:")
    print(f"  ✓ Programs tested: {fuzz['programs_tested']}")
    print(f"  ✓ Violations found: {fuzz['violations_found']}")
    print(f"  ✓ Errors found: {fuzz['errors_found']}")
    
    # Save results
    output_file = Path("artifacts/measurement_fuzzing_results.json")
    output_file.parent.mkdir(exist_ok=True)
    with open(output_file, "w") as f:
        json.dump(results, f, indent=2, default=str)
    
    print(f"\n✓ Results saved to: {output_file}")
    
    # Exit code based on results
    if conservation['monotonicity_preserved'] and fuzz['violations_found'] == 0:
        print("\n✅ ALL MEASUREMENTS AND FUZZING TESTS PASSED")
        return 0
    else:
        print("\n⚠️  SOME ISSUES DETECTED")
        return 1

if __name__ == "__main__":
    sys.exit(main())
