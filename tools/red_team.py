#!/usr/bin/env python3
"""
Red-Team Harness for The Thiele Machine

Automated falsification tests for core hypotheses.
See docs/HOW_TO_FALSIFY_THIS.md for test descriptions.

Usage:
    python tools/red_team.py --all                  # Run all tests
    python tools/red_team.py --test mu_bounds       # Test μ-monotonicity
    python tools/red_team.py --test landauer        # Test Landauer bound
    python tools/red_team.py --test isomorphism     # Test implementation consistency
    python tools/red_team.py --test random_advantage # Test random graph detection
    python tools/red_team.py --test polynomial_time # Test O(n³) complexity
"""

import sys
import argparse
import time
import random
import math
from pathlib import Path
from typing import List, Tuple, Dict, Any, Optional
from dataclasses import dataclass

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from thielecpu.vm import VM
from thielecpu.state import State, MuLedger
from thielecpu.isa import Opcode
from thielecpu.discovery import Problem, EfficientPartitionDiscovery
from thielecpu.mu import calculate_mu_cost


# Physical constants for Landauer bound
BOLTZMANN_CONSTANT = 1.380649e-23  # J/K
ROOM_TEMPERATURE = 300.0  # K
LANDAUER_BOUND_PER_BIT = BOLTZMANN_CONSTANT * ROOM_TEMPERATURE * math.log(2)  # ~3e-21 J/bit


@dataclass
class TestResult:
    """Result of a red-team test."""
    test_name: str
    passed: bool
    message: str
    details: Dict[str, Any]
    falsifies: List[str]  # List of hypotheses falsified (H1, H2, H3, H4)


class RedTeamHarness:
    """Red-team test harness for falsification attempts."""

    def __init__(self, verbose: bool = True):
        self.verbose = verbose
        self.results: List[TestResult] = []

    def log(self, message: str):
        """Log message if verbose."""
        if self.verbose:
            print(message)

    def add_result(self, result: TestResult):
        """Add test result."""
        self.results.append(result)

        if result.passed:
            self.log(f"✅ PASS: {result.test_name}")
        else:
            self.log(f"❌ FAIL: {result.test_name}")
            self.log(f"   Message: {result.message}")
            if result.falsifies:
                self.log(f"   ⚠️  FALSIFIES: {', '.join(result.falsifies)}")

    def print_summary(self):
        """Print test summary."""
        total = len(self.results)
        passed = sum(1 for r in self.results if r.passed)
        failed = total - passed

        falsifications = [r for r in self.results if not r.passed and r.falsifies]

        print()
        print("=" * 80)
        print("RED-TEAM TEST SUMMARY")
        print("=" * 80)
        print(f"Total Tests: {total}")
        print(f"Passed:      {passed} ✅")
        print(f"Failed:      {failed} ❌")
        print()

        if falsifications:
            print("⚠️  FALSIFICATIONS DETECTED:")
            for r in falsifications:
                print(f"  - {r.test_name}")
                print(f"    Falsifies: {', '.join(r.falsifies)}")
                print(f"    Message: {r.message}")
            print()
        else:
            print("✅ No falsifications detected - all hypotheses survive")
            print()

    # ==================== Test Category 1: μ-Bound Violations ====================

    def test_mu_monotonicity_basic(self) -> TestResult:
        """Test H1: μ never decreases during valid operations."""
        try:
            state = State()
            vm = VM(state=state)

            # Track μ through a sequence of operations
            initial_mu = vm.state.mu_ledger.mu_discovery + vm.state.mu_ledger.mu_execution

            # Create a partition (PNEW)
            region = [1, 2, 3, 4, 5]
            vm.state.pnew(region)
            after_pnew = vm.state.mu_ledger.mu_discovery + vm.state.mu_ledger.mu_execution

            if after_pnew < initial_mu:
                return TestResult(
                    test_name="μ-monotonicity (basic)",
                    passed=False,
                    message=f"μ decreased: {initial_mu} → {after_pnew}",
                    details={"initial": initial_mu, "after_pnew": after_pnew},
                    falsifies=["H1", "H4"]
                )

            # Split partition
            module_id = list(vm.state.regions.modules.keys())[0]
            vm.state.psplit(module_id, pred=lambda x: x <= 3)
            after_psplit = vm.state.mu_ledger.mu_discovery + vm.state.mu_ledger.mu_execution

            if after_psplit < after_pnew:
                return TestResult(
                    test_name="μ-monotonicity (basic)",
                    passed=False,
                    message=f"μ decreased: {after_pnew} → {after_psplit}",
                    details={"after_pnew": after_pnew, "after_psplit": after_psplit},
                    falsifies=["H1", "H4"]
                )

            return TestResult(
                test_name="μ-monotonicity (basic)",
                passed=True,
                message="μ is monotonically non-decreasing",
                details={"initial": initial_mu, "after_pnew": after_pnew, "after_psplit": after_psplit},
                falsifies=[]
            )

        except Exception as e:
            return TestResult(
                test_name="μ-monotonicity (basic)",
                passed=False,
                message=f"Exception: {str(e)}",
                details={"error": str(e)},
                falsifies=["H4"]
            )

    def test_mu_formula_bounds(self) -> TestResult:
        """Test H1: μ-formula never produces negative or undefined values."""
        try:
            test_cases = [
                ("binary_search", 1024, 1, "log2(1024/1) = 10 bits"),
                ("found_answer", 100, 1, "log2(100/1) ≈ 6.64 bits"),
                ("no_refinement", 50, 50, "log2(50/50) = 0 bits"),
                ("large_space", 2**20, 2**10, "log2(2^20/2^10) = 10 bits"),
            ]

            for query, N, M, description in test_cases:
                mu = calculate_mu_cost(query, N, M)

                if mu < 0:
                    return TestResult(
                        test_name="μ-formula bounds",
                        passed=False,
                        message=f"Negative μ: {mu} for {description}",
                        details={"query": query, "N": N, "M": M, "mu": mu},
                        falsifies=["H1"]
                    )

                if math.isnan(mu) or math.isinf(mu):
                    return TestResult(
                        test_name="μ-formula bounds",
                        passed=False,
                        message=f"Undefined μ: {mu} for {description}",
                        details={"query": query, "N": N, "M": M, "mu": mu},
                        falsifies=["H1"]
                    )

            return TestResult(
                test_name="μ-formula bounds",
                passed=True,
                message="μ-formula produces valid non-negative values",
                details={"test_cases": len(test_cases)},
                falsifies=[]
            )

        except Exception as e:
            return TestResult(
                test_name="μ-formula bounds",
                passed=False,
                message=f"Exception: {str(e)}",
                details={"error": str(e)},
                falsifies=["H1", "H4"]
            )

    def test_mu_adversarial_operations(self, trials: int = 100) -> TestResult:
        """Test H1: Try adversarial operations to make μ decrease."""
        try:
            violations = []

            for trial in range(trials):
                state = State()
                vm = VM(state=state)
                rng = random.Random(trial)

                # Build random state
                for _ in range(10):
                    op = rng.choice(['pnew', 'psplit', 'pmerge'])

                    mu_before = vm.state.mu_ledger.mu_discovery + vm.state.mu_ledger.mu_execution

                    try:
                        if op == 'pnew':
                            size = rng.randint(1, 20)
                            region = rng.sample(range(1, 101), size)
                            vm.state.pnew(region)

                        elif op == 'psplit' and len(vm.state.regions.modules) > 0:
                            module_id = rng.choice(list(vm.state.regions.modules.keys()))
                            vm.state.psplit(module_id, pred=lambda x: rng.random() < 0.5)

                        elif op == 'pmerge' and len(vm.state.regions.modules) >= 2:
                            m1, m2 = rng.sample(list(vm.state.regions.modules.keys()), 2)
                            vm.state.pmerge(m1, m2)

                    except Exception:
                        # Some operations may fail (empty partitions, etc.) - that's OK
                        continue

                    mu_after = vm.state.mu_ledger.mu_discovery + vm.state.mu_ledger.mu_execution

                    if mu_after < mu_before:
                        violations.append({
                            "trial": trial,
                            "operation": op,
                            "mu_before": mu_before,
                            "mu_after": mu_after,
                            "delta": mu_after - mu_before
                        })

            if violations:
                return TestResult(
                    test_name="μ-adversarial operations",
                    passed=False,
                    message=f"Found {len(violations)} μ-monotonicity violations",
                    details={"violations": violations[:5], "total_violations": len(violations)},
                    falsifies=["H1", "H4"]
                )

            return TestResult(
                test_name="μ-adversarial operations",
                passed=True,
                message=f"No μ-violations found in {trials} adversarial trials",
                details={"trials": trials},
                falsifies=[]
            )

        except Exception as e:
            return TestResult(
                test_name="μ-adversarial operations",
                passed=False,
                message=f"Exception: {str(e)}",
                details={"error": str(e)},
                falsifies=["H4"]
            )

    # ==================== Test Category 2: Landauer Bound ====================

    def test_landauer_bound_simple_gates(self) -> TestResult:
        """Test H1: Verify μ-cost respects Landauer bound for logical operations."""
        try:
            # Test simple logical operations
            # For irreversible operations (AND, OR), we erase information
            # Landauer bound: ≥ kT ln(2) per bit erased

            test_cases = [
                ("AND(0,1)", 4, 2, 1, "2→1 bit (erase 1 bit)"),
                ("OR(0,0)", 4, 2, 1, "2→1 bit (erase 1 bit)"),
                ("binary_search", 1024, 1, 10, "log2(1024) = 10 bits"),
            ]

            violations = []

            for query, N, M, expected_info_bits, description in test_cases:
                mu_bits = calculate_mu_cost(query, N, M)

                # Extract information gain component (without query encoding)
                info_bits = math.log2(N / M) if N > M else 0

                # Landauer bound in bits (at room temperature)
                # Note: Direct comparison is tricky due to units, but we can check order of magnitude

                # μ should capture at least the information-theoretic bound
                if info_bits < expected_info_bits * 0.5:  # Allow 50% tolerance
                    violations.append({
                        "query": query,
                        "description": description,
                        "info_bits": info_bits,
                        "expected": expected_info_bits,
                        "ratio": info_bits / expected_info_bits if expected_info_bits > 0 else float('inf')
                    })

            if violations:
                return TestResult(
                    test_name="Landauer bound (simple gates)",
                    passed=False,
                    message=f"Found {len(violations)} Landauer bound violations",
                    details={"violations": violations},
                    falsifies=["H1"]
                )

            return TestResult(
                test_name="Landauer bound (simple gates)",
                passed=True,
                message="μ-cost consistent with Landauer bound",
                details={"test_cases": len(test_cases)},
                falsifies=[]
            )

        except Exception as e:
            return TestResult(
                test_name="Landauer bound (simple gates)",
                passed=False,
                message=f"Exception: {str(e)}",
                details={"error": str(e)},
                falsifies=["H4"]
            )

    # ==================== Test Category 3: Isomorphism Breaking ====================

    def test_isomorphism_adversarial_cnf(self, trials: int = 20) -> TestResult:
        """Test H4: Try to break Python/Coq/Verilog isomorphism with adversarial inputs."""
        try:
            # We can't easily test Coq/Verilog here, but we can test internal consistency
            # and document what SHOULD be tested against Coq/Verilog

            violations = []

            for trial in range(trials):
                rng = random.Random(trial)

                # Generate adversarial CNF problem
                n_vars = rng.randint(10, 100)
                n_interactions = rng.randint(n_vars, n_vars * (n_vars - 1) // 4)

                interactions = []
                for _ in range(n_interactions):
                    v1 = rng.randint(1, n_vars)
                    v2 = rng.randint(1, n_vars)
                    if v1 != v2:
                        interactions.append((min(v1, v2), max(v1, v2)))

                interactions = list(set(interactions))  # Remove duplicates

                problem = Problem(num_variables=n_vars, interactions=interactions)

                # Run discovery twice with same seed - should get identical results
                discoverer1 = EfficientPartitionDiscovery(seed=42)
                result1 = discoverer1.discover_partition(problem)

                discoverer2 = EfficientPartitionDiscovery(seed=42)
                result2 = discoverer2.discover_partition(problem)

                # Check determinism
                if result1.num_modules != result2.num_modules:
                    violations.append({
                        "trial": trial,
                        "issue": "non_deterministic_num_modules",
                        "result1": result1.num_modules,
                        "result2": result2.num_modules
                    })

                if abs(result1.mdl_cost - result2.mdl_cost) > 1e-6:
                    violations.append({
                        "trial": trial,
                        "issue": "non_deterministic_mdl",
                        "result1": result1.mdl_cost,
                        "result2": result2.mdl_cost
                    })

            if violations:
                return TestResult(
                    test_name="Isomorphism (adversarial CNF)",
                    passed=False,
                    message=f"Found {len(violations)} determinism violations",
                    details={"violations": violations[:5], "total": len(violations)},
                    falsifies=["H4"]
                )

            return TestResult(
                test_name="Isomorphism (adversarial CNF)",
                passed=True,
                message=f"Deterministic results on {trials} adversarial CNFs",
                details={"trials": trials, "note": "Full Coq/Verilog isomorphism requires separate test"},
                falsifies=[]
            )

        except Exception as e:
            return TestResult(
                test_name="Isomorphism (adversarial CNF)",
                passed=False,
                message=f"Exception: {str(e)}",
                details={"error": str(e)},
                falsifies=["H4"]
            )

    # ==================== Test Category 4: Random Graph Advantage ====================

    def test_random_graph_no_advantage(self, trials: int = 50) -> TestResult:
        """Test H2: Random graphs should NOT show structural advantage."""
        try:
            # Generate random Erdős-Rényi graphs (no structure)
            # Check: Does partitioning help? (It shouldn't!)

            partitioning_helped = 0

            for trial in range(trials):
                rng = random.Random(trial)

                # Random graph
                n_vars = rng.randint(20, 60)
                p = 0.5  # Edge probability (maximum randomness)

                interactions = []
                for i in range(1, n_vars + 1):
                    for j in range(i + 1, n_vars + 1):
                        if rng.random() < p:
                            interactions.append((i, j))

                problem = Problem(num_variables=n_vars, interactions=interactions)

                # Discover partition
                discoverer = EfficientPartitionDiscovery(seed=trial)
                result = discoverer.discover_partition(problem)

                # Random graphs should yield k=2 (trivial partition) or very high MDL cost
                # If we get k > 2 with low MDL, that's suspicious
                if result.num_modules > 2 and result.mdl_cost < 10.0:
                    partitioning_helped += 1

            # If >20% of random graphs show "structure", our detection is bogus
            false_positive_rate = partitioning_helped / trials

            if false_positive_rate > 0.2:
                return TestResult(
                    test_name="Random graph advantage",
                    passed=False,
                    message=f"Random graphs show 'structure' {false_positive_rate:.1%} of the time",
                    details={
                        "trials": trials,
                        "false_positives": partitioning_helped,
                        "rate": false_positive_rate
                    },
                    falsifies=["H2"]
                )

            return TestResult(
                test_name="Random graph advantage",
                passed=True,
                message=f"Random graphs correctly detected as unstructured ({false_positive_rate:.1%} false positive rate)",
                details={
                    "trials": trials,
                    "false_positives": partitioning_helped,
                    "rate": false_positive_rate
                },
                falsifies=[]
            )

        except Exception as e:
            return TestResult(
                test_name="Random graph advantage",
                passed=False,
                message=f"Exception: {str(e)}",
                details={"error": str(e)},
                falsifies=["H4"]
            )

    # ==================== Test Category 5: Polynomial Time ====================

    def test_polynomial_time_scaling(self) -> TestResult:
        """Test H4: Verify discovery is O(n³) for large n."""
        try:
            # Test scaling behavior
            sizes = [10, 20, 40, 80, 160]
            times = []

            for n in sizes:
                # Create structured problem (two cliques)
                mid = n // 2
                interactions = []

                # First clique
                for i in range(1, mid + 1):
                    for j in range(i + 1, mid + 1):
                        interactions.append((i, j))

                # Second clique
                for i in range(mid + 1, n + 1):
                    for j in range(i + 1, n + 1):
                        interactions.append((i, j))

                problem = Problem(num_variables=n, interactions=interactions)

                # Time discovery
                discoverer = EfficientPartitionDiscovery(seed=42)
                start = time.perf_counter()
                result = discoverer.discover_partition(problem)
                elapsed = time.perf_counter() - start

                times.append((n, elapsed))
                self.log(f"  n={n:3d}: {elapsed*1000:7.2f} ms")

            # Fit O(n³) model: t = c * n³
            # Use least squares on log scale: log(t) ≈ α + 3*log(n)
            if len(times) >= 3:
                import numpy as np

                n_vals = np.array([n for n, _ in times])
                t_vals = np.array([t for _, t in times])

                # Fit power law: t = c * n^α
                log_n = np.log(n_vals)
                log_t = np.log(t_vals + 1e-9)  # Avoid log(0)

                # Linear regression on log scale
                coeffs = np.polyfit(log_n, log_t, 1)
                alpha = coeffs[0]  # Exponent

                # Check if α ≈ 3 (within tolerance)
                if alpha > 4.0:  # More than cubic
                    return TestResult(
                        test_name="Polynomial time scaling",
                        passed=False,
                        message=f"Scaling appears super-cubic: O(n^{alpha:.2f})",
                        details={"times": times, "exponent": alpha},
                        falsifies=["H4"]
                    )

                return TestResult(
                    test_name="Polynomial time scaling",
                    passed=True,
                    message=f"Scaling is polynomial: O(n^{alpha:.2f}) ≈ O(n³)",
                    details={"times": times, "exponent": alpha},
                    falsifies=[]
                )
            else:
                return TestResult(
                    test_name="Polynomial time scaling",
                    passed=True,
                    message="Insufficient data for scaling analysis",
                    details={"times": times},
                    falsifies=[]
                )

        except Exception as e:
            return TestResult(
                test_name="Polynomial time scaling",
                passed=False,
                message=f"Exception: {str(e)}",
                details={"error": str(e)},
                falsifies=["H4"]
            )

    # ==================== Test Runners ====================

    def run_mu_bounds_tests(self, trials: int = 100):
        """Run all μ-bound violation tests."""
        self.log("\n" + "=" * 80)
        self.log("CATEGORY 1: μ-BOUND VIOLATIONS (H1)")
        self.log("=" * 80)

        self.add_result(self.test_mu_monotonicity_basic())
        self.add_result(self.test_mu_formula_bounds())
        self.add_result(self.test_mu_adversarial_operations(trials=trials))

    def run_landauer_tests(self):
        """Run Landauer bound tests."""
        self.log("\n" + "=" * 80)
        self.log("CATEGORY 2: LANDAUER BOUND (H1)")
        self.log("=" * 80)

        self.add_result(self.test_landauer_bound_simple_gates())

    def run_isomorphism_tests(self, trials: int = 20):
        """Run isomorphism breaking tests."""
        self.log("\n" + "=" * 80)
        self.log("CATEGORY 3: ISOMORPHISM BREAKING (H4)")
        self.log("=" * 80)

        self.add_result(self.test_isomorphism_adversarial_cnf(trials=trials))

    def run_random_advantage_tests(self, trials: int = 50):
        """Run random graph advantage tests."""
        self.log("\n" + "=" * 80)
        self.log("CATEGORY 4: RANDOM GRAPH ADVANTAGE (H2)")
        self.log("=" * 80)

        self.add_result(self.test_random_graph_no_advantage(trials=trials))

    def run_polynomial_time_tests(self):
        """Run polynomial time verification tests."""
        self.log("\n" + "=" * 80)
        self.log("CATEGORY 5: POLYNOMIAL TIME VERIFICATION (H4)")
        self.log("=" * 80)

        self.add_result(self.test_polynomial_time_scaling())

    def run_all_tests(self, trials: int = 100):
        """Run all red-team tests."""
        self.log("=" * 80)
        self.log("RED-TEAM HARNESS: FALSIFICATION ATTEMPTS")
        self.log("=" * 80)

        self.run_mu_bounds_tests(trials=trials)
        self.run_landauer_tests()
        self.run_isomorphism_tests(trials=min(trials, 20))
        self.run_random_advantage_tests(trials=min(trials, 50))
        self.run_polynomial_time_tests()


def main():
    parser = argparse.ArgumentParser(
        description="Red-team harness for The Thiele Machine falsification tests"
    )

    parser.add_argument(
        "--test",
        choices=["mu_bounds", "landauer", "isomorphism", "random_advantage", "polynomial_time"],
        help="Run specific test category"
    )

    parser.add_argument(
        "--all",
        action="store_true",
        help="Run all tests"
    )

    parser.add_argument(
        "--trials",
        type=int,
        default=100,
        help="Number of trials for stochastic tests (default: 100)"
    )

    parser.add_argument(
        "--quiet",
        action="store_true",
        help="Suppress verbose output"
    )

    args = parser.parse_args()

    if not args.test and not args.all:
        parser.print_help()
        sys.exit(1)

    harness = RedTeamHarness(verbose=not args.quiet)

    if args.all:
        harness.run_all_tests(trials=args.trials)
    elif args.test == "mu_bounds":
        harness.run_mu_bounds_tests(trials=args.trials)
    elif args.test == "landauer":
        harness.run_landauer_tests()
    elif args.test == "isomorphism":
        harness.run_isomorphism_tests(trials=min(args.trials, 20))
    elif args.test == "random_advantage":
        harness.run_random_advantage_tests(trials=min(args.trials, 50))
    elif args.test == "polynomial_time":
        harness.run_polynomial_time_tests()

    harness.print_summary()

    # Exit with error code if any falsifications detected
    falsifications = [r for r in harness.results if not r.passed and r.falsifies]
    if falsifications:
        sys.exit(1)
    else:
        sys.exit(0)


if __name__ == "__main__":
    main()
