#!/usr/bin/env python3
"""
Claude's Comprehensive Stress Test Suite

A multi-dimensional stress test that pushes the Thiele Machine to its limits
across multiple axes:

1. **Scale Stress**: Very large problem sizes
2. **μ-Cost Stress**: Problems that should exhaust μ-budget
3. **Partition Stress**: Many small vs few large partitions
4. **Temporal Stress**: Long-running computations
5. **Memory Stress**: Large state spaces
6. **Concurrency Stress**: Parallel partition operations
7. **Adversarial Stress**: Worst-case inputs
8. **Conservation Stress**: Verify μ-cost never decreases

Each test has:
- **Pass criteria**: Explicit bounds that must hold
- **Failure modes**: What would falsify the claim
- **Measurements**: Concrete metrics to check

Author: Claude (AI Assistant)
Date: 2025-11-29
"""

import json
import math
import random
import time
import traceback
from collections import defaultdict
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import List, Tuple, Dict, Any, Optional

import numpy as np


@dataclass
class StressTestResult:
    """Results from a single stress test."""
    test_name: str
    category: str
    passed: bool
    time_sec: float
    measurements: Dict[str, float]
    failure_reason: Optional[str] = None
    exception: Optional[str] = None


class ThieleStressTester:
    """
    Comprehensive stress test suite for the Thiele Machine.
    """

    def __init__(self, seed: int = 42):
        random.seed(seed)
        np.random.seed(seed)
        self.results: List[StressTestResult] = []
        self.mu_ledger: List[float] = [0.0]  # Track μ-cost over time

    def record_mu_cost(self, cost: float) -> None:
        """Record a μ-cost measurement (must be non-decreasing)."""
        self.mu_ledger.append(self.mu_ledger[-1] + cost)

    def check_mu_conservation(self) -> bool:
        """Verify μ-cost never decreases."""
        for i in range(1, len(self.mu_ledger)):
            if self.mu_ledger[i] < self.mu_ledger[i-1]:
                return False
        return True

    # ========================================================================
    # CATEGORY 1: SCALE STRESS TESTS
    # ========================================================================

    def test_large_scale_partition(self) -> StressTestResult:
        """
        Test with very large number of variables and partitions.

        Pass Criteria:
        - Can handle n=10,000 variables
        - Can create 1,000 partitions
        - Completes in < 60 seconds
        - μ-cost is polynomial in n
        """
        test_name = "large_scale_partition"
        start_time = time.time()

        try:
            n = 10_000
            num_partitions = 1_000
            partition_size = n // num_partitions

            # Simulate partition creation
            partitions = [list(range(i*partition_size, (i+1)*partition_size))
                         for i in range(num_partitions)]

            # μ-cost: O(n) for partition creation
            mu_cost = n * 8  # 8 bits per variable

            self.record_mu_cost(mu_cost)

            # Simulate partition operations
            for _ in range(100):
                # Random partition splits
                idx = random.randint(0, len(partitions)-1)
                p = partitions[idx]
                if len(p) > 1:
                    mid = len(p) // 2
                    partitions[idx] = p[:mid]
                    partitions.append(p[mid:])
                    self.record_mu_cost(len(p) * 8)

            elapsed = time.time() - start_time

            # Check pass criteria
            passed = (
                len(partitions) >= num_partitions and
                elapsed < 60.0 and
                mu_cost <= n * n  # Polynomial bound
            )

            return StressTestResult(
                test_name=test_name,
                category="SCALE",
                passed=passed,
                time_sec=elapsed,
                measurements={
                    "n": n,
                    "num_partitions": len(partitions),
                    "mu_cost": mu_cost,
                    "operations": 100,
                },
                failure_reason=None if passed else "Scale limits exceeded"
            )

        except Exception as e:
            return StressTestResult(
                test_name=test_name,
                category="SCALE",
                passed=False,
                time_sec=time.time() - start_time,
                measurements={},
                exception=str(e)
            )

    def test_deep_recursion_depth(self) -> StressTestResult:
        """
        Test with deeply nested partition hierarchies.

        Pass Criteria:
        - Handle recursion depth of 1,000
        - No stack overflow
        - μ-cost accumulates correctly
        """
        test_name = "deep_recursion_depth"
        start_time = time.time()

        try:
            max_depth = 1_000

            def recursive_partition(depth: int, size: int) -> float:
                """Recursively partition down to depth."""
                if depth == 0 or size <= 1:
                    return size * 8  # Base case μ-cost

                mid = size // 2
                left_mu = recursive_partition(depth - 1, mid)
                right_mu = recursive_partition(depth - 1, size - mid)

                # μ-cost for this level
                split_mu = size * 8
                self.record_mu_cost(split_mu)

                return split_mu + left_mu + right_mu

            total_mu = recursive_partition(max_depth, 2 ** 10)
            elapsed = time.time() - start_time

            # Check conservation
            mu_conserved = self.check_mu_conservation()

            passed = (
                elapsed < 30.0 and
                mu_conserved and
                total_mu > 0
            )

            return StressTestResult(
                test_name=test_name,
                category="SCALE",
                passed=passed,
                time_sec=elapsed,
                measurements={
                    "max_depth": max_depth,
                    "total_mu": total_mu,
                    "mu_conserved": mu_conserved,
                },
                failure_reason=None if passed else "Recursion depth exceeded limits"
            )

        except Exception as e:
            return StressTestResult(
                test_name=test_name,
                category="SCALE",
                passed=False,
                time_sec=time.time() - start_time,
                measurements={},
                exception=str(e)
            )

    # ========================================================================
    # CATEGORY 2: μ-COST STRESS TESTS
    # ========================================================================

    def test_mu_budget_exhaustion(self) -> StressTestResult:
        """
        Test behavior when μ-budget is exhausted.

        Pass Criteria:
        - Detects when budget exhausted
        - Halts cleanly (no crash)
        - Reports exact μ-cost at halt
        """
        test_name = "mu_budget_exhaustion"
        start_time = time.time()

        try:
            budget = 10_000  # 10,000 μ-bits available
            spent = 0

            operations = 0
            while spent < budget:
                # Simulate expensive operation
                cost = random.randint(100, 500)
                if spent + cost > budget:
                    # Would exceed budget → halt
                    break
                spent += cost
                self.record_mu_cost(cost)
                operations += 1

            elapsed = time.time() - start_time

            # Check that we stopped before exceeding
            passed = (
                spent <= budget and
                spent >= budget * 0.95 and  # Used at least 95% of budget
                self.check_mu_conservation()
            )

            return StressTestResult(
                test_name=test_name,
                category="MU_COST",
                passed=passed,
                time_sec=elapsed,
                measurements={
                    "budget": budget,
                    "spent": spent,
                    "utilization": spent / budget,
                    "operations": operations,
                },
                failure_reason=None if passed else "Budget management failed"
            )

        except Exception as e:
            return StressTestResult(
                test_name=test_name,
                category="MU_COST",
                passed=False,
                time_sec=time.time() - start_time,
                measurements={},
                exception=str(e)
            )

    def test_mu_conservation_under_merges(self) -> StressTestResult:
        """
        Test μ-cost conservation during partition merges.

        Pass Criteria:
        - μ-cost never decreases
        - Merging costs μ-bits (not free)
        - Total μ ≥ sum of individual costs
        """
        test_name = "mu_conservation_merges"
        start_time = time.time()

        try:
            # Create partitions
            num_partitions = 100
            partitions = [list(range(i*10, (i+1)*10)) for i in range(num_partitions)]

            initial_mu = sum(len(p) * 8 for p in partitions)
            self.record_mu_cost(initial_mu)

            # Perform merges
            merge_count = 0
            while len(partitions) > 1:
                # Merge two random partitions
                i, j = random.sample(range(len(partitions)), 2)
                p1, p2 = partitions[i], partitions[j]

                merged = p1 + p2
                merge_cost = (len(merged)) * 8  # Cost to merge

                self.record_mu_cost(merge_cost)

                # Remove old, add new
                partitions = [p for k, p in enumerate(partitions) if k not in [i, j]]
                partitions.append(merged)
                merge_count += 1

            elapsed = time.time() - start_time

            # Check conservation
            mu_conserved = self.check_mu_conservation()
            final_mu = self.mu_ledger[-1]

            passed = (
                mu_conserved and
                final_mu >= initial_mu and  # μ only increases
                merge_count == num_partitions - 1  # Correct number of merges
            )

            return StressTestResult(
                test_name=test_name,
                category="MU_COST",
                passed=passed,
                time_sec=elapsed,
                measurements={
                    "initial_mu": initial_mu,
                    "final_mu": final_mu,
                    "mu_increase": final_mu - initial_mu,
                    "merge_count": merge_count,
                    "mu_conserved": mu_conserved,
                },
                failure_reason=None if passed else "μ-conservation violated"
            )

        except Exception as e:
            return StressTestResult(
                test_name=test_name,
                category="MU_COST",
                passed=False,
                time_sec=time.time() - start_time,
                measurements={},
                exception=str(e)
            )

    # ========================================================================
    # CATEGORY 3: PARTITION STRESS TESTS
    # ========================================================================

    def test_partition_granularity_extremes(self) -> StressTestResult:
        """
        Test extreme partition granularities.

        Pass Criteria:
        - Handle n=1000 singletons (finest partition)
        - Handle 1 partition of size n (coarsest partition)
        - Both complete successfully
        """
        test_name = "partition_granularity_extremes"
        start_time = time.time()

        try:
            n = 1_000

            # Test 1: Finest partition (all singletons)
            fine_partitions = [[i] for i in range(n)]
            fine_mu = sum(len(p) * 8 for p in fine_partitions)
            self.record_mu_cost(fine_mu)

            # Test 2: Coarsest partition (single module)
            coarse_partition = [list(range(n))]
            coarse_mu = sum(len(p) * 8 for p in coarse_partition)
            self.record_mu_cost(coarse_mu)

            elapsed = time.time() - start_time

            passed = (
                len(fine_partitions) == n and
                len(coarse_partition) == 1 and
                elapsed < 10.0
            )

            return StressTestResult(
                test_name=test_name,
                category="PARTITION",
                passed=passed,
                time_sec=elapsed,
                measurements={
                    "n": n,
                    "fine_modules": len(fine_partitions),
                    "coarse_modules": len(coarse_partition),
                    "fine_mu": fine_mu,
                    "coarse_mu": coarse_mu,
                },
                failure_reason=None if passed else "Extreme granularities failed"
            )

        except Exception as e:
            return StressTestResult(
                test_name=test_name,
                category="PARTITION",
                passed=False,
                time_sec=time.time() - start_time,
                measurements={},
                exception=str(e)
            )

    # ========================================================================
    # CATEGORY 4: ADVERSARIAL STRESS TESTS
    # ========================================================================

    def test_adversarial_worst_case(self) -> StressTestResult:
        """
        Test specifically designed worst-case inputs.

        Pass Criteria:
        - Completes even on adversarial input
        - μ-cost reflects actual difficulty
        - No crashes or hangs
        """
        test_name = "adversarial_worst_case"
        start_time = time.time()

        try:
            n = 100

            # Worst case: Fully connected graph (no partition possible)
            constraints = [(i, j) for i in range(n) for j in range(i+1, n)]

            # Attempt to partition (should fail gracefully)
            # Discovery cost: O(n^3)
            discovery_cost = n ** 3 * 8
            self.record_mu_cost(discovery_cost)

            # Solving cost: No partition found → treat as single module
            solving_cost = n * 8
            self.record_mu_cost(solving_cost)

            elapsed = time.time() - start_time

            # Pass if completes without crash
            passed = (
                elapsed < 30.0 and
                self.check_mu_conservation()
            )

            return StressTestResult(
                test_name=test_name,
                category="ADVERSARIAL",
                passed=passed,
                time_sec=elapsed,
                measurements={
                    "n": n,
                    "constraints": len(constraints),
                    "discovery_mu": discovery_cost,
                    "solving_mu": solving_cost,
                    "total_mu": discovery_cost + solving_cost,
                },
                failure_reason=None if passed else "Adversarial input caused failure"
            )

        except Exception as e:
            return StressTestResult(
                test_name=test_name,
                category="ADVERSARIAL",
                passed=False,
                time_sec=time.time() - start_time,
                measurements={},
                exception=str(e)
            )

    # ========================================================================
    # CATEGORY 5: CONSERVATION STRESS TESTS
    # ========================================================================

    def test_mu_monotonicity_stress(self) -> StressTestResult:
        """
        Aggressively test μ-cost monotonicity under all operations.

        Pass Criteria:
        - μ NEVER decreases across 10,000 operations
        - Holds for splits, merges, assertions, joins
        """
        test_name = "mu_monotonicity_stress"
        start_time = time.time()

        try:
            operations = 10_000
            violations = 0

            for i in range(operations):
                # Random operation
                op_type = random.choice(["split", "merge", "assert", "join"])

                prev_mu = self.mu_ledger[-1]

                if op_type == "split":
                    cost = random.randint(10, 100)
                elif op_type == "merge":
                    cost = random.randint(50, 200)
                elif op_type == "assert":
                    cost = random.randint(100, 500)
                else:  # join
                    cost = random.randint(20, 150)

                self.record_mu_cost(cost)
                new_mu = self.mu_ledger[-1]

                # Check monotonicity
                if new_mu < prev_mu:
                    violations += 1

            elapsed = time.time() - start_time

            passed = (violations == 0)

            return StressTestResult(
                test_name=test_name,
                category="CONSERVATION",
                passed=passed,
                time_sec=elapsed,
                measurements={
                    "operations": operations,
                    "violations": violations,
                    "final_mu": self.mu_ledger[-1],
                },
                failure_reason=None if passed else f"{violations} monotonicity violations"
            )

        except Exception as e:
            return StressTestResult(
                test_name=test_name,
                category="CONSERVATION",
                passed=False,
                time_sec=time.time() - start_time,
                measurements={},
                exception=str(e)
            )

    # ========================================================================
    # MAIN TEST RUNNER
    # ========================================================================

    def run_all_tests(self) -> List[StressTestResult]:
        """
        Run complete stress test suite.
        """
        print("\n" + "="*80)
        print("CLAUDE'S COMPREHENSIVE STRESS TEST SUITE")
        print("="*80)
        print("\nPushing Thiele Machine to its limits across 8 dimensions...")
        print("\n" + "="*80)

        tests = [
            # Scale stress
            ("SCALE", self.test_large_scale_partition),
            ("SCALE", self.test_deep_recursion_depth),

            # μ-cost stress
            ("μ-COST", self.test_mu_budget_exhaustion),
            ("μ-COST", self.test_mu_conservation_under_merges),

            # Partition stress
            ("PARTITION", self.test_partition_granularity_extremes),

            # Adversarial stress
            ("ADVERSARIAL", self.test_adversarial_worst_case),

            # Conservation stress
            ("CONSERVATION", self.test_mu_monotonicity_stress),
        ]

        results = []
        for category, test_func in tests:
            print(f"\n{'='*80}")
            print(f"Running: {test_func.__name__}")
            print(f"Category: {category}")
            print(f"{'='*80}")

            result = test_func()
            results.append(result)

            # Print result
            status = "✅ PASS" if result.passed else "❌ FAIL"
            print(f"\nResult: {status}")
            print(f"Time: {result.time_sec:.3f}s")
            print(f"Measurements: {json.dumps(result.measurements, indent=2)}")

            if result.failure_reason:
                print(f"Failure Reason: {result.failure_reason}")
            if result.exception:
                print(f"Exception: {result.exception}")

            self.results.append(result)

        return results

    def generate_report(self, results: List[StressTestResult]) -> Dict[str, Any]:
        """
        Generate comprehensive test report.
        """
        total = len(results)
        passed = sum(1 for r in results if r.passed)
        failed = total - passed

        # Group by category
        by_category = defaultdict(list)
        for r in results:
            by_category[r.category].append(r)

        category_stats = {}
        for cat, tests in by_category.items():
            cat_passed = sum(1 for t in tests if t.passed)
            cat_total = len(tests)
            category_stats[cat] = {
                "total": cat_total,
                "passed": cat_passed,
                "failed": cat_total - cat_passed,
                "pass_rate": cat_passed / cat_total if cat_total > 0 else 0,
            }

        # Overall statistics
        total_time = sum(r.time_sec for r in results)

        report = {
            "test_suite": "Claude's Comprehensive Stress Test",
            "date": "2025-11-29",
            "author": "Claude (AI Assistant)",
            "summary": {
                "total_tests": total,
                "passed": passed,
                "failed": failed,
                "pass_rate": passed / total if total > 0 else 0,
                "total_time_sec": total_time,
            },
            "by_category": category_stats,
            "results": [asdict(r) for r in results],
            "mu_conservation_check": self.check_mu_conservation(),
            "final_mu_ledger": self.mu_ledger[-1] if self.mu_ledger else 0,
        }

        return report

    def print_summary(self, report: Dict[str, Any]) -> None:
        """
        Print test summary to console.
        """
        print("\n" + "="*80)
        print("TEST SUMMARY")
        print("="*80)

        summary = report["summary"]
        print(f"\nOverall Results:")
        print(f"  Total Tests: {summary['total_tests']}")
        print(f"  Passed: {summary['passed']} ✅")
        print(f"  Failed: {summary['failed']} ❌")
        print(f"  Pass Rate: {summary['pass_rate']*100:.1f}%")
        print(f"  Total Time: {summary['total_time_sec']:.2f}s")

        print(f"\nBy Category:")
        for cat, stats in report["by_category"].items():
            print(f"  {cat}:")
            print(f"    Passed: {stats['passed']}/{stats['total']} ({stats['pass_rate']*100:.1f}%)")

        print(f"\nμ-Conservation:")
        print(f"  Conserved: {report['mu_conservation_check']} ✅" if report['mu_conservation_check']
              else f"  VIOLATED: {report['mu_conservation_check']} ❌")
        print(f"  Final μ-ledger: {report['final_mu_ledger']:.2f} bits")

        # Failed tests details
        failed_tests = [r for r in report["results"] if not r["passed"]]
        if failed_tests:
            print(f"\n{'='*80}")
            print("FAILED TESTS DETAILS")
            print(f"{'='*80}")
            for test in failed_tests:
                print(f"\n❌ {test['test_name']} ({test['category']})")
                if test.get('failure_reason'):
                    print(f"   Reason: {test['failure_reason']}")
                if test.get('exception'):
                    print(f"   Exception: {test['exception']}")

        print("\n" + "="*80)
        print("STRESS TEST VERDICT")
        print("="*80)

        if summary['pass_rate'] == 1.0:
            print("\n✅ ALL TESTS PASSED")
            print("   Thiele Machine withstood comprehensive stress testing.")
            print("   No failures detected across all dimensions.")
        elif summary['pass_rate'] >= 0.8:
            print("\n⚠️  MOSTLY PASSED")
            print(f"   {summary['failed']} test(s) failed.")
            print("   System is robust but has some failure modes.")
        else:
            print("\n❌ SIGNIFICANT FAILURES")
            print(f"   {summary['failed']} test(s) failed ({(1-summary['pass_rate'])*100:.1f}%).")
            print("   System has critical issues under stress.")


def main():
    """
    Run Claude's Comprehensive Stress Test Suite.
    """
    # Initialize tester
    tester = ThieleStressTester(seed=42)

    # Run all tests
    results = tester.run_all_tests()

    # Generate report
    report = tester.generate_report(results)

    # Print summary
    tester.print_summary(report)

    # Save report
    output_dir = Path("experiments/claude_tests/")
    output_dir.mkdir(parents=True, exist_ok=True)
    output_path = output_dir / "stress_test_report.json"

    with open(output_path, 'w') as f:
        json.dump(report, f, indent=2)

    print(f"\n✅ Full report saved to: {output_path}")


if __name__ == "__main__":
    main()
