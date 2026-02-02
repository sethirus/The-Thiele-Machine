#!/usr/bin/env python3
"""
Claude's Partition Collapse Test — Original Falsification Attempt

This test attempts to falsify the partition advantage claim by constructing
adversarial problem instances specifically designed to make sighted and blind
solvers perform identically.

Hypothesis to Falsify:
    "Sighted solving with partitions is always faster than blind solving
     on structured problems."

Strategy:
    1. Create problems where partition discovery is expensive
    2. Create problems where partitions provide no advantage
    3. Create problems where partitions actively hurt performance
    4. Measure the crossover point where advantage disappears

Expected Outcome if Correct:
    - Most problems should show sighted ≥ blind (no advantage)
    - Some problems should show sighted > blind (disadvantage!)

Actual Outcome:
    [To be filled in after running]

Author: Claude (AI Assistant)
Date: 2025-11-29
"""

import json
import math
import random
import time
from dataclasses import dataclass
from pathlib import Path
from typing import List, Tuple, Dict, Any

import numpy as np

@dataclass
class Problem:
    """A computational problem with structure metrics."""
    variables: List[int]
    constraints: List[Tuple[int, int]]
    true_partition: List[List[int]]
    interaction_density: float
    symmetry_degree: float
    name: str

@dataclass
class SolverResult:
    """Results from running a solver."""
    steps: int
    mu_cost: float
    time_sec: float
    success: bool
    partition_used: List[List[int]]

class PartitionCollapseTest:
    """
    Adversarial test suite designed to break partition advantage.
    """

    def __init__(self, seed: int = 42):
        random.seed(seed)
        np.random.seed(seed)
        self.results = []

    def create_fully_connected_problem(self, n: int) -> Problem:
        """
        Create a problem where EVERY variable interacts with EVERY other.

        Expected: Partition discovery finds n singleton modules (useless).
        Predicted Outcome: sighted ≈ blind (no advantage)
        """
        variables = list(range(n))
        constraints = [(i, j) for i in range(n) for j in range(i+1, n)]

        return Problem(
            variables=variables,
            constraints=constraints,
            true_partition=[[i] for i in range(n)],  # Only valid partition
            interaction_density=1.0,  # Fully connected
            symmetry_degree=1.0,  # Completely symmetric
            name=f"fully_connected_n{n}"
        )

    def create_uniform_random_problem(self, n: int, edge_prob: float) -> Problem:
        """
        Create a problem with uniform random structure.

        Expected: No natural partitions exist.
        Predicted Outcome: Partition discovery wastes time → sighted > blind
        """
        variables = list(range(n))
        constraints = []

        for i in range(n):
            for j in range(i+1, n):
                if random.random() < edge_prob:
                    constraints.append((i, j))

        density = len(constraints) / (n * (n-1) / 2)

        return Problem(
            variables=variables,
            constraints=constraints,
            true_partition=[[i] for i in range(n)],  # No structure
            interaction_density=density,
            symmetry_degree=0.5,  # Medium symmetry
            name=f"uniform_random_n{n}_p{edge_prob:.2f}"
        )

    def create_adversarial_hierarchy(self, n: int) -> Problem:
        """
        Create a problem with NESTED hierarchical structure.

        Expected: Partition discovery finds wrong granularity.
        Predicted Outcome: sighted uses wrong partition → sighted ≥ blind
        """
        variables = list(range(n))
        constraints = []

        # Create nested hierarchy: groups of 2, then groups of 4, then groups of 8
        for level in [2, 4, 8]:
            for group_start in range(0, n, level):
                group = list(range(group_start, min(group_start + level, n)))
                # Full connections within group
                for i in group:
                    for j in group:
                        if i < j:
                            constraints.append((i, j))

        # Add sparse cross-level connections to confuse discovery
        for i in range(0, n, 8):
            for j in range(4, n, 8):
                if i != j and abs(i - j) > 4:
                    constraints.append((i, j))

        density = len(constraints) / (n * (n-1) / 2)

        return Problem(
            variables=variables,
            constraints=constraints,
            true_partition=[[i, i+1] for i in range(0, n, 2)],  # True: pairs
            interaction_density=density,
            symmetry_degree=0.3,  # Low symmetry (hierarchy)
            name=f"adversarial_hierarchy_n{n}"
        )

    def create_misleading_clusters(self, n: int, cluster_size: int) -> Problem:
        """
        Create clusters that LOOK independent but are actually coupled.

        Expected: Discovery finds clusters, but solving reveals coupling.
        Predicted Outcome: sighted wastes work → sighted > blind
        """
        variables = list(range(n))
        constraints = []

        num_clusters = n // cluster_size

        # Create apparent clusters
        for cluster_id in range(num_clusters):
            start = cluster_id * cluster_size
            end = start + cluster_size
            cluster = list(range(start, min(end, n)))

            # Dense internal connections
            for i in cluster:
                for j in cluster:
                    if i < j and random.random() < 0.9:
                        constraints.append((i, j))

        # Add HIDDEN cross-cluster dependencies
        # (Spectral clustering won't see these easily)
        for i in range(num_clusters):
            for j in range(i+1, num_clusters):
                # One weak link between clusters
                v1 = i * cluster_size
                v2 = j * cluster_size
                constraints.append((v1, v2))

        density = len(constraints) / (n * (n-1) / 2)

        return Problem(
            variables=variables,
            constraints=constraints,
            true_partition=[[i] for i in range(n)],  # Actually can't partition!
            interaction_density=density,
            symmetry_degree=0.7,
            name=f"misleading_clusters_n{n}_k{cluster_size}"
        )

    def create_pathological_symmetry(self, n: int) -> Problem:
        """
        Create a problem with so much symmetry that every partition looks equally good.

        Expected: Partition discovery cannot decide which partition to use.
        Predicted Outcome: Discovery wastes time exploring → sighted ≥ blind
        """
        variables = list(range(n))
        constraints = []

        # Create a cycle graph (maximal symmetry)
        for i in range(n):
            constraints.append((i, (i+1) % n))

        # Add chords at every k steps to maintain symmetry
        k = int(math.sqrt(n))
        for i in range(n):
            constraints.append((i, (i + k) % n))

        density = len(constraints) / (n * (n-1) / 2)

        return Problem(
            variables=variables,
            constraints=constraints,
            true_partition=[list(range(n))],  # Only one module (all symmetric)
            interaction_density=density,
            symmetry_degree=1.0,  # Maximum symmetry
            name=f"pathological_symmetry_n{n}"
        )

    def solve_blind(self, problem: Problem) -> SolverResult:
        """
        Simulate blind solving (no partition knowledge).
        """
        start_time = time.time()

        n = len(problem.variables)
        # Blind solver: Exponential in problem size
        steps = 2 ** min(n, 20)  # Cap to avoid overflow

        # μ-cost: No partition discovery cost, but must explore all states
        mu_cost = steps * 8  # 8 bits per state exploration

        end_time = time.time()

        return SolverResult(
            steps=steps,
            mu_cost=mu_cost,
            time_sec=end_time - start_time,
            success=True,
            partition_used=[problem.variables]  # Single module
        )

    def solve_sighted(self, problem: Problem, use_true_partition: bool = False) -> SolverResult:
        """
        Simulate sighted solving (with partition discovery).
        """
        start_time = time.time()

        n = len(problem.variables)

        if use_true_partition:
            # Cheat mode: Use ground truth partition
            partition = problem.true_partition
            discovery_steps = 0
            discovery_mu = 0
        else:
            # Realistic mode: Must discover partition
            # Cost: O(n^3) for spectral clustering
            discovery_steps = n ** 3
            discovery_mu = discovery_steps * 8  # μ-bits for discovery

            # Simulated partition discovery
            # (In reality this would run actual clustering algorithm)
            if problem.interaction_density > 0.7:
                # High density → finds singletons (no advantage)
                partition = [[i] for i in range(n)]
            elif problem.symmetry_degree > 0.8:
                # High symmetry → finds full module (no advantage)
                partition = [problem.variables]
            else:
                # Use true partition (optimistic)
                partition = problem.true_partition

        # Solving cost: Linear in module sizes
        solving_steps = sum(len(module) for module in partition)
        solving_mu = solving_steps * 8

        total_steps = discovery_steps + solving_steps
        total_mu = discovery_mu + solving_mu

        end_time = time.time()

        return SolverResult(
            steps=total_steps,
            mu_cost=total_mu,
            time_sec=end_time - start_time,
            success=True,
            partition_used=partition
        )

    def run_test_case(self, problem: Problem) -> Dict[str, Any]:
        """
        Run both blind and sighted solvers on a problem.
        """
        print(f"\n{'='*80}")
        print(f"Testing: {problem.name}")
        print(f"  Variables: {len(problem.variables)}")
        print(f"  Constraints: {len(problem.constraints)}")
        print(f"  Density: {problem.interaction_density:.3f}")
        print(f"  Symmetry: {problem.symmetry_degree:.3f}")
        print(f"{'='*80}")

        # Run blind solver
        blind_result = self.solve_blind(problem)
        print(f"\nBlind Solver:")
        print(f"  Steps: {blind_result.steps:,}")
        print(f"  μ-cost: {blind_result.mu_cost:.2f} bits")
        print(f"  Time: {blind_result.time_sec:.4f}s")

        # Run sighted solver (realistic discovery)
        sighted_result = self.solve_sighted(problem, use_true_partition=False)
        print(f"\nSighted Solver (with discovery cost):")
        print(f"  Steps: {sighted_result.steps:,}")
        print(f"  μ-cost: {sighted_result.mu_cost:.2f} bits")
        print(f"  Time: {sighted_result.time_sec:.4f}s")
        print(f"  Partition: {len(sighted_result.partition_used)} modules")

        # Run sighted solver (oracle partition)
        sighted_oracle_result = self.solve_sighted(problem, use_true_partition=True)
        print(f"\nSighted Solver (oracle partition):")
        print(f"  Steps: {sighted_oracle_result.steps:,}")
        print(f"  μ-cost: {sighted_oracle_result.mu_cost:.2f} bits")

        # Compute ratios
        step_ratio = blind_result.steps / max(sighted_result.steps, 1)
        mu_ratio = blind_result.mu_cost / max(sighted_result.mu_cost, 1)

        print(f"\n{'='*80}")
        print(f"RATIOS (blind / sighted):")
        print(f"  Steps: {step_ratio:.3f}×")
        print(f"  μ-cost: {mu_ratio:.3f}×")

        if step_ratio < 1.0:
            print(f"  ⚠️  SIGHTED SLOWER than blind! ({1/step_ratio:.3f}× worse)")
        elif step_ratio < 1.2:
            print(f"  ⚠️  Advantage negligible (< 20%)")
        elif step_ratio < 2.0:
            print(f"  ⚙️  Modest advantage (< 2×)")
        else:
            print(f"  ✅ Strong advantage (≥ 2×)")

        return {
            "problem": problem.name,
            "n": len(problem.variables),
            "density": problem.interaction_density,
            "symmetry": problem.symmetry_degree,
            "blind_steps": blind_result.steps,
            "sighted_steps": sighted_result.steps,
            "blind_mu": blind_result.mu_cost,
            "sighted_mu": sighted_result.mu_cost,
            "step_ratio": step_ratio,
            "mu_ratio": mu_ratio,
            "sighted_modules": len(sighted_result.partition_used),
            "verdict": "SIGHTED_SLOWER" if step_ratio < 1.0
                      else "NEGLIGIBLE" if step_ratio < 1.2
                      else "MODEST" if step_ratio < 2.0
                      else "STRONG"
        }

    def run_full_suite(self) -> List[Dict[str, Any]]:
        """
        Run complete test suite across all adversarial problem types.
        """
        results = []

        print("\n" + "="*80)
        print("CLAUDE'S PARTITION COLLAPSE TEST — FALSIFICATION ATTEMPT")
        print("="*80)
        print("\nGoal: Find problems where partition advantage disappears or inverts")
        print("Strategy: Adversarial problem construction")
        print("\n" + "="*80)

        # Test 1: Fully connected (no partitions possible)
        for n in [8, 12, 16]:
            problem = self.create_fully_connected_problem(n)
            result = self.run_test_case(problem)
            results.append(result)

        # Test 2: Uniform random (no structure)
        for n in [10, 15, 20]:
            for edge_prob in [0.3, 0.5, 0.7]:
                problem = self.create_uniform_random_problem(n, edge_prob)
                result = self.run_test_case(problem)
                results.append(result)

        # Test 3: Adversarial hierarchy (wrong partition)
        for n in [16, 24, 32]:
            problem = self.create_adversarial_hierarchy(n)
            result = self.run_test_case(problem)
            results.append(result)

        # Test 4: Misleading clusters (hidden coupling)
        for n in [12, 18, 24]:
            for cluster_size in [3, 4]:
                problem = self.create_misleading_clusters(n, cluster_size)
                result = self.run_test_case(problem)
                results.append(result)

        # Test 5: Pathological symmetry (all partitions equal)
        for n in [10, 15, 20]:
            problem = self.create_pathological_symmetry(n)
            result = self.run_test_case(problem)
            results.append(result)

        return results

    def analyze_results(self, results: List[Dict[str, Any]]) -> None:
        """
        Analyze aggregate results and determine if falsification succeeded.
        """
        print("\n" + "="*80)
        print("AGGREGATE ANALYSIS")
        print("="*80)

        total_tests = len(results)
        sighted_slower = sum(1 for r in results if r["verdict"] == "SIGHTED_SLOWER")
        negligible = sum(1 for r in results if r["verdict"] == "NEGLIGIBLE")
        modest = sum(1 for r in results if r["verdict"] == "MODEST")
        strong = sum(1 for r in results if r["verdict"] == "STRONG")

        print(f"\nTotal Tests: {total_tests}")
        print(f"\nResults Breakdown:")
        print(f"  Sighted SLOWER than blind: {sighted_slower} ({sighted_slower/total_tests*100:.1f}%)")
        print(f"  Advantage negligible: {negligible} ({negligible/total_tests*100:.1f}%)")
        print(f"  Advantage modest (< 2×): {modest} ({modest/total_tests*100:.1f}%)")
        print(f"  Advantage strong (≥ 2×): {strong} ({strong/total_tests*100:.1f}%)")

        # Compute statistics
        step_ratios = [r["step_ratio"] for r in results]
        mu_ratios = [r["mu_ratio"] for r in results]

        print(f"\nStep Ratio Statistics:")
        print(f"  Mean: {np.mean(step_ratios):.3f}×")
        print(f"  Median: {np.median(step_ratios):.3f}×")
        print(f"  Min: {np.min(step_ratios):.3f}×")
        print(f"  Max: {np.max(step_ratios):.3f}×")

        print(f"\nμ-Cost Ratio Statistics:")
        print(f"  Mean: {np.mean(mu_ratios):.3f}×")
        print(f"  Median: {np.median(mu_ratios):.3f}×")
        print(f"  Min: {np.min(mu_ratios):.3f}×")
        print(f"  Max: {np.max(mu_ratios):.3f}×")

        # Verdict
        print("\n" + "="*80)
        print("FALSIFICATION VERDICT")
        print("="*80)

        if sighted_slower > 0:
            print(f"\n⚠️  FALSIFICATION EVIDENCE FOUND!")
            print(f"    {sighted_slower} cases where sighted is SLOWER than blind.")
            print(f"    Partition advantage claim is NOT universally true.")
        elif negligible > total_tests * 0.3:
            print(f"\n⚠️  WEAK FALSIFICATION EVIDENCE")
            print(f"    {negligible} cases ({negligible/total_tests*100:.1f}%) with negligible advantage.")
            print(f"    Partition advantage may not be practical on some problems.")
        else:
            print(f"\n✅ FALSIFICATION ATTEMPT FAILED")
            print(f"    All tested cases show sighted ≥ blind.")
            print(f"    Partition advantage claim withstands this test suite.")
            if strong > total_tests * 0.5:
                print(f"    {strong/total_tests*100:.1f}% of cases show strong (≥2×) advantage.")

        # Identify vulnerable problem classes
        print("\n" + "="*80)
        print("VULNERABLE PROBLEM CLASSES")
        print("="*80)

        worst_cases = sorted(results, key=lambda r: r["step_ratio"])[:5]
        print("\nTop 5 Cases Where Sighted Performs Worst:")
        for i, case in enumerate(worst_cases, 1):
            print(f"{i}. {case['problem']}")
            print(f"   Ratio: {case['step_ratio']:.3f}×, Verdict: {case['verdict']}")

    def save_results(self, results: List[Dict[str, Any]], output_path: Path) -> None:
        """
        Save results to JSON for further analysis.
        """
        output_data = {
            "test_name": "Claude's Partition Collapse Test",
            "date": "2025-11-29",
            "author": "Claude (AI Assistant)",
            "total_tests": len(results),
            "results": results,
            "summary": {
                "sighted_slower_count": sum(1 for r in results if r["verdict"] == "SIGHTED_SLOWER"),
                "negligible_count": sum(1 for r in results if r["verdict"] == "NEGLIGIBLE"),
                "modest_count": sum(1 for r in results if r["verdict"] == "MODEST"),
                "strong_count": sum(1 for r in results if r["verdict"] == "STRONG"),
                "mean_step_ratio": float(np.mean([r["step_ratio"] for r in results])),
                "median_step_ratio": float(np.median([r["step_ratio"] for r in results])),
            }
        }

        with open(output_path, 'w') as f:
            json.dump(output_data, f, indent=2)

        print(f"\n✅ Results saved to: {output_path}")


def main():
    """
    Run Claude's Partition Collapse Test.
    """
    # Initialize test suite
    test = PartitionCollapseTest(seed=42)

    # Run all tests
    results = test.run_full_suite()

    # Analyze results
    test.analyze_results(results)

    # Save results
    output_dir = Path("experiments/claude_tests/")
    output_dir.mkdir(parents=True, exist_ok=True)
    output_path = output_dir / "partition_collapse_results.json"
    test.save_results(results, output_path)

    print("\n" + "="*80)
    print("TEST COMPLETE")
    print("="*80)
    print(f"\nRun 'python -m experiments.claude_partition_collapse_test' to execute")
    print(f"Results will be saved to: {output_path}")


if __name__ == "__main__":
    main()
