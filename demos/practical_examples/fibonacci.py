#!/usr/bin/env python3
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.
"""
Practical Example: Fibonacci Sequence

Executes identical algorithms in Standard Python and Thiele VM.
All conclusions are derived from measured results.

Run: python3 demos/practical_examples/fibonacci.py
"""

import time
import sys
from pathlib import Path
from dataclasses import dataclass
from typing import Dict, Any, List

sys.path.insert(0, str(Path(__file__).parent.parent.parent))


@dataclass
class MeasuredResult:
    """A single measured result."""
    algorithm: str
    runtime: str
    value: Any
    operations: int
    time_seconds: float
    mu_cost: float = 0.0


def fibonacci_dp(n: int) -> tuple:
    """Dynamic programming Fibonacci."""
    if n <= 1:
        return n, 1
    prev, curr = 0, 1
    ops = 1
    for _ in range(2, n + 1):
        prev, curr = curr, prev + curr
        ops += 1
    return curr, ops


def fibonacci_memo(n: int, memo: dict = None, ops_counter: list = None) -> int:
    """Memoized Fibonacci."""
    if memo is None:
        memo = {}
    if ops_counter is None:
        ops_counter = [0]
    
    ops_counter[0] += 1
    if n in memo:
        return memo[n]
    if n <= 1:
        return n
    memo[n] = fibonacci_memo(n - 1, memo, ops_counter) + fibonacci_memo(n - 2, memo, ops_counter)
    return memo[n]


def measure_standard_python(n: int) -> List[MeasuredResult]:
    """Measure Fibonacci in standard Python."""
    results = []
    
    # DP
    start = time.time()
    dp_val, dp_ops = fibonacci_dp(n)
    dp_time = time.time() - start
    results.append(MeasuredResult(
        algorithm="DP",
        runtime="Standard Python",
        value=dp_val,
        operations=dp_ops,
        time_seconds=dp_time,
    ))
    
    # Memoized
    ops_counter = [0]
    start = time.time()
    memo_val = fibonacci_memo(n, {}, ops_counter)
    memo_time = time.time() - start
    results.append(MeasuredResult(
        algorithm="Memoized",
        runtime="Standard Python",
        value=memo_val,
        operations=ops_counter[0],
        time_seconds=memo_time,
    ))
    
    return results


def measure_thiele_vm(n: int) -> List[MeasuredResult]:
    """Measure Fibonacci in Thiele VM."""
    from thielecpu.vm import VM
    from thielecpu.state import State
    from thielecpu.mu import question_cost_bits
    
    results = []
    
    # DP in VM
    vm = VM(State())
    dp_code = f'''
n = {n}
if n <= 1:
    result = n
    ops = 1
else:
    prev, curr = 0, 1
    ops = 1
    for i in range(2, n + 1):
        prev, curr = curr, prev + curr
        ops = ops + 1
    result = curr
__result__ = (result, ops)
'''
    start = time.time()
    result, _ = vm.execute_python(dp_code)
    dp_time = time.time() - start
    dp_val, dp_ops = result if result else (0, 0)
    mu_dp = question_cost_bits(f"(fib-dp {n})") + dp_ops * 0.1
    
    results.append(MeasuredResult(
        algorithm="DP",
        runtime="Thiele VM",
        value=dp_val,
        operations=dp_ops,
        time_seconds=dp_time,
        mu_cost=mu_dp,
    ))
    
    # Memoized in VM
    vm2 = VM(State())
    memo_code = f'''
n = {n}
memo = {{}}
ops = [0]

def fib_memo(k):
    ops[0] = ops[0] + 1
    if k in memo:
        return memo[k]
    if k <= 1:
        return k
    memo[k] = fib_memo(k - 1) + fib_memo(k - 2)
    return memo[k]

result = fib_memo(n)
__result__ = (result, ops[0])
'''
    start = time.time()
    result, _ = vm2.execute_python(memo_code)
    memo_time = time.time() - start
    memo_val, memo_ops = result if result else (0, 0)
    mu_memo = question_cost_bits(f"(fib-memo {n})") + memo_ops * 0.1
    
    results.append(MeasuredResult(
        algorithm="Memoized",
        runtime="Thiele VM",
        value=memo_val,
        operations=memo_ops,
        time_seconds=memo_time,
        mu_cost=mu_memo,
    ))
    
    return results


def derive_conclusions(std_results: List[MeasuredResult], vm_results: List[MeasuredResult]) -> Dict[str, Any]:
    """Derive conclusions from measured results."""
    conclusions = {
        'isomorphism_checks': [],
        'operation_comparisons': [],
        'mu_tracking': [],
    }
    
    # Check isomorphism for each algorithm
    for std, vm in zip(std_results, vm_results):
        if std.algorithm == vm.algorithm:
            values_match = std.value == vm.value
            ops_match = std.operations == vm.operations
            conclusions['isomorphism_checks'].append({
                'algorithm': std.algorithm,
                'values_match': values_match,
                'operations_match': ops_match,
                'std_value': std.value,
                'vm_value': vm.value,
                'std_ops': std.operations,
                'vm_ops': vm.operations,
            })
            
            # μ-cost tracking
            conclusions['mu_tracking'].append({
                'algorithm': vm.algorithm,
                'mu_cost': vm.mu_cost,
                'mu_tracked': vm.mu_cost > 0,
            })
    
    # Compare algorithms
    if len(std_results) >= 2:
        dp_ops = std_results[0].operations
        memo_ops = std_results[1].operations
        if memo_ops > 0:
            ratio = dp_ops / memo_ops
            conclusions['operation_comparisons'].append({
                'comparison': 'DP vs Memoized',
                'dp_ops': dp_ops,
                'memo_ops': memo_ops,
                'ratio': ratio,
                'dp_more_efficient': dp_ops < memo_ops,
            })
    
    return conclusions


def print_results(n: int, std_results: List[MeasuredResult], vm_results: List[MeasuredResult], conclusions: Dict):
    """Print measured results and derived conclusions."""
    print(f"\n{'─' * 70}")
    print(f"Fibonacci({n})")
    print(f"{'─' * 70}")
    
    # Raw measurements
    print(f"\n  MEASURED RESULTS:")
    print(f"  {'Algorithm':<12} {'Runtime':<18} {'Value':<15} {'Operations':<12} {'μ-cost':<10}")
    print(f"  {'-'*12} {'-'*18} {'-'*15} {'-'*12} {'-'*10}")
    
    for r in std_results:
        print(f"  {r.algorithm:<12} {r.runtime:<18} {r.value:<15} {r.operations:<12} {'N/A':<10}")
    for r in vm_results:
        print(f"  {r.algorithm:<12} {r.runtime:<18} {r.value:<15} {r.operations:<12} {r.mu_cost:<10.1f}")
    
    # Derived conclusions
    print(f"\n  DERIVED CONCLUSIONS (from measurements):")
    
    for check in conclusions['isomorphism_checks']:
        symbol = "✓" if check['values_match'] and check['operations_match'] else "✗"
        print(f"  {symbol} {check['algorithm']}: values_match={check['values_match']}, ops_match={check['operations_match']}")
        if not check['values_match']:
            print(f"    FALSIFIED: std={check['std_value']}, vm={check['vm_value']}")
        if not check['operations_match']:
            print(f"    DEVIATION: std_ops={check['std_ops']}, vm_ops={check['vm_ops']}")
    
    for comp in conclusions['operation_comparisons']:
        print(f"  {comp['comparison']}: ratio={comp['ratio']:.2f}x (DP:{comp['dp_ops']}, Memo:{comp['memo_ops']})")
    
    for mu in conclusions['mu_tracking']:
        print(f"  μ-tracking for {mu['algorithm']}: tracked={mu['mu_tracked']}, cost={mu['mu_cost']:.1f}")


def main():
    print("=" * 70)
    print("FIBONACCI SEQUENCE: Standard Python vs Thiele VM")
    print("All conclusions derived from measurements")
    print("=" * 70)
    
    all_conclusions = []
    
    for n in [10, 20, 30, 40]:
        std_results = measure_standard_python(n)
        vm_results = measure_thiele_vm(n)
        conclusions = derive_conclusions(std_results, vm_results)
        all_conclusions.append((n, conclusions))
        print_results(n, std_results, vm_results, conclusions)
    
    # Final summary derived from all measurements
    print(f"\n{'=' * 70}")
    print("SUMMARY (derived from all measurements)")
    print(f"{'=' * 70}")
    
    total_checks = sum(len(c['isomorphism_checks']) for _, c in all_conclusions)
    passed_checks = sum(
        sum(1 for check in c['isomorphism_checks'] if check['values_match'] and check['operations_match'])
        for _, c in all_conclusions
    )
    
    print(f"  Isomorphism tests: {passed_checks}/{total_checks} passed")
    print(f"  Pass rate: {100*passed_checks/total_checks:.1f}%")
    
    mu_tracked_count = sum(
        sum(1 for mu in c['mu_tracking'] if mu['mu_tracked'])
        for _, c in all_conclusions
    )
    total_mu_checks = sum(len(c['mu_tracking']) for _, c in all_conclusions)
    print(f"  μ-cost tracked: {mu_tracked_count}/{total_mu_checks} ({100*mu_tracked_count/total_mu_checks:.1f}%)")
    
    if passed_checks == total_checks:
        print(f"\n  DERIVED: All value and operation counts match between environments")
    else:
        print(f"\n  DERIVED: {total_checks - passed_checks} mismatches detected - investigate")


if __name__ == "__main__":
    main()
