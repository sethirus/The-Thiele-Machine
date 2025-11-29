#!/usr/bin/env python3
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.
"""
Recursion Patterns

Tests different recursion paradigms:
- Deep recursion (stack depth testing)
- Mutual recursion
- Tail recursion patterns
- Memoization with recursion
- Tree recursion
"""

import time
from typing import Dict, Any, List, Tuple


# =============================================================================
# RECURSION ALGORITHMS (identical in both environments)
# =============================================================================

def factorial_recursive(n: int) -> Tuple[int, int]:
    """Standard recursive factorial."""
    calls = [0]
    
    def fact(x):
        calls[0] += 1
        if x <= 1:
            return 1
        return x * fact(x - 1)
    
    result = fact(n)
    return result, calls[0]


def fibonacci_recursive(n: int) -> Tuple[int, int]:
    """Naive recursive Fibonacci (exponential)."""
    calls = [0]
    
    def fib(x):
        calls[0] += 1
        if x <= 1:
            return x
        return fib(x - 1) + fib(x - 2)
    
    result = fib(n)
    return result, calls[0]


def fibonacci_memoized(n: int) -> Tuple[int, int]:
    """Memoized recursive Fibonacci (linear)."""
    calls = [0]
    memo = {}
    
    def fib(x):
        calls[0] += 1
        if x in memo:
            return memo[x]
        if x <= 1:
            result = x
        else:
            result = fib(x - 1) + fib(x - 2)
        memo[x] = result
        return result
    
    result = fib(n)
    return result, calls[0]


def mutual_recursion_even_odd(n: int) -> Tuple[bool, int]:
    """Mutual recursion: is_even and is_odd call each other."""
    calls = [0]
    
    def is_even(x):
        calls[0] += 1
        if x == 0:
            return True
        return is_odd(x - 1)
    
    def is_odd(x):
        calls[0] += 1
        if x == 0:
            return False
        return is_even(x - 1)
    
    result = is_even(n)
    return result, calls[0]


def tree_traversal_count(depth: int) -> Tuple[int, int]:
    """Simulate binary tree traversal (counting nodes)."""
    calls = [0]
    
    def traverse(d):
        calls[0] += 1
        if d == 0:
            return 1
        return 1 + traverse(d - 1) + traverse(d - 1)
    
    result = traverse(depth)
    return result, calls[0]


def ackermann(m: int, n: int) -> Tuple[int, int]:
    """Ackermann function - deeply recursive."""
    calls = [0]
    
    def ack(mm, nn):
        calls[0] += 1
        if mm == 0:
            return nn + 1
        if nn == 0:
            return ack(mm - 1, 1)
        return ack(mm - 1, ack(mm, nn - 1))
    
    result = ack(m, n)
    return result, calls[0]


def sum_nested_list(lst: List) -> Tuple[int, int]:
    """Recursively sum nested list structure."""
    calls = [0]
    
    def sum_list(l):
        calls[0] += 1
        total = 0
        for item in l:
            if isinstance(item, list):
                total += sum_list(item)
            else:
                total += item
        return total
    
    result = sum_list(lst)
    return result, calls[0]


def gcd_recursive(a: int, b: int) -> Tuple[int, int]:
    """Euclidean GCD using recursion."""
    calls = [0]
    
    def gcd(x, y):
        calls[0] += 1
        if y == 0:
            return x
        return gcd(y, x % y)
    
    result = gcd(a, b)
    return result, calls[0]


# =============================================================================
# TEST RUNNER
# =============================================================================

def run_standard_python() -> Dict[str, Any]:
    """Run all recursion tests with standard Python."""
    results = {'runtime': 'Standard Python', 'tests': []}
    
    test_cases = [
        # Factorial
        ("Factorial 0", lambda: factorial_recursive(0)),
        ("Factorial 5", lambda: factorial_recursive(5)),
        ("Factorial 10", lambda: factorial_recursive(10)),
        
        # Fibonacci (small n to avoid exponential blowup)
        ("Fib naive 10", lambda: fibonacci_recursive(10)),
        ("Fib naive 15", lambda: fibonacci_recursive(15)),
        ("Fib memo 10", lambda: fibonacci_memoized(10)),
        ("Fib memo 50", lambda: fibonacci_memoized(50)),
        ("Fib memo 100", lambda: fibonacci_memoized(100)),
        
        # Mutual recursion
        ("Even/Odd 0", lambda: mutual_recursion_even_odd(0)),
        ("Even/Odd 5", lambda: mutual_recursion_even_odd(5)),
        ("Even/Odd 100", lambda: mutual_recursion_even_odd(100)),
        
        # Tree traversal
        ("Tree depth 3", lambda: tree_traversal_count(3)),
        ("Tree depth 5", lambda: tree_traversal_count(5)),
        ("Tree depth 8", lambda: tree_traversal_count(8)),
        
        # Ackermann (small values only!)
        ("Ackermann(0,0)", lambda: ackermann(0, 0)),
        ("Ackermann(1,1)", lambda: ackermann(1, 1)),
        ("Ackermann(2,2)", lambda: ackermann(2, 2)),
        ("Ackermann(3,3)", lambda: ackermann(3, 3)),
        
        # Nested list
        ("Nested sum flat", lambda: sum_nested_list([1, 2, 3, 4, 5])),
        ("Nested sum 2-level", lambda: sum_nested_list([[1, 2], [3, 4], [5]])),
        ("Nested sum deep", lambda: sum_nested_list([1, [2, [3, [4, [5]]]]])),
        
        # GCD
        ("GCD(48, 18)", lambda: gcd_recursive(48, 18)),
        ("GCD(100, 1)", lambda: gcd_recursive(100, 1)),
        ("GCD(17, 23)", lambda: gcd_recursive(17, 23)),
    ]
    
    for name, test_fn in test_cases:
        start = time.time()
        result, ops = test_fn()
        elapsed = time.time() - start
        
        results['tests'].append({
            'name': name,
            'result': result,
            'operations': ops,
            'time': elapsed,
        })
    
    return results


def run_thiele_vm() -> Dict[str, Any]:
    """Run all recursion tests through Thiele VM."""
    from thielecpu.vm import VM
    from thielecpu.state import State
    from thielecpu.mu import question_cost_bits
    
    results = {'runtime': 'Thiele VM', 'tests': []}
    
    test_cases = [
        # Factorial
        ("Factorial 0", '''
calls = [0]
def fact(x):
    calls[0] = calls[0] + 1
    if x <= 1:
        return 1
    return x * fact(x - 1)
result = fact(0)
__result__ = (result, calls[0])
'''),
        ("Factorial 5", '''
calls = [0]
def fact(x):
    calls[0] = calls[0] + 1
    if x <= 1:
        return 1
    return x * fact(x - 1)
result = fact(5)
__result__ = (result, calls[0])
'''),
        ("Factorial 10", '''
calls = [0]
def fact(x):
    calls[0] = calls[0] + 1
    if x <= 1:
        return 1
    return x * fact(x - 1)
result = fact(10)
__result__ = (result, calls[0])
'''),
        # Fibonacci
        ("Fib naive 10", '''
calls = [0]
def fib(x):
    calls[0] = calls[0] + 1
    if x <= 1:
        return x
    return fib(x - 1) + fib(x - 2)
result = fib(10)
__result__ = (result, calls[0])
'''),
        ("Fib naive 15", '''
calls = [0]
def fib(x):
    calls[0] = calls[0] + 1
    if x <= 1:
        return x
    return fib(x - 1) + fib(x - 2)
result = fib(15)
__result__ = (result, calls[0])
'''),
        ("Fib memo 10", '''
calls = [0]
memo = {}
def fib(x):
    calls[0] = calls[0] + 1
    if x in memo:
        return memo[x]
    if x <= 1:
        res = x
    else:
        res = fib(x - 1) + fib(x - 2)
    memo[x] = res
    return res
result = fib(10)
__result__ = (result, calls[0])
'''),
        ("Fib memo 50", '''
calls = [0]
memo = {}
def fib(x):
    calls[0] = calls[0] + 1
    if x in memo:
        return memo[x]
    if x <= 1:
        res = x
    else:
        res = fib(x - 1) + fib(x - 2)
    memo[x] = res
    return res
result = fib(50)
__result__ = (result, calls[0])
'''),
        ("Fib memo 100", '''
calls = [0]
memo = {}
def fib(x):
    calls[0] = calls[0] + 1
    if x in memo:
        return memo[x]
    if x <= 1:
        res = x
    else:
        res = fib(x - 1) + fib(x - 2)
    memo[x] = res
    return res
result = fib(100)
__result__ = (result, calls[0])
'''),
        # Mutual recursion
        ("Even/Odd 0", '''
calls = [0]
def is_even(x):
    calls[0] = calls[0] + 1
    if x == 0:
        return True
    return is_odd(x - 1)
def is_odd(x):
    calls[0] = calls[0] + 1
    if x == 0:
        return False
    return is_even(x - 1)
result = is_even(0)
__result__ = (result, calls[0])
'''),
        ("Even/Odd 5", '''
calls = [0]
def is_even(x):
    calls[0] = calls[0] + 1
    if x == 0:
        return True
    return is_odd(x - 1)
def is_odd(x):
    calls[0] = calls[0] + 1
    if x == 0:
        return False
    return is_even(x - 1)
result = is_even(5)
__result__ = (result, calls[0])
'''),
        ("Even/Odd 100", '''
calls = [0]
def is_even(x):
    calls[0] = calls[0] + 1
    if x == 0:
        return True
    return is_odd(x - 1)
def is_odd(x):
    calls[0] = calls[0] + 1
    if x == 0:
        return False
    return is_even(x - 1)
result = is_even(100)
__result__ = (result, calls[0])
'''),
        # Tree traversal
        ("Tree depth 3", '''
calls = [0]
def traverse(d):
    calls[0] = calls[0] + 1
    if d == 0:
        return 1
    return 1 + traverse(d - 1) + traverse(d - 1)
result = traverse(3)
__result__ = (result, calls[0])
'''),
        ("Tree depth 5", '''
calls = [0]
def traverse(d):
    calls[0] = calls[0] + 1
    if d == 0:
        return 1
    return 1 + traverse(d - 1) + traverse(d - 1)
result = traverse(5)
__result__ = (result, calls[0])
'''),
        ("Tree depth 8", '''
calls = [0]
def traverse(d):
    calls[0] = calls[0] + 1
    if d == 0:
        return 1
    return 1 + traverse(d - 1) + traverse(d - 1)
result = traverse(8)
__result__ = (result, calls[0])
'''),
        # Ackermann
        ("Ackermann(0,0)", '''
calls = [0]
def ack(mm, nn):
    calls[0] = calls[0] + 1
    if mm == 0:
        return nn + 1
    if nn == 0:
        return ack(mm - 1, 1)
    return ack(mm - 1, ack(mm, nn - 1))
result = ack(0, 0)
__result__ = (result, calls[0])
'''),
        ("Ackermann(1,1)", '''
calls = [0]
def ack(mm, nn):
    calls[0] = calls[0] + 1
    if mm == 0:
        return nn + 1
    if nn == 0:
        return ack(mm - 1, 1)
    return ack(mm - 1, ack(mm, nn - 1))
result = ack(1, 1)
__result__ = (result, calls[0])
'''),
        ("Ackermann(2,2)", '''
calls = [0]
def ack(mm, nn):
    calls[0] = calls[0] + 1
    if mm == 0:
        return nn + 1
    if nn == 0:
        return ack(mm - 1, 1)
    return ack(mm - 1, ack(mm, nn - 1))
result = ack(2, 2)
__result__ = (result, calls[0])
'''),
        ("Ackermann(3,3)", '''
calls = [0]
def ack(mm, nn):
    calls[0] = calls[0] + 1
    if mm == 0:
        return nn + 1
    if nn == 0:
        return ack(mm - 1, 1)
    return ack(mm - 1, ack(mm, nn - 1))
result = ack(3, 3)
__result__ = (result, calls[0])
'''),
        # Nested list
        ("Nested sum flat", '''
calls = [0]
def sum_list(l):
    calls[0] = calls[0] + 1
    total = 0
    for item in l:
        if isinstance(item, list):
            total = total + sum_list(item)
        else:
            total = total + item
    return total
result = sum_list([1, 2, 3, 4, 5])
__result__ = (result, calls[0])
'''),
        ("Nested sum 2-level", '''
calls = [0]
def sum_list(l):
    calls[0] = calls[0] + 1
    total = 0
    for item in l:
        if isinstance(item, list):
            total = total + sum_list(item)
        else:
            total = total + item
    return total
result = sum_list([[1, 2], [3, 4], [5]])
__result__ = (result, calls[0])
'''),
        ("Nested sum deep", '''
calls = [0]
def sum_list(l):
    calls[0] = calls[0] + 1
    total = 0
    for item in l:
        if isinstance(item, list):
            total = total + sum_list(item)
        else:
            total = total + item
    return total
result = sum_list([1, [2, [3, [4, [5]]]]])
__result__ = (result, calls[0])
'''),
        # GCD
        ("GCD(48, 18)", '''
calls = [0]
def gcd(x, y):
    calls[0] = calls[0] + 1
    if y == 0:
        return x
    return gcd(y, x % y)
result = gcd(48, 18)
__result__ = (result, calls[0])
'''),
        ("GCD(100, 1)", '''
calls = [0]
def gcd(x, y):
    calls[0] = calls[0] + 1
    if y == 0:
        return x
    return gcd(y, x % y)
result = gcd(100, 1)
__result__ = (result, calls[0])
'''),
        ("GCD(17, 23)", '''
calls = [0]
def gcd(x, y):
    calls[0] = calls[0] + 1
    if y == 0:
        return x
    return gcd(y, x % y)
result = gcd(17, 23)
__result__ = (result, calls[0])
'''),
    ]
    
    for name, code in test_cases:
        vm = VM(State())
        start = time.time()
        res, _ = vm.execute_python(code)
        elapsed = time.time() - start
        
        result, ops = res if res else (None, 0)
        mu_cost = question_cost_bits(f"(recursion {name})") + ops * 0.1
        
        results['tests'].append({
            'name': name,
            'result': result,
            'operations': ops,
            'time': elapsed,
            'mu_cost': mu_cost,
        })
    
    return results


def compare_and_report() -> Dict[str, Any]:
    """Run both and compare results."""
    print("=" * 70)
    print("RECURSION PATTERNS")
    print("=" * 70)
    
    std_results = run_standard_python()
    vm_results = run_thiele_vm()
    
    all_match = True
    comparison_results = []
    
    print(f"\n{'Test Name':<25} {'Std Result':<15} {'VM Result':<15} {'Ops Match':<10}")
    print("-" * 70)
    
    for std_test, vm_test in zip(std_results['tests'], vm_results['tests']):
        result_match = std_test['result'] == vm_test['result']
        ops_match = std_test['operations'] == vm_test['operations']
        match = result_match and ops_match
        if not match:
            all_match = False
        
        std_res = str(std_test['result'])[:12]
        vm_res = str(vm_test['result'])[:12]
        status = "✓" if match else "✗"
        ops_status = "✓" if ops_match else "✗"
        
        print(f"{std_test['name']:<25} {std_res:<15} {vm_res:<15} {ops_status:<10}")
        
        comparison_results.append({
            'name': std_test['name'],
            'std_result': std_test['result'],
            'vm_result': vm_test['result'],
            'std_ops': std_test['operations'],
            'vm_ops': vm_test['operations'],
            'match': match,
            'mu_cost': vm_test.get('mu_cost', 0),
        })
    
    print("\n" + "-" * 70)
    print(f"ISOMORPHISM: {'✓ ALL TESTS PASS' if all_match else '✗ SOME TESTS FAILED'}")
    print(f"Total tests: {len(comparison_results)}")
    print(f"Matching: {sum(1 for r in comparison_results if r['match'])}")
    
    return {
        'category': 'Recursion Patterns',
        'all_match': all_match,
        'comparisons': comparison_results,
    }


if __name__ == "__main__":
    compare_and_report()
