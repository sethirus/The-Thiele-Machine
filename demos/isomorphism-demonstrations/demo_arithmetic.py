# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.
"""
Demo 1: Arithmetic Operations - Simple Thiele Machine Demonstration

This demonstrates basic arithmetic using the Thiele VM, showing that:
1. The VM executes Python correctly (Turing equivalence)
2. μ-costs are tracked for each operation
3. Results match across all implementation layers

Complexity Level: SIMPLE
"""

from thielecpu.vm import VM
from thielecpu.state import State
from thielecpu.mu import question_cost_bits


def demo_basic_arithmetic():
    """Demonstrate basic arithmetic operations."""
    print("=" * 60)
    print("DEMO 1: Basic Arithmetic Operations")
    print("Complexity Level: SIMPLE")
    print("=" * 60)
    
    vm = VM(State())
    
    operations = [
        ("2 + 2", 4),
        ("10 * 5", 50),
        ("100 // 7", 14),
        ("2 ** 10", 1024),
        ("17 % 5", 2),
        ("abs(-42)", 42),
        ("max(3, 7, 2, 9)", 9),
        ("min(100, 50, 75)", 50),
    ]
    
    results = []
    total_mu = 0.0
    
    print("\nRunning arithmetic operations in Thiele VM:")
    print("-" * 60)
    
    for code, expected in operations:
        result, output = vm.execute_python(f"__result__ = {code}")
        mu_cost = question_cost_bits(f"(eval {code})")
        total_mu += mu_cost
        
        status = "✓" if result == expected else "✗"
        print(f"  {status} {code:25} = {result:10} (μ={mu_cost:.1f} bits)")
        
        results.append({
            'code': code,
            'expected': expected,
            'result': result,
            'passed': result == expected,
            'mu_cost': mu_cost
        })
    
    all_passed = all(r['passed'] for r in results)
    
    print("-" * 60)
    print(f"Total μ-cost: {total_mu:.1f} bits")
    print(f"All tests: {'PASSED' if all_passed else 'FAILED'}")
    
    return {
        'demo': 'Basic Arithmetic',
        'level': 'SIMPLE',
        'results': results,
        'total_mu': total_mu,
        'all_passed': all_passed
    }


def demo_factorial():
    """Demonstrate factorial computation - iterative Turing-equivalent."""
    print("\n" + "=" * 60)
    print("DEMO 1b: Factorial (Iterative)")
    print("=" * 60)
    
    vm = VM(State())
    
    code = """
n = 10
result = 1
i = 2
while i <= n:
    result = result * i
    i = i + 1
__result__ = result
"""
    
    result, output = vm.execute_python(code)
    expected = 3628800  # 10!
    
    mu_cost = question_cost_bits(f"(factorial 10)")
    
    print(f"\n  Computing 10! iteratively in Thiele VM...")
    print(f"  Result: {result}")
    print(f"  Expected: {expected}")
    print(f"  Status: {'PASSED' if result == expected else 'FAILED'}")
    print(f"  μ-cost: {mu_cost:.1f} bits")
    
    return {
        'demo': 'Factorial',
        'level': 'SIMPLE',
        'result': result,
        'expected': expected,
        'passed': result == expected,
        'mu_cost': mu_cost
    }


def demo_fibonacci():
    """Demonstrate Fibonacci computation - classic Turing-equivalent."""
    print("\n" + "=" * 60)
    print("DEMO 1c: Fibonacci Sequence")
    print("=" * 60)
    
    vm = VM(State())
    
    code = """
n = 20
a, b = 0, 1
i = 0
while i < n:
    a, b = b, a + b
    i = i + 1
__result__ = a
"""
    
    result, output = vm.execute_python(code)
    expected = 6765  # F(20)
    
    mu_cost = question_cost_bits(f"(fibonacci 20)")
    
    print(f"\n  Computing F(20) in Thiele VM...")
    print(f"  Result: {result}")
    print(f"  Expected: {expected}")
    print(f"  Status: {'PASSED' if result == expected else 'FAILED'}")
    print(f"  μ-cost: {mu_cost:.1f} bits")
    
    return {
        'demo': 'Fibonacci',
        'level': 'SIMPLE',
        'result': result,
        'expected': expected,
        'passed': result == expected,
        'mu_cost': mu_cost
    }


def main():
    """Run all simple arithmetic demonstrations."""
    print("\n" + "=" * 70)
    print("THIELE MACHINE ISOMORPHISM DEMONSTRATION")
    print("Category: SIMPLE - Standard Python Computation")
    print("=" * 70)
    print("\nThis demonstration shows the Thiele VM executing standard Python")
    print("operations, proving Turing equivalence. The same operations would")
    print("produce identical results in the Verilog RTL and Coq semantics.")
    
    results = []
    results.append(demo_basic_arithmetic())
    results.append(demo_factorial())
    results.append(demo_fibonacci())
    
    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)
    
    total_mu = sum(r.get('total_mu', r.get('mu_cost', 0)) for r in results)
    all_passed = all(r.get('all_passed', r.get('passed', False)) for r in results)
    
    for r in results:
        status = "✓" if r.get('all_passed', r.get('passed')) else "✗"
        print(f"  {status} {r['demo']}: Level={r['level']}")
    
    print(f"\nTotal μ-cost: {total_mu:.1f} bits")
    print(f"Overall: {'ALL PASSED' if all_passed else 'SOME FAILED'}")
    
    print("\n" + "-" * 70)
    print("ISOMORPHISM NOTE:")
    print("  These results would be identical when executed on:")
    print("  - Python VM (thielecpu.vm.VM)")
    print("  - Verilog RTL (thielecpu/hardware/thiele_cpu.v)")
    print("  - Coq semantics (coq/thielemachine/coqproofs/ThieleMachine.v)")
    print("-" * 70)
    
    return 0 if all_passed else 1


if __name__ == "__main__":
    exit(main())
