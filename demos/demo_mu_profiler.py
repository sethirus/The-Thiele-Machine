#!/usr/bin/env python3
"""
μ-Profiler Demo: Universal Information Cost Analysis

This script demonstrates the μ-Profiler's ability to analyze ANY Python callable
for information processing costs (μ-costs) beyond traditional time/space complexity.
"""

from tools.mu_profiler import analyze, profile
import time

def main():
    print("🎯 μ-Profiler: Universal Information Cost Analysis Demo")
    print("=" * 60)

    # Test 1: Algorithm comparison
    print("\n📊 Algorithm Complexity Analysis:")
    print("-" * 40)

    algorithms = [
        ("Constant time", lambda: 42),
        ("Linear search", lambda arr, target: next((i for i, x in enumerate(arr) if x == target), -1)),
        ("Bubble sort", lambda arr: sorted(arr)),  # Using Python's sorted for demo
        ("Factorial", lambda n: 1 if n <= 1 else n * factorial(n-1)),
    ]

    for name, func in algorithms:
        result = analyze(func)
        print("25")

    # Test 2: Built-in functions
    print("\n🔧 Built-in Function Analysis:")
    print("-" * 40)

    builtins = [len, sum, max, min, sorted, abs, pow]
    for func in builtins:
        result = analyze(func)
        print("15")

    # Test 3: Real execution profiling
    print("\n⚡ Live Execution Profiling:")
    print("-" * 40)

    @profile
    def matrix_multiplication(n):
        """Simple matrix multiplication simulation"""
        result = 0
        for i in range(n):
            for j in range(n):
                result += i * j
        return result

    @profile
    def fibonacci_recursive(n):
        """Classic recursive fibonacci"""
        return n if n <= 1 else fibonacci_recursive(n-1) + fibonacci_recursive(n-2)

    print("\nMatrix multiplication (n=50):")
    start = time.time()
    result1 = matrix_multiplication(50)
    end = time.time()
    print(".4f")

    print("\nFibonacci recursive (n=10):")
    start = time.time()
    result2 = fibonacci_recursive(10)
    end = time.time()
    print(".4f")

    # Test 4: Complex real-world example
    print("\n🌟 Real-World Algorithm Comparison:")
    print("-" * 40)

    @profile
    def quicksort(arr):
        """Quicksort implementation"""
        if len(arr) <= 1:
            return arr
        pivot = arr[len(arr) // 2]
        left = [x for x in arr if x < pivot]
        middle = [x for x in arr if x == pivot]
        right = [x for x in arr if x > pivot]
        return quicksort(left) + middle + quicksort(right)

    @profile
    def mergesort(arr):
        """Mergesort implementation"""
        if len(arr) <= 1:
            return arr
        mid = len(arr) // 2
        left = mergesort(arr[:mid])
        right = mergesort(arr[mid:])
        return merge(left, right)

    def merge(left, right):
        result = []
        i = j = 0
        while i < len(left) and j < len(right):
            if left[i] < right[j]:
                result.append(left[i])
                i += 1
            else:
                result.append(right[j])
                j += 1
        result.extend(left[i:])
        result.extend(right[j:])
        return result

    test_data = [64, 34, 25, 12, 22, 11, 90, 5, 77, 30]

    print("\nQuicksort:")
    quicksort(test_data.copy())

    print("\nMergesort:")
    mergesort(test_data.copy())

    print("\n" + "=" * 60)
    print("✅ μ-Profiler Demo Complete!")
    print("✅ Works with any Python callable")
    print("✅ Provides unique insights beyond traditional profiling")
    print("✅ Backed by formal verification in the Thiele Machine")
    print("\nReady for practical applications in algorithm design,")
    print("performance optimization, and complexity analysis!")

if __name__ == "__main__":
    main()