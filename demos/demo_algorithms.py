#!/usr/bin/env python3
"""
Demo algorithms for μ-profiling
"""

def bubble_sort(arr):
    """Classic bubble sort - O(n²) time, but what about μ-cost?"""
    n = len(arr)
    for i in range(n):
        for j in range(0, n-i-1):
            if arr[j] > arr[j+1]:
                arr[j], arr[j+1] = arr[j+1], arr[j]
    return arr

def binary_search(arr, target):
    """Binary search - O(log n) time, low μ-cost"""
    left, right = 0, len(arr) - 1
    while left <= right:
        mid = (left + right) // 2
        if arr[mid] == target:
            return mid
        elif arr[mid] < target:
            left = mid + 1
        else:
            right = mid - 1
    return -1

def factorial_recursive(n):
    """Recursive factorial - elegant but high μ-cost"""
    if n <= 1:
        return 1
    return n * factorial_recursive(n - 1)

def factorial_iterative(n):
    """Iterative factorial - lower μ-cost"""
    result = 1
    for i in range(1, n + 1):
        result *= i
    return result

def matrix_multiply(a, b):
    """Matrix multiplication - O(n³) with high information cost"""
    result = [[0 for _ in range(len(b[0]))] for _ in range(len(a))]
    for i in range(len(a)):
        for j in range(len(b[0])):
            for k in range(len(b)):
                result[i][j] += a[i][k] * b[k][j]
    return result

if __name__ == "__main__":
    # Demo the algorithms
    print("Demo algorithms loaded. Use μ-profiler to analyze:")
    print("python tools/mu_profiler.py demo_algorithms.py")
    print("python tools/mu_profiler.py demo_algorithms.py --function bubble_sort")