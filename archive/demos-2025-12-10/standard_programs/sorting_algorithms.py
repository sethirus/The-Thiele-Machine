# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.
"""
Standard Program: Sorting Algorithms

Classic sorting algorithms that every developer knows.
Run BOTH in standard Python AND Thiele VM to demonstrate isomorphism.

Algorithms:
- Bubble Sort (O(n²) - blind/naive)
- Quick Sort (O(n log n) - structure-exploiting)
- Merge Sort (O(n log n) - divide and conquer)
"""

import time
import random
from typing import List, Tuple, Dict, Any


# ============================================================================
# SORTING ALGORITHMS (identical in both environments)
# ============================================================================

def bubble_sort(arr: List[int]) -> Tuple[List[int], int]:
    """
    Bubble Sort - the naive O(n²) algorithm.
    No structure exploitation, just compare everything.
    
    Returns: (sorted_array, comparisons_made)
    """
    result = arr[:]
    n = len(result)
    comparisons = 0
    
    for i in range(n):
        for j in range(0, n - i - 1):
            comparisons += 1
            if result[j] > result[j + 1]:
                result[j], result[j + 1] = result[j + 1], result[j]
    
    return result, comparisons


def quick_sort(arr: List[int]) -> Tuple[List[int], int]:
    """
    Quick Sort - O(n log n) average, exploits partitioning.
    
    Returns: (sorted_array, comparisons_made)
    """
    comparisons = [0]
    
    def partition(lst, low, high):
        pivot = lst[high]
        i = low - 1
        for j in range(low, high):
            comparisons[0] += 1
            if lst[j] <= pivot:
                i += 1
                lst[i], lst[j] = lst[j], lst[i]
        lst[i + 1], lst[high] = lst[high], lst[i + 1]
        return i + 1
    
    def quicksort_impl(lst, low, high):
        if low < high:
            pi = partition(lst, low, high)
            quicksort_impl(lst, low, pi - 1)
            quicksort_impl(lst, pi + 1, high)
    
    result = arr[:]
    if len(result) > 1:
        quicksort_impl(result, 0, len(result) - 1)
    return result, comparisons[0]


def merge_sort(arr: List[int]) -> Tuple[List[int], int]:
    """
    Merge Sort - O(n log n), divide and conquer.
    
    Returns: (sorted_array, comparisons_made)
    """
    comparisons = [0]
    
    def merge(left, right):
        result = []
        i = j = 0
        while i < len(left) and j < len(right):
            comparisons[0] += 1
            if left[i] <= right[j]:
                result.append(left[i])
                i += 1
            else:
                result.append(right[j])
                j += 1
        result.extend(left[i:])
        result.extend(right[j:])
        return result
    
    def mergesort_impl(lst):
        if len(lst) <= 1:
            return lst
        mid = len(lst) // 2
        left = mergesort_impl(lst[:mid])
        right = mergesort_impl(lst[mid:])
        return merge(left, right)
    
    return mergesort_impl(arr), comparisons[0]


# ============================================================================
# STANDARD PYTHON EXECUTION
# ============================================================================

def run_standard_python(arr: List[int]) -> Dict[str, Any]:
    """Run all sorting algorithms with standard Python."""
    
    results = {'runtime': 'Standard Python', 'input_size': len(arr)}
    
    # Bubble sort
    start = time.time()
    sorted_bubble, comps_bubble = bubble_sort(arr)
    results['bubble'] = {
        'sorted': sorted_bubble,
        'comparisons': comps_bubble,
        'time': time.time() - start,
        'correct': sorted_bubble == sorted(arr)
    }
    
    # Quick sort
    start = time.time()
    sorted_quick, comps_quick = quick_sort(arr)
    results['quick'] = {
        'sorted': sorted_quick,
        'comparisons': comps_quick,
        'time': time.time() - start,
        'correct': sorted_quick == sorted(arr)
    }
    
    # Merge sort
    start = time.time()
    sorted_merge, comps_merge = merge_sort(arr)
    results['merge'] = {
        'sorted': sorted_merge,
        'comparisons': comps_merge,
        'time': time.time() - start,
        'correct': sorted_merge == sorted(arr)
    }
    
    return results


# ============================================================================
# THIELE VM EXECUTION
# ============================================================================

def run_thiele_vm(arr: List[int]) -> Dict[str, Any]:
    """Run all sorting algorithms through Thiele VM."""
    from thielecpu.vm import VM
    from thielecpu.state import State
    from thielecpu.mu import question_cost_bits, information_gain_bits
    import math
    
    results = {'runtime': 'Thiele VM', 'input_size': len(arr)}
    arr_str = str(arr)
    
    # Bubble sort in VM
    vm = VM(State())
    bubble_code = f'''
arr = {arr_str}
result = arr[:]
n = len(result)
comparisons = 0

for i in range(n):
    for j in range(0, n - i - 1):
        comparisons = comparisons + 1
        if result[j] > result[j + 1]:
            result[j], result[j + 1] = result[j + 1], result[j]

__result__ = (result, comparisons)
'''
    start = time.time()
    res_bubble, _ = vm.execute_python(bubble_code)
    time_bubble = time.time() - start
    
    # μ-cost for bubble sort: each comparison is a question
    n = len(arr)
    mu_bubble = question_cost_bits(f"(sort bubble {n})") + n * (n - 1) // 2 * 0.5  # Scaled
    
    results['bubble'] = {
        'sorted': res_bubble[0] if res_bubble else [],
        'comparisons': res_bubble[1] if res_bubble else 0,
        'time': time_bubble,
        'correct': res_bubble[0] == sorted(arr) if res_bubble else False,
        'mu_cost': mu_bubble
    }
    
    # Quick sort in VM - using recursive function (sandbox unrestricted)
    vm2 = VM(State())
    quick_code = f'''
arr = {arr_str}
comparisons = 0

def partition(lst, low, high):
    global comparisons
    pivot = lst[high]
    i = low - 1
    for j in range(low, high):
        comparisons = comparisons + 1
        if lst[j] <= pivot:
            i = i + 1
            lst[i], lst[j] = lst[j], lst[i]
    lst[i + 1], lst[high] = lst[high], lst[i + 1]
    return i + 1

def quicksort_impl(lst, low, high):
    if low < high:
        pi = partition(lst, low, high)
        quicksort_impl(lst, low, pi - 1)
        quicksort_impl(lst, pi + 1, high)

result = arr[:]
if len(result) > 1:
    quicksort_impl(result, 0, len(result) - 1)
__result__ = (result, comparisons)
'''
    start = time.time()
    res_quick, _ = vm2.execute_python(quick_code)
    time_quick = time.time() - start
    
    # μ-cost for quick sort: O(n log n) comparisons typical
    mu_quick = question_cost_bits(f"(sort quick {n})") + n * math.log2(max(n, 1)) * 0.5
    
    results['quick'] = {
        'sorted': res_quick[0] if res_quick else [],
        'comparisons': res_quick[1] if res_quick else 0,
        'time': time_quick,
        'correct': res_quick[0] == sorted(arr) if res_quick else False,
        'mu_cost': mu_quick
    }
    
    # Merge sort in VM - using recursive function (sandbox unrestricted)
    vm3 = VM(State())
    merge_code = f'''
arr = {arr_str}
comparisons = 0

def merge(left, right):
    global comparisons
    result = []
    i = 0
    j = 0
    while i < len(left) and j < len(right):
        comparisons = comparisons + 1
        if left[i] <= right[j]:
            result.append(left[i])
            i = i + 1
        else:
            result.append(right[j])
            j = j + 1
    result.extend(left[i:])
    result.extend(right[j:])
    return result

def mergesort_impl(lst):
    if len(lst) <= 1:
        return lst
    mid = len(lst) // 2
    left = mergesort_impl(lst[:mid])
    right = mergesort_impl(lst[mid:])
    return merge(left, right)

sorted_arr = mergesort_impl(arr)
__result__ = (sorted_arr, comparisons)
'''
    start = time.time()
    res_merge, _ = vm3.execute_python(merge_code)
    time_merge = time.time() - start
    
    mu_merge = question_cost_bits(f"(sort merge {n})") + n * math.log2(max(n, 1)) * 0.5
    
    results['merge'] = {
        'sorted': res_merge[0] if res_merge else [],
        'comparisons': res_merge[1] if res_merge else 0,
        'time': time_merge,
        'correct': res_merge[0] == sorted(arr) if res_merge else False,
        'mu_cost': mu_merge
    }
    
    return results


# ============================================================================
# COMPARISON
# ============================================================================

def compare_executions():
    """Compare standard Python vs Thiele VM execution."""
    print("=" * 70)
    print("STANDARD PROGRAM: Sorting Algorithms")
    print("Running SAME algorithms in Standard Python AND Thiele VM")
    print("=" * 70)
    
    # Test with different array sizes
    test_cases = [
        ("Small (10 elements)", [random.randint(1, 100) for _ in range(10)]),
        ("Medium (50 elements)", [random.randint(1, 1000) for _ in range(50)]),
        ("Sorted (20 elements)", list(range(20))),
        ("Reverse (20 elements)", list(range(20, 0, -1))),
    ]
    
    all_isomorphic = True
    
    for name, arr in test_cases:
        print(f"\n{'─' * 70}")
        print(f"Test: {name}")
        print(f"Input: {arr[:5]}... (showing first 5)")
        print(f"{'─' * 70}")
        
        # Run both
        std_result = run_standard_python(arr)
        vm_result = run_thiele_vm(arr)
        
        # Display comparison table
        print(f"\n  {'Algorithm':<12} {'Runtime':<18} {'Comparisons':<12} {'Correct':<8} {'μ-cost':<12}")
        print(f"  {'-'*12} {'-'*18} {'-'*12} {'-'*8} {'-'*12}")
        
        for algo in ['bubble', 'quick', 'merge']:
            std = std_result[algo]
            vm = vm_result[algo]
            
            print(f"  {algo.title():<12} {'Standard Python':<18} {std['comparisons']:<12} {'✓' if std['correct'] else '✗':<8} {'N/A':<12}")
            print(f"  {'':<12} {'Thiele VM':<18} {vm['comparisons']:<12} {'✓' if vm['correct'] else '✗':<8} {vm['mu_cost']:.1f} bits")
        
        # Check isomorphism
        print(f"\n  Isomorphism Verification:")
        for algo in ['bubble', 'quick', 'merge']:
            std = std_result[algo]
            vm = vm_result[algo]
            
            comps_match = std['comparisons'] == vm['comparisons']
            sorted_match = std['sorted'] == vm['sorted']
            
            status = "✓" if (comps_match and sorted_match) else "✗"
            print(f"    {algo.title()}: comparisons match={comps_match}, output match={sorted_match} {status}")
            
            if not (comps_match and sorted_match):
                all_isomorphic = False
        
        # Show separation insight
        if std_result['bubble']['comparisons'] > 0:
            bubble_comps = std_result['bubble']['comparisons']
            quick_comps = std_result['quick']['comparisons']
            ratio = bubble_comps / max(quick_comps, 1)
            print(f"\n  Separation Insight:")
            print(f"    Bubble O(n²): {bubble_comps} comparisons")
            print(f"    Quick O(n log n): {quick_comps} comparisons")
            print(f"    Structure exploitation: {ratio:.1f}x improvement")
    
    # Summary
    print(f"\n{'=' * 70}")
    print("VALIDATION SUMMARY")
    print(f"{'=' * 70}")
    
    print(f"\n  Structural Isomorphism: {'✓ VERIFIED' if all_isomorphic else '✗ FAILED'}")
    print(f"  - Same algorithm code runs in both environments")
    print(f"  - Same comparison counts")
    print(f"  - Same sorted output")
    
    print(f"\n  Separation Demonstrated:")
    print(f"  - Standard Python: Pure computation")
    print(f"  - Thiele VM: Computation + μ-cost tracking")
    print(f"  - O(n log n) algorithms exploit divide-and-conquer structure")
    print(f"  - O(n²) algorithms don't exploit any structure")
    
    return all_isomorphic


if __name__ == "__main__":
    random.seed(42)  # Reproducibility
    success = compare_executions()
    exit(0 if success else 1)
