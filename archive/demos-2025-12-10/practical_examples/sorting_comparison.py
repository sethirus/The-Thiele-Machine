#!/usr/bin/env python3
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.
"""
Practical Example: Sorting Comparison

Executes identical sorting algorithms in Standard Python and Thiele VM.
All conclusions are derived from measured results.

Run: python3 demos/practical_examples/sorting_comparison.py
"""

import time
import sys
import random
from pathlib import Path
from dataclasses import dataclass, field
from typing import Dict, Any, List

sys.path.insert(0, str(Path(__file__).parent.parent.parent))


@dataclass
class SortMeasurement:
    """Measured sorting result."""
    algorithm: str
    runtime: str
    input_size: int
    sorted_correctly: bool
    comparisons: int
    swaps: int
    time_seconds: float
    mu_cost: float = 0.0
    output_sample: List[int] = field(default_factory=list)


def bubble_sort_measured(arr: List[int]) -> tuple:
    """Bubble sort with measurements."""
    result = arr[:]
    comparisons = 0
    swaps = 0
    n = len(result)
    
    for i in range(n):
        for j in range(n - i - 1):
            comparisons += 1
            if result[j] > result[j + 1]:
                result[j], result[j + 1] = result[j + 1], result[j]
                swaps += 1
    
    return result, comparisons, swaps


def quick_sort_measured(arr: List[int]) -> tuple:
    """Quick sort with measurements."""
    comparisons = [0]
    swaps = [0]
    
    def partition(lst, low, high):
        pivot = lst[high]
        i = low - 1
        for j in range(low, high):
            comparisons[0] += 1
            if lst[j] <= pivot:
                i += 1
                lst[i], lst[j] = lst[j], lst[i]
                swaps[0] += 1
        lst[i + 1], lst[high] = lst[high], lst[i + 1]
        swaps[0] += 1
        return i + 1
    
    def quicksort(lst, low, high):
        if low < high:
            pi = partition(lst, low, high)
            quicksort(lst, low, pi - 1)
            quicksort(lst, pi + 1, high)
    
    result = arr[:]
    if len(result) > 1:
        quicksort(result, 0, len(result) - 1)
    
    return result, comparisons[0], swaps[0]


def merge_sort_measured(arr: List[int]) -> tuple:
    """Merge sort with measurements."""
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
    
    def mergesort(lst):
        if len(lst) <= 1:
            return lst
        mid = len(lst) // 2
        left = mergesort(lst[:mid])
        right = mergesort(lst[mid:])
        return merge(left, right)
    
    result = mergesort(arr)
    return result, comparisons[0], 0  # Merge sort doesn't swap in place


def measure_standard_python(arr: List[int]) -> List[SortMeasurement]:
    """Measure all sorting algorithms in standard Python."""
    expected = sorted(arr)
    results = []
    
    # Bubble sort
    start = time.time()
    bubble_result, bubble_comps, bubble_swaps = bubble_sort_measured(arr)
    bubble_time = time.time() - start
    results.append(SortMeasurement(
        algorithm="Bubble",
        runtime="Standard Python",
        input_size=len(arr),
        sorted_correctly=bubble_result == expected,
        comparisons=bubble_comps,
        swaps=bubble_swaps,
        time_seconds=bubble_time,
        output_sample=bubble_result[:5],
    ))
    
    # Quick sort
    start = time.time()
    quick_result, quick_comps, quick_swaps = quick_sort_measured(arr)
    quick_time = time.time() - start
    results.append(SortMeasurement(
        algorithm="Quick",
        runtime="Standard Python",
        input_size=len(arr),
        sorted_correctly=quick_result == expected,
        comparisons=quick_comps,
        swaps=quick_swaps,
        time_seconds=quick_time,
        output_sample=quick_result[:5],
    ))
    
    # Merge sort
    start = time.time()
    merge_result, merge_comps, merge_swaps = merge_sort_measured(arr)
    merge_time = time.time() - start
    results.append(SortMeasurement(
        algorithm="Merge",
        runtime="Standard Python",
        input_size=len(arr),
        sorted_correctly=merge_result == expected,
        comparisons=merge_comps,
        swaps=merge_swaps,
        time_seconds=merge_time,
        output_sample=merge_result[:5],
    ))
    
    return results


def measure_thiele_vm(arr: List[int]) -> List[SortMeasurement]:
    """Measure all sorting algorithms in Thiele VM."""
    from thielecpu.vm import VM
    from thielecpu.state import State
    from thielecpu.mu import question_cost_bits
    
    expected = sorted(arr)
    arr_str = str(arr)
    results = []
    
    # Bubble sort in VM
    vm = VM(State())
    bubble_code = f'''
arr = {arr_str}
result = arr[:]
comparisons = 0
swaps = 0
n = len(result)

for i in range(n):
    for j in range(n - i - 1):
        comparisons = comparisons + 1
        if result[j] > result[j + 1]:
            result[j], result[j + 1] = result[j + 1], result[j]
            swaps = swaps + 1

__result__ = (result, comparisons, swaps)
'''
    start = time.time()
    result, _ = vm.execute_python(bubble_code)
    bubble_time = time.time() - start
    bubble_result, bubble_comps, bubble_swaps = result if result else ([], 0, 0)
    mu_bubble = question_cost_bits(f"(sort-bubble {len(arr)})") + bubble_comps * 0.05
    
    results.append(SortMeasurement(
        algorithm="Bubble",
        runtime="Thiele VM",
        input_size=len(arr),
        sorted_correctly=bubble_result == expected,
        comparisons=bubble_comps,
        swaps=bubble_swaps,
        time_seconds=bubble_time,
        mu_cost=mu_bubble,
        output_sample=bubble_result[:5] if bubble_result else [],
    ))
    
    # Quick sort in VM
    vm2 = VM(State())
    quick_code = f'''
arr = {arr_str}
comparisons = [0]
swaps = [0]

def partition(lst, low, high):
    pivot = lst[high]
    i = low - 1
    for j in range(low, high):
        comparisons[0] = comparisons[0] + 1
        if lst[j] <= pivot:
            i = i + 1
            lst[i], lst[j] = lst[j], lst[i]
            swaps[0] = swaps[0] + 1
    lst[i + 1], lst[high] = lst[high], lst[i + 1]
    swaps[0] = swaps[0] + 1
    return i + 1

def quicksort(lst, low, high):
    if low < high:
        pi = partition(lst, low, high)
        quicksort(lst, low, pi - 1)
        quicksort(lst, pi + 1, high)

result = arr[:]
if len(result) > 1:
    quicksort(result, 0, len(result) - 1)

__result__ = (result, comparisons[0], swaps[0])
'''
    start = time.time()
    result, _ = vm2.execute_python(quick_code)
    quick_time = time.time() - start
    quick_result, quick_comps, quick_swaps = result if result else ([], 0, 0)
    mu_quick = question_cost_bits(f"(sort-quick {len(arr)})") + quick_comps * 0.05
    
    results.append(SortMeasurement(
        algorithm="Quick",
        runtime="Thiele VM",
        input_size=len(arr),
        sorted_correctly=quick_result == expected,
        comparisons=quick_comps,
        swaps=quick_swaps,
        time_seconds=quick_time,
        mu_cost=mu_quick,
        output_sample=quick_result[:5] if quick_result else [],
    ))
    
    # Merge sort in VM
    vm3 = VM(State())
    merge_code = f'''
arr = {arr_str}
comparisons = [0]

def merge(left, right):
    result = []
    i = 0
    j = 0
    while i < len(left) and j < len(right):
        comparisons[0] = comparisons[0] + 1
        if left[i] <= right[j]:
            result.append(left[i])
            i = i + 1
        else:
            result.append(right[j])
            j = j + 1
    result.extend(left[i:])
    result.extend(right[j:])
    return result

def mergesort(lst):
    if len(lst) <= 1:
        return lst
    mid = len(lst) // 2
    left = mergesort(lst[:mid])
    right = mergesort(lst[mid:])
    return merge(left, right)

result = mergesort(arr)
__result__ = (result, comparisons[0], 0)
'''
    start = time.time()
    result, _ = vm3.execute_python(merge_code)
    merge_time = time.time() - start
    merge_result, merge_comps, merge_swaps = result if result else ([], 0, 0)
    mu_merge = question_cost_bits(f"(sort-merge {len(arr)})") + merge_comps * 0.05
    
    results.append(SortMeasurement(
        algorithm="Merge",
        runtime="Thiele VM",
        input_size=len(arr),
        sorted_correctly=merge_result == expected,
        comparisons=merge_comps,
        swaps=merge_swaps,
        time_seconds=merge_time,
        mu_cost=mu_merge,
        output_sample=merge_result[:5] if merge_result else [],
    ))
    
    return results


def derive_conclusions(std: List[SortMeasurement], vm: List[SortMeasurement]) -> Dict[str, Any]:
    """Derive conclusions from measurements."""
    conclusions = {
        'isomorphism': [],
        'complexity_ratios': [],
        'mu_tracking': [],
    }
    
    # Check isomorphism
    for s, v in zip(std, vm):
        if s.algorithm == v.algorithm:
            comps_match = s.comparisons == v.comparisons
            correct_match = s.sorted_correctly == v.sorted_correctly
            conclusions['isomorphism'].append({
                'algorithm': s.algorithm,
                'comparisons_match': comps_match,
                'correctness_match': correct_match,
                'std_comps': s.comparisons,
                'vm_comps': v.comparisons,
                'std_correct': s.sorted_correctly,
                'vm_correct': v.sorted_correctly,
            })
            conclusions['mu_tracking'].append({
                'algorithm': v.algorithm,
                'mu_cost': v.mu_cost,
            })
    
    # Calculate complexity ratios
    if len(std) >= 2:
        bubble_comps = std[0].comparisons
        quick_comps = std[1].comparisons
        merge_comps = std[2].comparisons
        
        if quick_comps > 0:
            conclusions['complexity_ratios'].append({
                'comparison': 'Bubble/Quick',
                'ratio': bubble_comps / quick_comps,
                'bubble': bubble_comps,
                'quick': quick_comps,
            })
        if merge_comps > 0:
            conclusions['complexity_ratios'].append({
                'comparison': 'Bubble/Merge',
                'ratio': bubble_comps / merge_comps,
                'bubble': bubble_comps,
                'merge': merge_comps,
            })
    
    return conclusions


def print_results(arr_desc: str, std: List[SortMeasurement], vm: List[SortMeasurement], conclusions: Dict):
    """Print measured results and derived conclusions."""
    print(f"\n{'─' * 80}")
    print(f"Input: {arr_desc}")
    print(f"{'─' * 80}")
    
    print(f"\n  MEASURED RESULTS:")
    print(f"  {'Algo':<8} {'Runtime':<18} {'Correct':<8} {'Comparisons':<12} {'Swaps':<8} {'μ-cost':<10}")
    print(f"  {'-'*8} {'-'*18} {'-'*8} {'-'*12} {'-'*8} {'-'*10}")
    
    for r in std:
        print(f"  {r.algorithm:<8} {r.runtime:<18} {str(r.sorted_correctly):<8} {r.comparisons:<12} {r.swaps:<8} {'N/A':<10}")
    for r in vm:
        print(f"  {r.algorithm:<8} {r.runtime:<18} {str(r.sorted_correctly):<8} {r.comparisons:<12} {r.swaps:<8} {r.mu_cost:<10.1f}")
    
    print(f"\n  DERIVED CONCLUSIONS:")
    
    for iso in conclusions['isomorphism']:
        symbol = "✓" if iso['comparisons_match'] and iso['correctness_match'] else "✗"
        print(f"  {symbol} {iso['algorithm']}: comps_match={iso['comparisons_match']}, correct_match={iso['correctness_match']}")
        if not iso['comparisons_match']:
            print(f"    std_comps={iso['std_comps']}, vm_comps={iso['vm_comps']}")
    
    for ratio in conclusions['complexity_ratios']:
        print(f"  {ratio['comparison']}: {ratio['ratio']:.2f}x")


def main():
    print("=" * 80)
    print("SORTING COMPARISON: Standard Python vs Thiele VM")
    print("All conclusions derived from measurements")
    print("=" * 80)
    
    random.seed(42)
    
    test_cases = [
        ("Random 20 elements", [random.randint(1, 100) for _ in range(20)]),
        ("Random 50 elements", [random.randint(1, 100) for _ in range(50)]),
        ("Already sorted 30", list(range(30))),
        ("Reverse sorted 30", list(range(30, 0, -1))),
    ]
    
    all_iso_results = []
    
    for desc, arr in test_cases:
        std = measure_standard_python(arr)
        vm = measure_thiele_vm(arr)
        conclusions = derive_conclusions(std, vm)
        all_iso_results.extend(conclusions['isomorphism'])
        print_results(desc, std, vm, conclusions)
    
    # Summary
    print(f"\n{'=' * 80}")
    print("SUMMARY (derived from all measurements)")
    print(f"{'=' * 80}")
    
    total = len(all_iso_results)
    passed = sum(1 for r in all_iso_results if r['comparisons_match'] and r['correctness_match'])
    all_correct = sum(1 for r in all_iso_results if r['std_correct'] and r['vm_correct'])
    
    print(f"  Isomorphism checks: {passed}/{total} passed ({100*passed/total:.1f}%)")
    print(f"  Correctness: {all_correct}/{total} ({100*all_correct/total:.1f}%)")
    
    if passed == total:
        print(f"\n  DERIVED: Standard Python and Thiele VM produce identical comparison counts")
    else:
        print(f"\n  DERIVED: {total - passed} comparison count mismatches detected")


if __name__ == "__main__":
    main()
