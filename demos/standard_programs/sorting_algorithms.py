"""Standard Program: Sorting Algorithms

Classic sorting algorithms that run in both Standard Python and the Thiele VM.
Used by pytest imports as part of the demo surface area.
"""

from __future__ import annotations

import math
import random
import time
from typing import Any, Dict, List, Tuple


def bubble_sort(arr: List[int]) -> Tuple[List[int], int]:
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
    comparisons = [0]

    def merge(left, right):
        result: List[int] = []
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


def run_standard_python(arr: List[int]) -> Dict[str, Any]:
    results: Dict[str, Any] = {"runtime": "Standard Python", "input_size": len(arr)}

    start = time.time()
    sorted_bubble, comps_bubble = bubble_sort(arr)
    results["bubble"] = {
        "sorted": sorted_bubble,
        "comparisons": comps_bubble,
        "time": time.time() - start,
        "correct": sorted_bubble == sorted(arr),
    }

    start = time.time()
    sorted_quick, comps_quick = quick_sort(arr)
    results["quick"] = {
        "sorted": sorted_quick,
        "comparisons": comps_quick,
        "time": time.time() - start,
        "correct": sorted_quick == sorted(arr),
    }

    start = time.time()
    sorted_merge, comps_merge = merge_sort(arr)
    results["merge"] = {
        "sorted": sorted_merge,
        "comparisons": comps_merge,
        "time": time.time() - start,
        "correct": sorted_merge == sorted(arr),
    }

    return results


def run_thiele_vm(arr: List[int]) -> Dict[str, Any]:
    from thielecpu.mu import question_cost_bits
    from thielecpu.state import State
    from thielecpu.vm import VM

    results: Dict[str, Any] = {"runtime": "Thiele VM", "input_size": len(arr)}
    arr_str = str(arr)
    n = len(arr)

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
    mu_bubble = question_cost_bits(f"(sort bubble {n})") + n * (n - 1) // 2 * 0.5
    results["bubble"] = {
        "sorted": res_bubble[0] if res_bubble else [],
        "comparisons": res_bubble[1] if res_bubble else 0,
        "time": time_bubble,
        "correct": res_bubble[0] == sorted(arr) if res_bubble else False,
        "mu_cost": mu_bubble,
    }

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
    mu_quick = question_cost_bits(f"(sort quick {n})") + n * math.log2(max(n, 1)) * 0.5
    results["quick"] = {
        "sorted": res_quick[0] if res_quick else [],
        "comparisons": res_quick[1] if res_quick else 0,
        "time": time_quick,
        "correct": res_quick[0] == sorted(arr) if res_quick else False,
        "mu_cost": mu_quick,
    }

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
    results["merge"] = {
        "sorted": res_merge[0] if res_merge else [],
        "comparisons": res_merge[1] if res_merge else 0,
        "time": time_merge,
        "correct": res_merge[0] == sorted(arr) if res_merge else False,
        "mu_cost": mu_merge,
    }

    return results


def compare_executions() -> bool:
    test_cases = [
        ("Small (10 elements)", [random.randint(1, 100) for _ in range(10)]),
        ("Medium (50 elements)", [random.randint(1, 1000) for _ in range(50)]),
        ("Sorted (20 elements)", list(range(20))),
        ("Reverse (20 elements)", list(range(20, 0, -1))),
    ]

    all_isomorphic = True
    for _, arr in test_cases:
        std_result = run_standard_python(arr)
        vm_result = run_thiele_vm(arr)
        for algo in ["bubble", "quick", "merge"]:
            std = std_result[algo]
            vm = vm_result[algo]
            if std["comparisons"] != vm["comparisons"] or std["sorted"] != vm["sorted"]:
                all_isomorphic = False
    return all_isomorphic


if __name__ == "__main__":
    random.seed(42)
    raise SystemExit(0 if compare_executions() else 1)
