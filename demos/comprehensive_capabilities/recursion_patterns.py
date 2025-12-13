#!/usr/bin/env python3
"""Recursion Patterns

Restored from the archived demo set.
"""

import time
from typing import Any, Dict, List, Tuple


def factorial_recursive(n: int) -> Tuple[int, int]:
    calls = [0]

    def fact(x):
        calls[0] += 1
        if x <= 1:
            return 1
        return x * fact(x - 1)

    return fact(n), calls[0]


def fibonacci_recursive(n: int) -> Tuple[int, int]:
    calls = [0]

    def fib(x):
        calls[0] += 1
        if x <= 1:
            return x
        return fib(x - 1) + fib(x - 2)

    return fib(n), calls[0]


def fibonacci_memoized(n: int) -> Tuple[int, int]:
    calls = [0]
    memo: Dict[int, int] = {}

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

    return fib(n), calls[0]


def mutual_recursion_even_odd(n: int) -> Tuple[bool, int]:
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

    return is_even(n), calls[0]


def tree_traversal_count(depth: int) -> Tuple[int, int]:
    calls = [0]

    def traverse(d):
        calls[0] += 1
        if d == 0:
            return 1
        return 1 + traverse(d - 1) + traverse(d - 1)

    return traverse(depth), calls[0]


def ackermann(m: int, n: int) -> Tuple[int, int]:
    calls = [0]

    def ack(mm, nn):
        calls[0] += 1
        if mm == 0:
            return nn + 1
        if nn == 0:
            return ack(mm - 1, 1)
        return ack(mm - 1, ack(mm, nn - 1))

    return ack(m, n), calls[0]


def sum_nested_list(lst: List) -> Tuple[int, int]:
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

    return sum_list(lst), calls[0]


def gcd_recursive(a: int, b: int) -> Tuple[int, int]:
    calls = [0]

    def gcd(x, y):
        calls[0] += 1
        if y == 0:
            return x
        return gcd(y, x % y)

    return gcd(a, b), calls[0]


def run_standard_python() -> Dict[str, Any]:
    results: Dict[str, Any] = {"runtime": "Standard Python", "tests": []}

    test_cases = [
        ("Factorial 0", lambda: factorial_recursive(0)),
        ("Factorial 5", lambda: factorial_recursive(5)),
        ("Factorial 10", lambda: factorial_recursive(10)),
        ("Fib naive 10", lambda: fibonacci_recursive(10)),
        ("Fib naive 15", lambda: fibonacci_recursive(15)),
        ("Fib memo 10", lambda: fibonacci_memoized(10)),
        ("Fib memo 50", lambda: fibonacci_memoized(50)),
        ("Fib memo 100", lambda: fibonacci_memoized(100)),
        ("Even/Odd 0", lambda: mutual_recursion_even_odd(0)),
        ("Even/Odd 5", lambda: mutual_recursion_even_odd(5)),
        ("Even/Odd 100", lambda: mutual_recursion_even_odd(100)),
        ("Tree depth 3", lambda: tree_traversal_count(3)),
        ("Tree depth 5", lambda: tree_traversal_count(5)),
        ("Tree depth 8", lambda: tree_traversal_count(8)),
        ("Ackermann(0,0)", lambda: ackermann(0, 0)),
        ("Ackermann(1,1)", lambda: ackermann(1, 1)),
        ("Ackermann(2,2)", lambda: ackermann(2, 2)),
        ("Ackermann(3,3)", lambda: ackermann(3, 3)),
        ("Nested sum flat", lambda: sum_nested_list([1, 2, 3, 4, 5])),
        ("Nested sum 2-level", lambda: sum_nested_list([[1, 2], [3, 4], [5]])),
        ("Nested sum deep", lambda: sum_nested_list([1, [2, [3, [4, [5]]]]])),
        ("GCD(48, 18)", lambda: gcd_recursive(48, 18)),
        ("GCD(100, 1)", lambda: gcd_recursive(100, 1)),
        ("GCD(17, 23)", lambda: gcd_recursive(17, 23)),
    ]

    for name, fn in test_cases:
        start = time.time()
        result, ops = fn()
        elapsed = time.time() - start
        results["tests"].append({"name": name, "result": result, "operations": ops, "time": elapsed})

    return results


def run_thiele_vm() -> Dict[str, Any]:
    from thielecpu.mu import question_cost_bits
    from thielecpu.state import State
    from thielecpu.vm import VM

    results: Dict[str, Any] = {"runtime": "Thiele VM", "tests": []}

    test_cases = [
        (
            "Factorial 0",
            """
calls = [0]
def fact(x):
    calls[0] = calls[0] + 1
    if x <= 1:
        return 1
    return x * fact(x - 1)
result = fact(0)
__result__ = (result, calls[0])
""",
        ),
        (
            "Factorial 5",
            """
calls = [0]
def fact(x):
    calls[0] = calls[0] + 1
    if x <= 1:
        return 1
    return x * fact(x - 1)
result = fact(5)
__result__ = (result, calls[0])
""",
        ),
        (
            "Factorial 10",
            """
calls = [0]
def fact(x):
    calls[0] = calls[0] + 1
    if x <= 1:
        return 1
    return x * fact(x - 1)
result = fact(10)
__result__ = (result, calls[0])
""",
        ),
        (
            "Fib naive 10",
            """
calls = [0]
def fib(x):
    calls[0] = calls[0] + 1
    if x <= 1:
        return x
    return fib(x - 1) + fib(x - 2)
result = fib(10)
__result__ = (result, calls[0])
""",
        ),
        (
            "Fib naive 15",
            """
calls = [0]
def fib(x):
    calls[0] = calls[0] + 1
    if x <= 1:
        return x
    return fib(x - 1) + fib(x - 2)
result = fib(15)
__result__ = (result, calls[0])
""",
        ),
        (
            "Fib memo 10",
            """
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
""",
        ),
        (
            "Fib memo 50",
            """
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
""",
        ),
        (
            "Fib memo 100",
            """
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
""",
        ),
        (
            "Even/Odd 0",
            """
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
""",
        ),
        (
            "Even/Odd 5",
            """
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
""",
        ),
        (
            "Even/Odd 100",
            """
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
""",
        ),
        (
            "Tree depth 3",
            """
calls = [0]
def traverse(d):
    calls[0] = calls[0] + 1
    if d == 0:
        return 1
    return 1 + traverse(d - 1) + traverse(d - 1)
result = traverse(3)
__result__ = (result, calls[0])
""",
        ),
        (
            "Tree depth 5",
            """
calls = [0]
def traverse(d):
    calls[0] = calls[0] + 1
    if d == 0:
        return 1
    return 1 + traverse(d - 1) + traverse(d - 1)
result = traverse(5)
__result__ = (result, calls[0])
""",
        ),
        (
            "Tree depth 8",
            """
calls = [0]
def traverse(d):
    calls[0] = calls[0] + 1
    if d == 0:
        return 1
    return 1 + traverse(d - 1) + traverse(d - 1)
result = traverse(8)
__result__ = (result, calls[0])
""",
        ),
        (
            "Ackermann(0,0)",
            """
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
""",
        ),
        (
            "Ackermann(1,1)",
            """
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
""",
        ),
        (
            "Ackermann(2,2)",
            """
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
""",
        ),
        (
            "Ackermann(3,3)",
            """
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
""",
        ),
        (
            "Nested sum flat",
            """
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
""",
        ),
        (
            "Nested sum 2-level",
            """
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
""",
        ),
        (
            "Nested sum deep",
            """
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
""",
        ),
        (
            "GCD(48, 18)",
            """
calls = [0]
def gcd(x, y):
    calls[0] = calls[0] + 1
    if y == 0:
        return x
    return gcd(y, x % y)
result = gcd(48, 18)
__result__ = (result, calls[0])
""",
        ),
        (
            "GCD(100, 1)",
            """
calls = [0]
def gcd(x, y):
    calls[0] = calls[0] + 1
    if y == 0:
        return x
    return gcd(y, x % y)
result = gcd(100, 1)
__result__ = (result, calls[0])
""",
        ),
        (
            "GCD(17, 23)",
            """
calls = [0]
def gcd(x, y):
    calls[0] = calls[0] + 1
    if y == 0:
        return x
    return gcd(y, x % y)
result = gcd(17, 23)
__result__ = (result, calls[0])
""",
        ),
    ]

    for name, code in test_cases:
        vm = VM(State())
        start = time.time()
        res, _ = vm.execute_python(code)
        elapsed = time.time() - start
        value, ops = res if res else (None, 0)
        mu_cost = question_cost_bits(f"(recursion {name})") + ops * 0.1
        results["tests"].append(
            {"name": name, "result": value, "operations": ops, "time": elapsed, "mu_cost": mu_cost}
        )

    return results


def compare_and_report() -> Dict[str, Any]:
    std_results = run_standard_python()
    vm_results = run_thiele_vm()

    all_match = True
    comparisons = []

    for std_test, vm_test in zip(std_results["tests"], vm_results["tests"]):
        match = std_test["result"] == vm_test["result"] and std_test["operations"] == vm_test["operations"]
        all_match = all_match and match
        comparisons.append(
            {
                "name": std_test["name"],
                "std_result": std_test["result"],
                "vm_result": vm_test["result"],
                "std_ops": std_test["operations"],
                "vm_ops": vm_test["operations"],
                "match": match,
                "mu_cost": vm_test.get("mu_cost", 0),
            }
        )

    return {"category": "Recursion Patterns", "all_match": all_match, "comparisons": comparisons}


if __name__ == "__main__":
    compare_and_report()
