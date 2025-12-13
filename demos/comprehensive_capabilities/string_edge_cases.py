#!/usr/bin/env python3
"""String Manipulation Edge Cases

Restored from the archived demo set to satisfy tests that import
`demos.comprehensive_capabilities.*`.
"""

import time
from typing import Any, Dict, List, Tuple


def reverse_string(s: str) -> Tuple[str, int]:
    result = ""
    ops = 0
    for char in s:
        ops += 1
        result = char + result
    return result, ops


def palindrome_check(s: str) -> Tuple[bool, int]:
    ops = 0
    left, right = 0, len(s) - 1
    while left < right:
        ops += 1
        if s[left] != s[right]:
            return False, ops
        left += 1
        right -= 1
    return True, ops


def count_substrings(text: str, pattern: str) -> Tuple[int, int]:
    if not pattern:
        return 0, 0
    count = 0
    ops = 0
    for i in range(len(text) - len(pattern) + 1):
        match = True
        for j in range(len(pattern)):
            ops += 1
            if text[i + j] != pattern[j]:
                match = False
                break
        if match:
            count += 1
    return count, ops


def longest_common_prefix(strings: List[str]) -> Tuple[str, int]:
    if not strings:
        return "", 0
    ops = 0
    prefix = ""
    min_len = min(len(s) for s in strings)
    for i in range(min_len):
        char = strings[0][i]
        all_match = True
        for s in strings:
            ops += 1
            if s[i] != char:
                all_match = False
                break
        if all_match:
            prefix += char
        else:
            break
    return prefix, ops


def anagram_check(s1: str, s2: str) -> Tuple[bool, int]:
    if len(s1) != len(s2):
        return False, 0
    ops = 0
    counts: Dict[str, int] = {}
    for char in s1:
        ops += 1
        counts[char] = counts.get(char, 0) + 1
    for char in s2:
        ops += 1
        if char not in counts or counts[char] == 0:
            return False, ops
        counts[char] -= 1
    return True, ops


def run_standard_python() -> Dict[str, Any]:
    results: Dict[str, Any] = {"runtime": "Standard Python", "tests": []}
    test_cases = [
        ("Empty string reverse", lambda: reverse_string("")),
        ("Empty palindrome", lambda: palindrome_check("")),
        ("Single char reverse", lambda: reverse_string("x")),
        ("Single char palindrome", lambda: palindrome_check("x")),
        ("Unicode reverse", lambda: reverse_string("héllo wörld")),
        ("Unicode palindrome", lambda: palindrome_check("日本日")),
        ("Long string reverse", lambda: reverse_string("a" * 1000)),
        ("Long palindrome check", lambda: palindrome_check("a" * 1000)),
        ("Substring count normal", lambda: count_substrings("abababa", "aba")),
        ("Substring count none", lambda: count_substrings("hello", "xyz")),
        ("Substring count empty pattern", lambda: count_substrings("hello", "")),
        ("LCP normal", lambda: longest_common_prefix(["flower", "flow", "flight"])),
        ("LCP empty", lambda: longest_common_prefix([])),
        ("LCP single", lambda: longest_common_prefix(["alone"])),
        ("Anagram true", lambda: anagram_check("listen", "silent")),
        ("Anagram false", lambda: anagram_check("hello", "world")),
        ("Anagram empty", lambda: anagram_check("", "")),
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
            "Empty string reverse",
            """
s = ""
result = ""
ops = 0
for char in s:
    ops = ops + 1
    result = char + result
__result__ = (result, ops)
""",
        ),
        (
            "Empty palindrome",
            """
s = ""
ops = 0
left, right = 0, len(s) - 1
is_palindrome = True
while left < right:
    ops = ops + 1
    if s[left] != s[right]:
        is_palindrome = False
        break
    left = left + 1
    right = right - 1
__result__ = (is_palindrome, ops)
""",
        ),
        (
            "Single char reverse",
            """
s = "x"
result = ""
ops = 0
for char in s:
    ops = ops + 1
    result = char + result
__result__ = (result, ops)
""",
        ),
        (
            "Single char palindrome",
            """
s = "x"
ops = 0
left, right = 0, len(s) - 1
is_palindrome = True
while left < right:
    ops = ops + 1
    if s[left] != s[right]:
        is_palindrome = False
        break
    left = left + 1
    right = right - 1
__result__ = (is_palindrome, ops)
""",
        ),
        (
            "Unicode reverse",
            """
s = "héllo wörld"
result = ""
ops = 0
for char in s:
    ops = ops + 1
    result = char + result
__result__ = (result, ops)
""",
        ),
        (
            "Unicode palindrome",
            """
s = "日本日"
ops = 0
left, right = 0, len(s) - 1
is_palindrome = True
while left < right:
    ops = ops + 1
    if s[left] != s[right]:
        is_palindrome = False
        break
    left = left + 1
    right = right - 1
__result__ = (is_palindrome, ops)
""",
        ),
        (
            "Long string reverse",
            """
s = "a" * 1000
result = ""
ops = 0
for char in s:
    ops = ops + 1
    result = char + result
__result__ = (result, ops)
""",
        ),
        (
            "Long palindrome check",
            """
s = "a" * 1000
ops = 0
left, right = 0, len(s) - 1
is_palindrome = True
while left < right:
    ops = ops + 1
    if s[left] != s[right]:
        is_palindrome = False
        break
    left = left + 1
    right = right - 1
__result__ = (is_palindrome, ops)
""",
        ),
        (
            "Substring count normal",
            """
text = "abababa"
pattern = "aba"
count = 0
ops = 0
for i in range(len(text) - len(pattern) + 1):
    match = True
    for j in range(len(pattern)):
        ops = ops + 1
        if text[i + j] != pattern[j]:
            match = False
            break
    if match:
        count = count + 1
__result__ = (count, ops)
""",
        ),
        (
            "Substring count none",
            """
text = "hello"
pattern = "xyz"
count = 0
ops = 0
for i in range(len(text) - len(pattern) + 1):
    match = True
    for j in range(len(pattern)):
        ops = ops + 1
        if text[i + j] != pattern[j]:
            match = False
            break
    if match:
        count = count + 1
__result__ = (count, ops)
""",
        ),
        (
            "Substring count empty pattern",
            """
text = "hello"
pattern = ""
count = 0
ops = 0
if pattern:
    for i in range(len(text) - len(pattern) + 1):
        match = True
        for j in range(len(pattern)):
            ops = ops + 1
            if text[i + j] != pattern[j]:
                match = False
                break
        if match:
            count = count + 1
__result__ = (count, ops)
""",
        ),
        (
            "LCP normal",
            """
strings = ["flower", "flow", "flight"]
prefix = ""
ops = 0
if strings:
    min_len = min(len(s) for s in strings)
    for i in range(min_len):
        char = strings[0][i]
        all_match = True
        for s in strings:
            ops = ops + 1
            if s[i] != char:
                all_match = False
                break
        if all_match:
            prefix = prefix + char
        else:
            break
__result__ = (prefix, ops)
""",
        ),
        (
            "LCP empty",
            """
strings = []
prefix = ""
ops = 0
__result__ = (prefix, ops)
""",
        ),
        (
            "LCP single",
            """
strings = ["alone"]
prefix = ""
ops = 0
if strings:
    min_len = min(len(s) for s in strings)
    for i in range(min_len):
        char = strings[0][i]
        all_match = True
        for s in strings:
            ops = ops + 1
            if s[i] != char:
                all_match = False
                break
        if all_match:
            prefix = prefix + char
        else:
            break
__result__ = (prefix, ops)
""",
        ),
        (
            "Anagram true",
            """
s1, s2 = "listen", "silent"
is_anagram = True
ops = 0
if len(s1) != len(s2):
    is_anagram = False
else:
    counts = {}
    for char in s1:
        ops = ops + 1
        counts[char] = counts.get(char, 0) + 1
    for char in s2:
        ops = ops + 1
        if char not in counts or counts[char] == 0:
            is_anagram = False
            break
        counts[char] = counts[char] - 1
__result__ = (is_anagram, ops)
""",
        ),
        (
            "Anagram false",
            """
s1, s2 = "hello", "world"
is_anagram = True
ops = 0
if len(s1) != len(s2):
    is_anagram = False
else:
    counts = {}
    for char in s1:
        ops = ops + 1
        counts[char] = counts.get(char, 0) + 1
    for char in s2:
        ops = ops + 1
        if char not in counts or counts[char] == 0:
            is_anagram = False
            break
        counts[char] = counts[char] - 1
__result__ = (is_anagram, ops)
""",
        ),
        (
            "Anagram empty",
            """
s1, s2 = "", ""
is_anagram = True
ops = 0
if len(s1) != len(s2):
    is_anagram = False
else:
    counts = {}
    for char in s1:
        ops = ops + 1
        counts[char] = counts.get(char, 0) + 1
    for char in s2:
        ops = ops + 1
        if char not in counts or counts[char] == 0:
            is_anagram = False
            break
        counts[char] = counts[char] - 1
__result__ = (is_anagram, ops)
""",
        ),
    ]

    for name, code in test_cases:
        vm = VM(State())
        start = time.time()
        res, _ = vm.execute_python(code)
        elapsed = time.time() - start
        value, ops = res if res else (None, 0)
        mu_cost = question_cost_bits(f"(string-op {name})") + ops * 0.05
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

    return {"category": "String Manipulation Edge Cases", "all_match": all_match, "comparisons": comparisons}


if __name__ == "__main__":
    compare_and_report()
