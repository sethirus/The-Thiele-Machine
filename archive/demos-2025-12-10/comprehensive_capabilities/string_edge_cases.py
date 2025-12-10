#!/usr/bin/env python3
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.
"""
String Manipulation Edge Cases

Tests edge cases in string processing:
- Empty strings
- Unicode handling
- Very long strings
- Substring operations
- Pattern matching without regex
"""

import time
from typing import Dict, Any, List, Tuple


# =============================================================================
# STRING ALGORITHMS (identical in both environments)
# =============================================================================

def reverse_string(s: str) -> Tuple[str, int]:
    """Reverse a string character by character."""
    result = ""
    ops = 0
    for char in s:
        ops += 1
        result = char + result
    return result, ops


def palindrome_check(s: str) -> Tuple[bool, int]:
    """Check if string is palindrome."""
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
    """Count occurrences of pattern in text (naive O(n*m) algorithm)."""
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
    """Find longest common prefix of string list."""
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
    """Check if two strings are anagrams (using counting)."""
    if len(s1) != len(s2):
        return False, 0
    
    ops = 0
    counts = {}
    
    # Count characters in s1
    for char in s1:
        ops += 1
        counts[char] = counts.get(char, 0) + 1
    
    # Subtract characters in s2
    for char in s2:
        ops += 1
        if char not in counts or counts[char] == 0:
            return False, ops
        counts[char] -= 1
    
    return True, ops


# =============================================================================
# EDGE CASE TEST RUNNER
# =============================================================================

def run_standard_python() -> Dict[str, Any]:
    """Run all string tests with standard Python."""
    results = {'runtime': 'Standard Python', 'tests': []}
    
    # Test cases with edge cases
    test_cases = [
        # Empty strings
        ("Empty string reverse", lambda: reverse_string("")),
        ("Empty palindrome", lambda: palindrome_check("")),
        
        # Single character
        ("Single char reverse", lambda: reverse_string("x")),
        ("Single char palindrome", lambda: palindrome_check("x")),
        
        # Unicode
        ("Unicode reverse", lambda: reverse_string("héllo wörld")),
        ("Unicode palindrome", lambda: palindrome_check("日本日")),
        
        # Long strings
        ("Long string reverse", lambda: reverse_string("a" * 1000)),
        ("Long palindrome check", lambda: palindrome_check("a" * 1000)),
        
        # Pattern matching
        ("Substring count normal", lambda: count_substrings("abababa", "aba")),
        ("Substring count none", lambda: count_substrings("hello", "xyz")),
        ("Substring count empty pattern", lambda: count_substrings("hello", "")),
        
        # Prefix
        ("LCP normal", lambda: longest_common_prefix(["flower", "flow", "flight"])),
        ("LCP empty", lambda: longest_common_prefix([])),
        ("LCP single", lambda: longest_common_prefix(["alone"])),
        
        # Anagrams
        ("Anagram true", lambda: anagram_check("listen", "silent")),
        ("Anagram false", lambda: anagram_check("hello", "world")),
        ("Anagram empty", lambda: anagram_check("", "")),
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
    """Run all string tests through Thiele VM."""
    from thielecpu.vm import VM
    from thielecpu.state import State
    from thielecpu.mu import question_cost_bits
    
    results = {'runtime': 'Thiele VM', 'tests': []}
    
    test_cases = [
        # Empty strings
        ("Empty string reverse", '''
s = ""
result = ""
ops = 0
for char in s:
    ops = ops + 1
    result = char + result
__result__ = (result, ops)
'''),
        ("Empty palindrome", '''
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
'''),
        # Single character
        ("Single char reverse", '''
s = "x"
result = ""
ops = 0
for char in s:
    ops = ops + 1
    result = char + result
__result__ = (result, ops)
'''),
        ("Single char palindrome", '''
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
'''),
        # Unicode
        ("Unicode reverse", '''
s = "héllo wörld"
result = ""
ops = 0
for char in s:
    ops = ops + 1
    result = char + result
__result__ = (result, ops)
'''),
        ("Unicode palindrome", '''
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
'''),
        # Long strings
        ("Long string reverse", '''
s = "a" * 1000
result = ""
ops = 0
for char in s:
    ops = ops + 1
    result = char + result
__result__ = (result, ops)
'''),
        ("Long palindrome check", '''
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
'''),
        # Pattern matching
        ("Substring count normal", '''
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
'''),
        ("Substring count none", '''
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
'''),
        ("Substring count empty pattern", '''
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
'''),
        # Prefix
        ("LCP normal", '''
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
'''),
        ("LCP empty", '''
strings = []
prefix = ""
ops = 0
__result__ = (prefix, ops)
'''),
        ("LCP single", '''
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
'''),
        # Anagrams
        ("Anagram true", '''
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
'''),
        ("Anagram false", '''
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
'''),
        ("Anagram empty", '''
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
'''),
    ]
    
    for name, code in test_cases:
        vm = VM(State())
        start = time.time()
        res, _ = vm.execute_python(code)
        elapsed = time.time() - start
        
        result, ops = res if res else (None, 0)
        mu_cost = question_cost_bits(f"(string-op {name})") + ops * 0.05
        
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
    print("STRING MANIPULATION EDGE CASES")
    print("=" * 70)
    
    std_results = run_standard_python()
    vm_results = run_thiele_vm()
    
    all_match = True
    comparison_results = []
    
    print(f"\n{'Test Name':<30} {'Std Result':<15} {'VM Result':<15} {'Match':<6}")
    print("-" * 70)
    
    for std_test, vm_test in zip(std_results['tests'], vm_results['tests']):
        match = std_test['result'] == vm_test['result'] and std_test['operations'] == vm_test['operations']
        if not match:
            all_match = False
        
        std_res = str(std_test['result'])[:12]
        vm_res = str(vm_test['result'])[:12]
        status = "✓" if match else "✗"
        
        print(f"{std_test['name']:<30} {std_res:<15} {vm_res:<15} {status:<6}")
        
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
        'category': 'String Manipulation Edge Cases',
        'all_match': all_match,
        'comparisons': comparison_results,
    }


if __name__ == "__main__":
    compare_and_report()
