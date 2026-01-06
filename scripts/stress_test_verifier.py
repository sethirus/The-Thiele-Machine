#!/usr/bin/env python3
"""
Thiele Machine Verification Stress Test

This script thoroughly tests the verification system to ensure it catches
all bad code and correctly verifies good code.

Run: python scripts/stress_test_verifier.py
"""

import ast
import json
import sys
import time
import traceback
from pathlib import Path
from dataclasses import dataclass
from typing import Optional, Callable
import urllib.request
import urllib.error

# Add repo root
REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from thielecpu.structural_verify import StructuralVerifier, VerificationCategory


@dataclass
class TestCase:
    """A single test case."""
    name: str
    input_text: str
    expected_verified: Optional[bool]  # True=should pass, False=should fail, None=should be unverifiable
    category: str
    description: str = ""


@dataclass  
class TestResult:
    """Result of running a test."""
    test: TestCase
    passed: bool
    actual_verified: Optional[bool]
    witness: str
    error: str
    time_ms: float


class VerificationStressTester:
    """Comprehensive stress tester for the verification system."""
    
    def __init__(self):
        self.verifier = StructuralVerifier()
        self.results: list[TestResult] = []
        self.server_url = "http://localhost:7331"
        
    def test_server_health(self) -> bool:
        """Check if verification server is running."""
        try:
            with urllib.request.urlopen(f"{self.server_url}/health", timeout=2) as resp:
                return resp.status == 200
        except:
            return False
    
    def run_test(self, test: TestCase) -> TestResult:
        """Run a single test case."""
        start = time.time()
        
        try:
            result = self.verifier.verify_text(test.input_text)
            elapsed_ms = (time.time() - start) * 1000
            
            # Find the relevant claim
            relevant_claims = [c for c in result.claims if c.category.value == test.category]
            
            if not relevant_claims:
                # No claims found - check if that's expected
                if test.expected_verified is None:
                    return TestResult(test, True, None, "No verifiable claims found (expected)", "", elapsed_ms)
                else:
                    return TestResult(test, False, None, "", f"No {test.category} claims extracted", elapsed_ms)
            
            claim = relevant_claims[0]
            actual = claim.verified
            
            # Check if result matches expectation
            if test.expected_verified is None:
                # Expected unverifiable
                passed = actual is None
            else:
                passed = actual == test.expected_verified
            
            witness = claim.witness or ""
            error = claim.error or ""
            
            return TestResult(test, passed, actual, witness, error, elapsed_ms)
            
        except Exception as e:
            elapsed_ms = (time.time() - start) * 1000
            return TestResult(test, False, None, "", f"Exception: {e}", elapsed_ms)
    
    def run_all_tests(self, tests: list[TestCase]) -> list[TestResult]:
        """Run all test cases."""
        self.results = []
        for test in tests:
            result = self.run_test(test)
            self.results.append(result)
        return self.results
    
    def print_results(self):
        """Print test results in a nice format."""
        passed = sum(1 for r in self.results if r.passed)
        failed = sum(1 for r in self.results if not r.passed)
        total = len(self.results)
        
        print("\n" + "=" * 70)
        print("THIELE MACHINE VERIFICATION STRESS TEST RESULTS")
        print("=" * 70)
        print(f"\n✓ Passed: {passed}/{total}  ✗ Failed: {failed}/{total}")
        print(f"Total time: {sum(r.time_ms for r in self.results):.1f}ms")
        print()
        
        # Group by category
        categories = {}
        for r in self.results:
            cat = r.test.category
            if cat not in categories:
                categories[cat] = []
            categories[cat].append(r)
        
        for cat, results in categories.items():
            cat_passed = sum(1 for r in results if r.passed)
            print(f"\n{'─' * 70}")
            print(f"📁 {cat.upper()} ({cat_passed}/{len(results)} passed)")
            print(f"{'─' * 70}")
            
            for r in results:
                icon = "✓" if r.passed else "✗"
                status = "PASS" if r.passed else "FAIL"
                expected = "✓" if r.test.expected_verified else ("✗" if r.test.expected_verified is False else "?")
                actual = "✓" if r.actual_verified else ("✗" if r.actual_verified is False else "?")
                
                print(f"\n  {icon} [{status}] {r.test.name}")
                print(f"    Expected: {expected}  Actual: {actual}  Time: {r.time_ms:.1f}ms")
                
                if r.witness:
                    print(f"    Witness: {r.witness[:60]}{'...' if len(r.witness) > 60 else ''}")
                if r.error:
                    print(f"    Error: {r.error[:60]}{'...' if len(r.error) > 60 else ''}")
                if not r.passed:
                    print(f"    Input: {r.test.input_text[:50]}{'...' if len(r.test.input_text) > 50 else ''}")
        
        # Summary of failures
        failures = [r for r in self.results if not r.passed]
        if failures:
            print(f"\n{'=' * 70}")
            print(f"⚠️  {len(failures)} FAILURES NEED ATTENTION:")
            print("=" * 70)
            for r in failures:
                print(f"  - {r.test.name}: {r.error or 'Unexpected result'}")
        
        return failed == 0


# =============================================================================
# TEST CASES
# =============================================================================

CODE_TESTS = [
    # Valid Python code
    TestCase("simple_function", "```python\ndef hello():\n    return 42\n```", True, "code_syntax", "Basic function"),
    TestCase("class_definition", "```python\nclass Foo:\n    def bar(self): pass\n```", True, "code_syntax", "Class with method"),
    TestCase("list_comprehension", "```python\nx = [i*2 for i in range(10)]\n```", True, "code_syntax", "List comprehension"),
    TestCase("async_function", "```python\nasync def fetch():\n    await something()\n```", True, "code_syntax", "Async function"),
    TestCase("type_hints", "```python\ndef add(a: int, b: int) -> int:\n    return a + b\n```", True, "code_syntax", "Type hints"),
    TestCase("decorator", "```python\n@property\ndef name(self):\n    return self._name\n```", True, "code_syntax", "Decorator"),
    TestCase("multiline_string", '```python\nx = """multi\nline\nstring"""\n```', True, "code_syntax", "Multiline string"),
    TestCase("lambda", "```python\nf = lambda x: x * 2\n```", True, "code_syntax", "Lambda"),
    TestCase("with_statement", "```python\nwith open('f') as f:\n    data = f.read()\n```", True, "code_syntax", "Context manager"),
    TestCase("match_statement", "```python\nmatch x:\n    case 1: pass\n    case _: pass\n```", True, "code_syntax", "Match statement (Python 3.10+)"),
    
    # Invalid Python code - MUST FAIL
    TestCase("missing_colon", "```python\ndef hello()\n    return 42\n```", False, "code_syntax", "Missing colon after def"),
    TestCase("unclosed_paren", "```python\ndef hello(\n    return 42\n```", False, "code_syntax", "Unclosed parenthesis"),
    TestCase("bad_indent", "```python\ndef hello():\nreturn 42\n```", False, "code_syntax", "Bad indentation"),
    TestCase("invalid_syntax", "```python\nif x = 5:\n    pass\n```", False, "code_syntax", "Assignment in condition"),
    TestCase("unclosed_string", "```python\nx = 'hello\n```", False, "code_syntax", "Unclosed string"),
    TestCase("invalid_decorator", "```python\n@\ndef foo(): pass\n```", False, "code_syntax", "Empty decorator"),
    TestCase("mismatched_brackets", "```python\nx = [1, 2, 3}\n```", False, "code_syntax", "Mismatched brackets"),
    TestCase("double_colon", "```python\ndef foo():: pass\n```", False, "code_syntax", "Double colon"),
    TestCase("invalid_import", "```python\nimport .foo\n```", False, "code_syntax", "Invalid relative import"),
    TestCase("break_outside_loop", "```python\nbreak\n```", True, "code_syntax", "Break alone (syntax valid, semantic error)"),
]

MATH_TESTS = [
    # Correct math
    TestCase("simple_add", "2 + 2 = 4", True, "mathematical", "Simple addition"),
    TestCase("simple_mult", "3 * 5 = 15", True, "mathematical", "Simple multiplication"),
    TestCase("factorization", "15 = 3 × 5", True, "mathematical", "Factorization with ×"),
    TestCase("factorization_star", "15 = 3 * 5", True, "mathematical", "Factorization with *"),
    TestCase("large_mult", "144 = 12 * 12", True, "mathematical", "Larger multiplication"),
    TestCase("subtraction", "10 - 3 = 7", True, "mathematical", "Subtraction"),
    TestCase("division", "20 / 4 = 5", True, "mathematical", "Division"),
    TestCase("power", "2^3 = 8", True, "mathematical", "Power"),
    TestCase("comparison_gt", "10 > 5", True, "mathematical", "Greater than"),
    TestCase("comparison_lt", "3 < 7", True, "mathematical", "Less than"),
    
    # Incorrect math - MUST FAIL
    TestCase("wrong_add", "2 + 2 = 5", False, "mathematical", "Wrong addition"),
    TestCase("wrong_mult", "3 * 5 = 16", False, "mathematical", "Wrong multiplication"),
    TestCase("wrong_factor", "15 = 3 × 6", False, "mathematical", "Wrong factorization"),
    TestCase("wrong_sub", "10 - 3 = 8", False, "mathematical", "Wrong subtraction"),
    TestCase("wrong_compare_gt", "5 > 10", False, "mathematical", "Wrong greater than"),
    TestCase("wrong_compare_lt", "7 < 3", False, "mathematical", "Wrong less than"),
]

FILE_TESTS = [
    # Files that exist
    TestCase("vm_exists", "Check `thielecpu/vm.py`", True, "file_system", "VM file exists"),
    TestCase("readme_exists", "See `README.md`", True, "file_system", "README exists"),
    TestCase("init_exists", "The `thielecpu/__init__.py` file", True, "file_system", "Init file exists"),
    
    # Files that don't exist - MUST FAIL
    TestCase("fake_file", "Check `nonexistent_file_xyz.py`", False, "file_system", "Fake file"),
    TestCase("fake_module", "See `fake_module/fake.py`", False, "file_system", "Fake module"),
    TestCase("typo_file", "The `thielcpu/vm.py` file", False, "file_system", "Typo in path"),
]

IMPORT_TESTS = [
    # Valid imports
    TestCase("import_json", "`import json`", True, "import", "Standard library"),
    TestCase("import_os", "`import os`", True, "import", "OS module"),
    TestCase("import_sys", "`import sys`", True, "import", "Sys module"),
    TestCase("import_ast", "`import ast`", True, "import", "AST module"),
    TestCase("import_re", "`import re`", True, "import", "Regex module"),
    TestCase("import_pathlib", "`from pathlib import Path`", True, "import", "Pathlib"),
    
    # Invalid imports - MUST FAIL
    TestCase("fake_import", "`import nonexistent_module_xyz`", False, "import", "Fake module"),
    TestCase("typo_import", "`import jsn`", False, "import", "Typo in module"),
    TestCase("fake_from", "`from fake_pkg import thing`", False, "import", "Fake package"),
]

FACTUAL_TESTS = [
    # Factual claims - should be marked as requiring oracle (None)
    TestCase("capital_france", "The capital of France is Paris", None, "factual_world", "Capital city"),
    TestCase("earth_round", "The Earth is round", None, "factual_world", "Shape of Earth"),
    TestCase("python_creator", "Guido van Rossum created Python", None, "factual_world", "Invention claim"),
]

OPINION_TESTS = [
    # Opinions - should be unverifiable (None)
    TestCase("best_language", "I think Python is the best language", None, "opinion", "Language opinion"),
    TestCase("preference", "I believe functional programming is better", None, "opinion", "Paradigm preference"),
]

# Additional edge case tests
EDGE_CASE_TESTS = [
    # Nested imports
    TestCase("nested_import", "`import os.path`", True, "import", "Nested module import"),
    TestCase("from_nested", "`from collections.abc import Mapping`", True, "import", "From nested import"),
    
    # Edge case math  
    TestCase("zero_mult", "0 * 100 = 0", True, "mathematical", "Zero multiplication"),
    TestCase("negative_result", "5 - 10 = -5", True, "mathematical", "Negative result"),
    TestCase("float_div", "7 / 2 = 3.5", True, "mathematical", "Float division"),
    
    # Complex code
    TestCase("nested_class", "```python\nclass A:\n    class B:\n        pass\n```", True, "code_syntax", "Nested class"),
    TestCase("walrus", "```python\nif (n := len(a)) > 10:\n    print(n)\n```", True, "code_syntax", "Walrus operator"),
    TestCase("fstring_expr", "```python\nx = f'{1+1=}'\n```", True, "code_syntax", "f-string with expression"),
    
    # Tricky invalid code
    TestCase("async_no_await", "```python\nasync def f(): return 42\n```", True, "code_syntax", "Async without await (valid)"),
    TestCase("return_outside", "```python\nreturn 42\n```", True, "code_syntax", "Return outside func (syntax valid)"),
    
    # Empty/whitespace
    TestCase("empty_code", "```python\n```", True, "code_syntax", "Empty code block (valid)"),
    TestCase("just_pass", "```python\npass\n```", True, "code_syntax", "Just pass statement"),
]


def main():
    """Run the stress test."""
    print("╔════════════════════════════════════════════════════════════════╗")
    print("║     THIELE MACHINE VERIFICATION STRESS TEST                   ║")
    print("╚════════════════════════════════════════════════════════════════╝")
    print()
    
    tester = VerificationStressTester()
    
    # Check server
    if tester.test_server_health():
        print("✓ Verification server is running")
    else:
        print("⚠ Verification server not running (using direct verification)")
    
    # Collect all tests
    all_tests = CODE_TESTS + MATH_TESTS + FILE_TESTS + IMPORT_TESTS + FACTUAL_TESTS + OPINION_TESTS + EDGE_CASE_TESTS
    
    print(f"\nRunning {len(all_tests)} test cases...")
    print()
    
    # Run tests
    tester.run_all_tests(all_tests)
    
    # Print results
    all_passed = tester.print_results()
    
    # Return exit code
    return 0 if all_passed else 1


if __name__ == "__main__":
    sys.exit(main())
