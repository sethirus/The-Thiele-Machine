#!/usr/bin/env python3
"""Mathematical Edge Cases

Restored from the archived demo set.
"""

import time
from typing import Any, Dict, List, Tuple


def safe_multiply(a: int, b: int) -> Tuple[int, int]:
    return a * b, 1


def power_mod(base: int, exp: int, mod: int) -> Tuple[int, int]:
    result = 1
    ops = 0
    base = base % mod

    while exp > 0:
        ops += 1
        if exp % 2 == 1:
            result = (result * base) % mod
        exp = exp >> 1
        base = (base * base) % mod

    return result, ops


def prime_factors(n: int) -> Tuple[List[int], int]:
    factors: List[int] = []
    ops = 0
    d = 2

    while d * d <= n:
        ops += 1
        while n % d == 0:
            ops += 1
            factors.append(d)
            n //= d
        d += 1

    if n > 1:
        factors.append(n)

    return factors, ops


def gcd_extended(a: int, b: int) -> Tuple[Tuple[int, int, int], int]:
    ops = 0

    if b == 0:
        return (a, 1, 0), 1

    old_r, r = a, b
    old_s, s = 1, 0
    old_t, t = 0, 1

    while r != 0:
        ops += 1
        q = old_r // r
        old_r, r = r, old_r - q * r
        old_s, s = s, old_s - q * s
        old_t, t = t, old_t - q * t

    return (old_r, old_s, old_t), ops


def binomial(n: int, k: int) -> Tuple[int, int]:
    if k > n or k < 0:
        return 0, 0
    if k == 0 or k == n:
        return 1, 1

    ops = 0
    if k > n - k:
        k = n - k

    result = 1
    for i in range(k):
        ops += 1
        result = result * (n - i) // (i + 1)

    return result, ops


def integer_sqrt(n: int) -> Tuple[int, int]:
    if n < 0:
        return -1, 0
    if n == 0:
        return 0, 1

    ops = 0
    x = n
    y = (x + 1) // 2

    while y < x:
        ops += 1
        x = y
        y = (x + n // x) // 2

    return x, ops


def is_perfect_square(n: int) -> Tuple[bool, int]:
    if n < 0:
        return False, 0

    root, ops = integer_sqrt(n)
    return root * root == n, ops + 1


def fibonacci_matrix(n: int) -> Tuple[int, int]:
    ops = 0

    def matrix_mult(A, B):
        nonlocal ops
        ops += 1
        return [
            [A[0][0] * B[0][0] + A[0][1] * B[1][0], A[0][0] * B[0][1] + A[0][1] * B[1][1]],
            [A[1][0] * B[0][0] + A[1][1] * B[1][0], A[1][0] * B[0][1] + A[1][1] * B[1][1]],
        ]

    def matrix_pow(M, p):
        if p == 1:
            return M
        if p % 2 == 0:
            half = matrix_pow(M, p // 2)
            return matrix_mult(half, half)
        return matrix_mult(M, matrix_pow(M, p - 1))

    if n <= 0:
        return 0, 0
    if n == 1:
        return 1, 1

    base = [[1, 1], [1, 0]]
    result = matrix_pow(base, n - 1)
    return result[0][0], ops


def catalan(n: int) -> Tuple[int, int]:
    ops = 0
    if n <= 1:
        return 1, 1

    result, bin_ops = binomial(2 * n, n)
    ops += bin_ops
    return result // (n + 1), ops


def modular_inverse(a: int, mod: int) -> Tuple[int, int]:
    (g, x, _), ops = gcd_extended(a, mod)
    if g != 1:
        return -1, ops
    return x % mod, ops


def run_standard_python() -> Dict[str, Any]:
    results: Dict[str, Any] = {"runtime": "Standard Python", "tests": []}

    test_cases = [
        ("Multiply small", lambda: safe_multiply(123, 456)),
        ("Multiply large", lambda: safe_multiply(10**100, 10**100)),
        ("Multiply negative", lambda: safe_multiply(-999999, 888888)),
        ("PowerMod 2^10 mod 1000", lambda: power_mod(2, 10, 1000)),
        ("PowerMod 3^1000 mod 7", lambda: power_mod(3, 1000, 7)),
        ("PowerMod large", lambda: power_mod(123456789, 987654321, 1000000007)),
        ("Factor 12", lambda: prime_factors(12)),
        ("Factor 1001", lambda: prime_factors(1001)),
        ("Factor prime", lambda: prime_factors(997)),
        ("Factor power of 2", lambda: prime_factors(1024)),
        ("ExtGCD(48, 18)", lambda: gcd_extended(48, 18)),
        ("ExtGCD(35, 15)", lambda: gcd_extended(35, 15)),
        ("ExtGCD coprime", lambda: gcd_extended(17, 31)),
        ("C(10, 5)", lambda: binomial(10, 5)),
        ("C(20, 10)", lambda: binomial(20, 10)),
        ("C(100, 50)", lambda: binomial(100, 50)),
        ("C(5, 0)", lambda: binomial(5, 0)),
        ("C(5, 6)", lambda: binomial(5, 6)),
        ("isqrt(0)", lambda: integer_sqrt(0)),
        ("isqrt(1)", lambda: integer_sqrt(1)),
        ("isqrt(100)", lambda: integer_sqrt(100)),
        ("isqrt(1000000)", lambda: integer_sqrt(1000000)),
        ("isqrt(non-perfect)", lambda: integer_sqrt(99)),
        ("Perfect 16", lambda: is_perfect_square(16)),
        ("Perfect 17", lambda: is_perfect_square(17)),
        ("Perfect 0", lambda: is_perfect_square(0)),
        ("Perfect large", lambda: is_perfect_square(1000000)),
        ("Fib matrix 10", lambda: fibonacci_matrix(10)),
        ("Fib matrix 20", lambda: fibonacci_matrix(20)),
        ("Fib matrix 50", lambda: fibonacci_matrix(50)),
        ("Catalan 0", lambda: catalan(0)),
        ("Catalan 5", lambda: catalan(5)),
        ("Catalan 10", lambda: catalan(10)),
        ("ModInv(3, 7)", lambda: modular_inverse(3, 7)),
        ("ModInv(2, 5)", lambda: modular_inverse(2, 5)),
        ("ModInv no inverse", lambda: modular_inverse(6, 9)),
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
        # Multiply
        (
            "Multiply small",
            """
a, b = 123, 456
result = a * b
ops = 1
__result__ = (result, ops)
""",
        ),
        (
            "Multiply large",
            """
a = 10 ** 100
b = 10 ** 100
result = a * b
ops = 1
__result__ = (result, ops)
""",
        ),
        (
            "Multiply negative",
            """
a, b = -999999, 888888
result = a * b
ops = 1
__result__ = (result, ops)
""",
        ),
        # Power mod
        (
            "PowerMod 2^10 mod 1000",
            """
base, exp, mod = 2, 10, 1000
result = 1
ops = 0
base = base % mod
while exp > 0:
    ops = ops + 1
    if exp % 2 == 1:
        result = (result * base) % mod
    exp = exp >> 1
    base = (base * base) % mod
__result__ = (result, ops)
""",
        ),
        (
            "PowerMod 3^1000 mod 7",
            """
base, exp, mod = 3, 1000, 7
result = 1
ops = 0
base = base % mod
while exp > 0:
    ops = ops + 1
    if exp % 2 == 1:
        result = (result * base) % mod
    exp = exp >> 1
    base = (base * base) % mod
__result__ = (result, ops)
""",
        ),
        (
            "PowerMod large",
            """
base, exp, mod = 123456789, 987654321, 1000000007
result = 1
ops = 0
base = base % mod
while exp > 0:
    ops = ops + 1
    if exp % 2 == 1:
        result = (result * base) % mod
    exp = exp >> 1
    base = (base * base) % mod
__result__ = (result, ops)
""",
        ),
        # Prime factorization
        (
            "Factor 12",
            """
n = 12
factors = []
ops = 0
d = 2
while d * d <= n:
    ops = ops + 1
    while n % d == 0:
        ops = ops + 1
        factors.append(d)
        n = n // d
    d = d + 1
if n > 1:
    factors.append(n)
__result__ = (factors, ops)
""",
        ),
        (
            "Factor 1001",
            """
n = 1001
factors = []
ops = 0
d = 2
while d * d <= n:
    ops = ops + 1
    while n % d == 0:
        ops = ops + 1
        factors.append(d)
        n = n // d
    d = d + 1
if n > 1:
    factors.append(n)
__result__ = (factors, ops)
""",
        ),
        (
            "Factor prime",
            """
n = 997
factors = []
ops = 0
d = 2
while d * d <= n:
    ops = ops + 1
    while n % d == 0:
        ops = ops + 1
        factors.append(d)
        n = n // d
    d = d + 1
if n > 1:
    factors.append(n)
__result__ = (factors, ops)
""",
        ),
        (
            "Factor power of 2",
            """
n = 1024
factors = []
ops = 0
d = 2
while d * d <= n:
    ops = ops + 1
    while n % d == 0:
        ops = ops + 1
        factors.append(d)
        n = n // d
    d = d + 1
if n > 1:
    factors.append(n)
__result__ = (factors, ops)
""",
        ),
        # Extended GCD
        (
            "ExtGCD(48, 18)",
            """
a, b = 48, 18
ops = 0
old_r, r = a, b
old_s, s = 1, 0
old_t, t = 0, 1
while r != 0:
    ops = ops + 1
    q = old_r // r
    old_r, r = r, old_r - q * r
    old_s, s = s, old_s - q * s
    old_t, t = t, old_t - q * t
__result__ = ((old_r, old_s, old_t), ops)
""",
        ),
        (
            "ExtGCD(35, 15)",
            """
a, b = 35, 15
ops = 0
old_r, r = a, b
old_s, s = 1, 0
old_t, t = 0, 1
while r != 0:
    ops = ops + 1
    q = old_r // r
    old_r, r = r, old_r - q * r
    old_s, s = s, old_s - q * s
    old_t, t = t, old_t - q * t
__result__ = ((old_r, old_s, old_t), ops)
""",
        ),
        (
            "ExtGCD coprime",
            """
a, b = 17, 31
ops = 0
old_r, r = a, b
old_s, s = 1, 0
old_t, t = 0, 1
while r != 0:
    ops = ops + 1
    q = old_r // r
    old_r, r = r, old_r - q * r
    old_s, s = s, old_s - q * s
    old_t, t = t, old_t - q * t
__result__ = ((old_r, old_s, old_t), ops)
""",
        ),
        # Binomial
        (
            "C(10, 5)",
            """
n, k = 10, 5
ops = 0
if k > n or k < 0:
    result = 0
elif k == 0 or k == n:
    result = 1
    ops = 1
else:
    if k > n - k:
        k = n - k
    result = 1
    for i in range(k):
        ops = ops + 1
        result = result * (n - i) // (i + 1)
__result__ = (result, ops)
""",
        ),
        (
            "C(20, 10)",
            """
n, k = 20, 10
ops = 0
if k > n or k < 0:
    result = 0
elif k == 0 or k == n:
    result = 1
    ops = 1
else:
    if k > n - k:
        k = n - k
    result = 1
    for i in range(k):
        ops = ops + 1
        result = result * (n - i) // (i + 1)
__result__ = (result, ops)
""",
        ),
        (
            "C(100, 50)",
            """
n, k = 100, 50
ops = 0
if k > n or k < 0:
    result = 0
elif k == 0 or k == n:
    result = 1
    ops = 1
else:
    if k > n - k:
        k = n - k
    result = 1
    for i in range(k):
        ops = ops + 1
        result = result * (n - i) // (i + 1)
__result__ = (result, ops)
""",
        ),
        (
            "C(5, 0)",
            """
n, k = 5, 0
ops = 0
if k > n or k < 0:
    result = 0
elif k == 0 or k == n:
    result = 1
    ops = 1
else:
    if k > n - k:
        k = n - k
    result = 1
    for i in range(k):
        ops = ops + 1
        result = result * (n - i) // (i + 1)
__result__ = (result, ops)
""",
        ),
        (
            "C(5, 6)",
            """
n, k = 5, 6
ops = 0
if k > n or k < 0:
    result = 0
elif k == 0 or k == n:
    result = 1
    ops = 1
else:
    if k > n - k:
        k = n - k
    result = 1
    for i in range(k):
        ops = ops + 1
        result = result * (n - i) // (i + 1)
__result__ = (result, ops)
""",
        ),
        # Integer sqrt
        (
            "isqrt(0)",
            """
n = 0
if n == 0:
    result = 0
    ops = 1
else:
    ops = 0
    x = n
    y = (x + 1) // 2
    while y < x:
        ops = ops + 1
        x = y
        y = (x + n // x) // 2
    result = x
__result__ = (result, ops)
""",
        ),
        (
            "isqrt(1)",
            """
n = 1
if n == 0:
    result = 0
    ops = 1
else:
    ops = 0
    x = n
    y = (x + 1) // 2
    while y < x:
        ops = ops + 1
        x = y
        y = (x + n // x) // 2
    result = x
__result__ = (result, ops)
""",
        ),
        (
            "isqrt(100)",
            """
n = 100
if n == 0:
    result = 0
    ops = 1
else:
    ops = 0
    x = n
    y = (x + 1) // 2
    while y < x:
        ops = ops + 1
        x = y
        y = (x + n // x) // 2
    result = x
__result__ = (result, ops)
""",
        ),
        (
            "isqrt(1000000)",
            """
n = 1000000
if n == 0:
    result = 0
    ops = 1
else:
    ops = 0
    x = n
    y = (x + 1) // 2
    while y < x:
        ops = ops + 1
        x = y
        y = (x + n // x) // 2
    result = x
__result__ = (result, ops)
""",
        ),
        (
            "isqrt(non-perfect)",
            """
n = 99
if n == 0:
    result = 0
    ops = 1
else:
    ops = 0
    x = n
    y = (x + 1) // 2
    while y < x:
        ops = ops + 1
        x = y
        y = (x + n // x) // 2
    result = x
__result__ = (result, ops)
""",
        ),
        # Perfect square check
        (
            "Perfect 16",
            """
n = 16
if n == 0:
    root = 0
    ops = 1
else:
    ops = 0
    x = n
    y = (x + 1) // 2
    while y < x:
        ops = ops + 1
        x = y
        y = (x + n // x) // 2
    root = x
result = root * root == n
ops = ops + 1
__result__ = (result, ops)
""",
        ),
        (
            "Perfect 17",
            """
n = 17
if n == 0:
    root = 0
    ops = 1
else:
    ops = 0
    x = n
    y = (x + 1) // 2
    while y < x:
        ops = ops + 1
        x = y
        y = (x + n // x) // 2
    root = x
result = root * root == n
ops = ops + 1
__result__ = (result, ops)
""",
        ),
        (
            "Perfect 0",
            """
n = 0
if n == 0:
    root = 0
    ops = 1
else:
    ops = 0
    x = n
    y = (x + 1) // 2
    while y < x:
        ops = ops + 1
        x = y
        y = (x + n // x) // 2
    root = x
result = root * root == n
ops = ops + 1
__result__ = (result, ops)
""",
        ),
        (
            "Perfect large",
            """
n = 1000000
if n == 0:
    root = 0
    ops = 1
else:
    ops = 0
    x = n
    y = (x + 1) // 2
    while y < x:
        ops = ops + 1
        x = y
        y = (x + n // x) // 2
    root = x
result = root * root == n
ops = ops + 1
__result__ = (result, ops)
""",
        ),
        # Fibonacci matrix
        (
            "Fib matrix 10",
            """
n = 10
ops = [0]
def matrix_mult(A, B):
    ops[0] = ops[0] + 1
    return [
        [A[0][0] * B[0][0] + A[0][1] * B[1][0], A[0][0] * B[0][1] + A[0][1] * B[1][1]],
        [A[1][0] * B[0][0] + A[1][1] * B[1][0], A[1][0] * B[0][1] + A[1][1] * B[1][1]]
    ]
def matrix_pow(M, p):
    if p == 1:
        return M
    if p % 2 == 0:
        half = matrix_pow(M, p // 2)
        return matrix_mult(half, half)
    else:
        return matrix_mult(M, matrix_pow(M, p - 1))
if n <= 0:
    result = 0
elif n == 1:
    result = 1
    ops[0] = 1
else:
    base = [[1, 1], [1, 0]]
    res = matrix_pow(base, n - 1)
    result = res[0][0]
__result__ = (result, ops[0])
""",
        ),
        (
            "Fib matrix 20",
            """
n = 20
ops = [0]
def matrix_mult(A, B):
    ops[0] = ops[0] + 1
    return [
        [A[0][0] * B[0][0] + A[0][1] * B[1][0], A[0][0] * B[0][1] + A[0][1] * B[1][1]],
        [A[1][0] * B[0][0] + A[1][1] * B[1][0], A[1][0] * B[0][1] + A[1][1] * B[1][1]]
    ]
def matrix_pow(M, p):
    if p == 1:
        return M
    if p % 2 == 0:
        half = matrix_pow(M, p // 2)
        return matrix_mult(half, half)
    else:
        return matrix_mult(M, matrix_pow(M, p - 1))
if n <= 0:
    result = 0
elif n == 1:
    result = 1
    ops[0] = 1
else:
    base = [[1, 1], [1, 0]]
    res = matrix_pow(base, n - 1)
    result = res[0][0]
__result__ = (result, ops[0])
""",
        ),
        (
            "Fib matrix 50",
            """
n = 50
ops = [0]
def matrix_mult(A, B):
    ops[0] = ops[0] + 1
    return [
        [A[0][0] * B[0][0] + A[0][1] * B[1][0], A[0][0] * B[0][1] + A[0][1] * B[1][1]],
        [A[1][0] * B[0][0] + A[1][1] * B[1][0], A[1][0] * B[0][1] + A[1][1] * B[1][1]]
    ]
def matrix_pow(M, p):
    if p == 1:
        return M
    if p % 2 == 0:
        half = matrix_pow(M, p // 2)
        return matrix_mult(half, half)
    else:
        return matrix_mult(M, matrix_pow(M, p - 1))
if n <= 0:
    result = 0
elif n == 1:
    result = 1
    ops[0] = 1
else:
    base = [[1, 1], [1, 0]]
    res = matrix_pow(base, n - 1)
    result = res[0][0]
__result__ = (result, ops[0])
""",
        ),
        # Catalan
        (
            "Catalan 0",
            """
n = 0
if n <= 1:
    result = 1
    ops = 1
else:
    k = n
    nn = 2 * n
    ops = 0
    if k > nn - k:
        k = nn - k
    binom = 1
    for i in range(k):
        ops = ops + 1
        binom = binom * (nn - i) // (i + 1)
    result = binom // (n + 1)
__result__ = (result, ops)
""",
        ),
        (
            "Catalan 5",
            """
n = 5
if n <= 1:
    result = 1
    ops = 1
else:
    k = n
    nn = 2 * n
    ops = 0
    if k > nn - k:
        k = nn - k
    binom = 1
    for i in range(k):
        ops = ops + 1
        binom = binom * (nn - i) // (i + 1)
    result = binom // (n + 1)
__result__ = (result, ops)
""",
        ),
        (
            "Catalan 10",
            """
n = 10
if n <= 1:
    result = 1
    ops = 1
else:
    k = n
    nn = 2 * n
    ops = 0
    if k > nn - k:
        k = nn - k
    binom = 1
    for i in range(k):
        ops = ops + 1
        binom = binom * (nn - i) // (i + 1)
    result = binom // (n + 1)
__result__ = (result, ops)
""",
        ),
        # Modular inverse
        (
            "ModInv(3, 7)",
            """
a, mod = 3, 7
ops = 0
old_r, r = a, mod
old_s, s = 1, 0
while r != 0:
    ops = ops + 1
    q = old_r // r
    old_r, r = r, old_r - q * r
    old_s, s = s, old_s - q * s
if old_r != 1:
    result = -1
else:
    result = old_s % mod
__result__ = (result, ops)
""",
        ),
        (
            "ModInv(2, 5)",
            """
a, mod = 2, 5
ops = 0
old_r, r = a, mod
old_s, s = 1, 0
while r != 0:
    ops = ops + 1
    q = old_r // r
    old_r, r = r, old_r - q * r
    old_s, s = s, old_s - q * s
if old_r != 1:
    result = -1
else:
    result = old_s % mod
__result__ = (result, ops)
""",
        ),
        (
            "ModInv no inverse",
            """
a, mod = 6, 9
ops = 0
old_r, r = a, mod
old_s, s = 1, 0
while r != 0:
    ops = ops + 1
    q = old_r // r
    old_r, r = r, old_r - q * r
    old_s, s = s, old_s - q * s
if old_r != 1:
    result = -1
else:
    result = old_s % mod
__result__ = (result, ops)
""",
        ),
    ]

    for name, code in test_cases:
        vm = VM(State())
        start = time.time()
        res, _ = vm.execute_python(code)
        elapsed = time.time() - start
        value, ops = res if res else (None, 0)
        mu_cost = question_cost_bits(f"(math {name})") + ops * 0.1
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

    return {"category": "Mathematical Edge Cases", "all_match": all_match, "comparisons": comparisons}


if __name__ == "__main__":
    compare_and_report()
