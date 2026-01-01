#!/usr/bin/env python3
"""Compare Thiele period-oracle factorization vs classical baselines.

Writes CSV to artifacts/factor_compare.csv with columns:
n,method,success,wall_time,details
"""

from __future__ import annotations

import csv
import math
import random
import time
from pathlib import Path
from typing import List, Tuple

REPO_ROOT = Path(__file__).resolve().parents[2]
import sys
sys.path.insert(0, str(REPO_ROOT))

from thielecpu.shor_oracle import find_period_with_claims


def trial_division(n: int) -> List[int]:
    factors = []
    d = 2
    while d * d <= n:
        while n % d == 0:
            factors.append(d)
            n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        factors.append(n)
    return factors


def pollards_rho(n: int, seed: int = 1) -> List[int]:
    if n % 2 == 0:
        return [2] + pollards_rho(n // 2, seed)
    if n == 1:
        return []
    if is_prime(n:=int(n)):
        return [n]

    def rho(n):
        random.seed(seed)
        if n % 2 == 0:
            return 2
        x = random.randrange(2, n - 1)
        y = x
        c = random.randrange(1, n - 1)
        d = 1
        while d == 1:
            x = (x * x + c) % n
            y = (y * y + c) % n
            y = (y * y + c) % n
            d = math.gcd(abs(x - y), n)
            if d == n:
                return rho(n)
        return d

    factor = rho(n)
    if factor == n:
        return [n]
    left = pollards_rho(factor, seed + 1)
    right = pollards_rho(n // factor, seed + 2)
    return left + right


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    r = int(math.isqrt(n))
    for i in range(3, r + 1, 2):
        if n % i == 0:
            return False
    return True


def shor_reduce(n: int, a: int, period: int) -> List[int]:
    if period % 2 != 0:
        return []
    half = period // 2
    term = pow(a, half, n)
    if term in (1, n - 1):
        return []
    f1 = math.gcd(term - 1, n)
    f2 = math.gcd(term + 1, n)
    res = []
    for f in (f1, f2):
        if 1 < f < n and f not in res:
            res.append(f)
    return res


def run(ns: List[int], out: Path) -> None:
    out.parent.mkdir(parents=True, exist_ok=True)
    with out.open("w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["n", "method", "success", "wall_time", "details"])
        for n in ns:
            # Thiele
            a = 2
            t0 = time.time()
            try:
                res = find_period_with_claims(n, a, max_period=2 * n)
                period = res.period
                facts = shor_reduce(n, a, period)
                success = len(facts) >= 2
                details = f"period={period},mu={res.mu_cost},queries={res.solver_queries},factors={facts}"
            except Exception as e:
                success = False
                details = f"error:{e}"
            wall = time.time() - t0
            w.writerow([n, "thiele", success, f"{wall:.6f}", details])

            # Pollard's Rho
            t0 = time.time()
            try:
                factors = pollards_rho(n)
                success = len(factors) >= 2
                details = f"factors={factors}"
            except Exception as e:
                success = False
                details = f"error:{e}"
            wall = time.time() - t0
            w.writerow([n, "pollard_rho", success, f"{wall:.6f}", details])

            # Trial division (fast for small N)
            t0 = time.time()
            try:
                factors = trial_division(n)
                success = len(factors) >= 2
                details = f"factors={factors}"
            except Exception as e:
                success = False
                details = f"error:{e}"
            wall = time.time() - t0
            w.writerow([n, "trial", success, f"{wall:.6f}", details])


if __name__ == "__main__":
    ns = [15, 21, 35, 55, 77, 91, 143, 3233]
    out = REPO_ROOT / "artifacts" / "factor_compare.csv"
    run(ns, out)
    print("Wrote", out)
