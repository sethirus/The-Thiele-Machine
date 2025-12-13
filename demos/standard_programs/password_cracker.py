"""Standard Program: Password Cracker

A brute-force password finder used to demonstrate blind vs sighted execution.
"""

from __future__ import annotations

import hashlib
import time
from typing import Any, Dict, Optional, Tuple


def crack_password_classical(
    target_hash: str, charset: str = "abcdefghijklmnopqrstuvwxyz", max_length: int = 4
) -> Tuple[Optional[str], int]:
    attempts = 0

    def generate_passwords(length: int, prefix: str = ""):
        nonlocal attempts
        if length == 0:
            attempts += 1
            yield prefix
            return
        for char in charset:
            yield from generate_passwords(length - 1, prefix + char)

    for length in range(1, max_length + 1):
        for password in generate_passwords(length):
            if hashlib.sha256(password.encode()).hexdigest() == target_hash:
                return password, attempts

    return None, attempts


def crack_password_structured(
    target_hash: str,
    charset: str = "abcdefghijklmnopqrstuvwxyz",
    max_length: int = 4,
    known_prefix: str = "",
    known_suffix: str = "",
) -> Tuple[Optional[str], int]:
    attempts = 0
    unknown_length = max_length - len(known_prefix) - len(known_suffix)
    if unknown_length < 0:
        return None, 0

    def generate_unknown(length: int, prefix: str = ""):
        nonlocal attempts
        if length == 0:
            attempts += 1
            yield prefix
            return
        for char in charset:
            yield from generate_unknown(length - 1, prefix + char)

    for length in range(0, unknown_length + 1):
        for middle in generate_unknown(length):
            candidate = known_prefix + middle + known_suffix
            if hashlib.sha256(candidate.encode()).hexdigest() == target_hash:
                return candidate, attempts

    return None, attempts


def crack_with_thiele_blind(target_hash: str, charset: str, max_length: int) -> Dict[str, Any]:
    from thielecpu.mu import question_cost_bits
    from thielecpu.state import State
    from thielecpu.vm import VM

    vm = VM(State())

    code = f'''
import hashlib

target_hash = "{target_hash}"
charset = "{charset}"
max_length = {max_length}
attempts = 0

def generate_passwords(length, prefix=""):
    global attempts
    if length == 0:
        attempts = attempts + 1
        return [prefix]
    results = []
    for char in charset:
        results.extend(generate_passwords(length - 1, prefix + char))
    return results

result = None
for length in range(1, max_length + 1):
    for password in generate_passwords(length):
        if hashlib.sha256(password.encode()).hexdigest() == target_hash:
            result = password
            break
    if result:
        break

__result__ = (result, attempts)
'''

    start_time = time.time()
    result, _ = vm.execute_python(code)
    elapsed = time.time() - start_time

    return {
        "mode": "BLIND",
        "password": result[0] if result else None,
        "attempts": result[1] if result else 0,
        "time": elapsed,
        "mu_cost": question_cost_bits(f"(crack-password {target_hash[:16]}...)"),
        "partitions": 1,
    }


def crack_with_thiele_sighted(
    target_hash: str,
    charset: str,
    max_length: int,
    known_prefix: str = "",
    known_suffix: str = "",
) -> Dict[str, Any]:
    from thielecpu.mu import information_gain_bits, question_cost_bits
    from thielecpu.state import State
    from thielecpu.vm import VM

    vm = VM(State())
    state = vm.state

    if known_prefix:
        state.pnew({i for i in range(len(known_prefix))})

    unknown_length = max_length - len(known_prefix) - len(known_suffix)
    if unknown_length > 0:
        state.pnew({i for i in range(len(known_prefix), len(known_prefix) + unknown_length)})

    if known_suffix:
        state.pnew({i for i in range(max_length - len(known_suffix), max_length)})

    code = f'''
import hashlib

target_hash = "{target_hash}"
charset = "{charset}"
known_prefix = "{known_prefix}"
known_suffix = "{known_suffix}"
unknown_length = {unknown_length}
attempts = 0

def generate_unknown(length, prefix=""):
    global attempts
    if length == 0:
        attempts = attempts + 1
        return [prefix]
    results = []
    for char in charset:
        results.extend(generate_unknown(length - 1, prefix + char))
    return results

result = None
for length in range(0, unknown_length + 1):
    for middle in generate_unknown(length):
        candidate = known_prefix + middle + known_suffix
        if hashlib.sha256(candidate.encode()).hexdigest() == target_hash:
            result = candidate
            break
    if result:
        break

__result__ = (result, attempts)
'''

    start_time = time.time()
    result, _ = vm.execute_python(code)
    elapsed = time.time() - start_time

    full_search_space = len(charset) ** max_length
    reduced_search_space = len(charset) ** unknown_length if unknown_length > 0 else 1

    mu_question = question_cost_bits(f"(crack-password {target_hash[:16]}...)"
    )
    mu_info_saved = information_gain_bits(full_search_space, reduced_search_space)

    partitions_used = sum([1 if known_prefix else 0, 1 if unknown_length > 0 else 0, 1 if known_suffix else 0])

    return {
        "mode": "SIGHTED",
        "password": result[0] if result else None,
        "attempts": result[1] if result else 0,
        "time": elapsed,
        "mu_cost": mu_question,
        "mu_saved": mu_info_saved,
        "partitions": max(partitions_used, 1),
        "search_reduction": f"{reduced_search_space}/{full_search_space}",
    }
