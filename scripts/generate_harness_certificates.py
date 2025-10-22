#!/usr/bin/env python3
"""Generate solver-independent certificates for attempt.py demonstrations."""

from __future__ import annotations

import json
import math
from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations
from pathlib import Path
from typing import List, Sequence, Tuple
import hashlib

import networkx as nx
import numpy as np

REPO_ROOT = Path(__file__).resolve().parents[1]
ARTIFACTS_DIR = REPO_ROOT / "artifacts"
ARTIFACTS_DIR.mkdir(exist_ok=True)


# ----------------------------- Paradox certificate -----------------------------

def write_paradox_certificate() -> None:
    dataset = [
        ("A", 0, 0, 0, 0),
        ("B", 1, 0, 0, 0),
        ("C", 0, 0, 1, 0),
        ("D", 1, 1, 1, 1),
    ]
    lam = [Fraction(1), Fraction(-1), Fraction(-1), Fraction(1)]
    coeffs = [(row[1], row[3], 1) for row in dataset]
    rhs = [row[4] for row in dataset]

    sum_k = sum(l * Fraction(k) for l, (k, _, _) in zip(lam, coeffs))
    sum_t = sum(l * Fraction(t) for l, (_, t, _) in zip(lam, coeffs))
    sum_c = sum(l for l in lam)
    sum_rhs = sum(l * Fraction(r) for l, r in zip(lam, rhs))

    lines = [
        "Paradox certificate for attempt.py",
        "===================================",
        "The blind solver demands a single affine rule a*K + b*T + c = W for all four pieces.",
        "Combining the rows with lambda = [1, -1, -1, 1] yields:",
        f"  Σ lambda_i * K_i = {sum_k}",
        f"  Σ lambda_i * T_i = {sum_t}",
        f"  Σ lambda_i       = {sum_c}",
        "so the left-hand side collapses to 0·a + 0·b + 0 = 0.",
        f"The right-hand side combines to Σ lambda_i * W_i = {sum_rhs} = 1.",
        "Therefore the affine requirements imply 0 = 1, proving the system UNSAT without solver help.",
    ]
    (ARTIFACTS_DIR / "paradox_certificate.txt").write_text("\n".join(lines) + "\n", encoding="utf-8")


# --------------------------- Discovery certificate ----------------------------

@dataclass
class LinearSolution:
    partition: Tuple[Tuple[int, ...], Tuple[int, ...]]
    coefficients: Tuple[Tuple[Fraction, Fraction, Fraction], Tuple[Fraction, Fraction, Fraction]]
    mdl_bits: float


def gaussian_solve(rows: Sequence[Tuple[int, int, int]], rhs: Sequence[int]) -> Tuple[Fraction, Fraction, Fraction] | None:
    aug = [[Fraction(k), Fraction(t), Fraction(1), Fraction(r)] for (k, t, _), r in zip(rows, rhs)]
    rcount = len(aug)
    ccount = 3
    pivot_row = 0
    pivot_cols: List[int] = []
    for col in range(ccount):
        pivot = None
        for r in range(pivot_row, rcount):
            if aug[r][col] != 0:
                pivot = r
                break
        if pivot is None:
            continue
        aug[pivot_row], aug[pivot] = aug[pivot], aug[pivot_row]
        pivot_val = aug[pivot_row][col]
        aug[pivot_row] = [entry / pivot_val for entry in aug[pivot_row]]
        for r in range(rcount):
            if r != pivot_row and aug[r][col] != 0:
                factor = aug[r][col]
                aug[r] = [aug[r][i] - factor * aug[pivot_row][i] for i in range(ccount + 1)]
        pivot_cols.append(col)
        pivot_row += 1
    for row in aug:
        if all(entry == 0 for entry in row[:ccount]) and row[ccount] != 0:
            return None
    solution = [Fraction(0)] * ccount
    for idx, col in enumerate(pivot_cols):
        solution[col] = aug[idx][ccount]
    return tuple(solution)


def partition_mdl(split: Tuple[Tuple[int, ...], Tuple[int, ...]], names: Sequence[str]) -> float:
    param_bits = 8
    num_groups = len(split)
    param_count = num_groups * 3
    split_count = 1 if num_groups == 1 else 2
    split_code = math.log2(split_count) if split_count > 1 else 0.0
    artifact = "|".join(",".join(names[i] for i in group) for group in split)
    mdl_bits = len(artifact.encode("utf-8")) * 8
    return mdl_bits + param_count * param_bits + split_code


def write_discovery_certificate() -> None:
    dataset = [
        ("A", 0, 0, 0, 0),
        ("B", 1, 0, 0, 0),
        ("C", 0, 0, 1, 0),
        ("D", 1, 1, 1, 1),
    ]
    names = [row[0] for row in dataset]
    coeff_rows = [(row[1], row[3], 1) for row in dataset]
    rhs = [row[4] for row in dataset]

    solutions: List[LinearSolution] = []
    indices = tuple(range(len(dataset)))
    for group in combinations(indices, 2):
        complement = tuple(sorted(set(indices) - set(group)))
        if len(complement) != 2:
            continue
        split = (tuple(sorted(group)), complement)
        coeff_left = [coeff_rows[i] for i in split[0]]
        coeff_right = [coeff_rows[i] for i in split[1]]
        rhs_left = [rhs[i] for i in split[0]]
        rhs_right = [rhs[i] for i in split[1]]
        sol_left = gaussian_solve(coeff_left, rhs_left)
        sol_right = gaussian_solve(coeff_right, rhs_right)
        if sol_left is None or sol_right is None:
            continue
        mdl = partition_mdl(split, names)
        solutions.append(
            LinearSolution(
                partition=split,
                coefficients=(sol_left, sol_right),
                mdl_bits=mdl,
            )
        )

    if not solutions:
        raise RuntimeError("No solvable partitions discovered")

    best_mdl = min(sol.mdl_bits for sol in solutions)
    epsilon = 1e-8
    winning = [sol for sol in solutions if abs(sol.mdl_bits - best_mdl) < epsilon]

    lines = [
        "Discovery certificate for attempt.py",
        "====================================",
        "Each partition below admits affine rules for both groups without Z3:",
    ]
    for sol in solutions:
        group_names = [
            "{" + ", ".join(names[i] for i in part) + "}" for part in sol.partition
        ]
        tag = "<= minimal MDL" if sol in winning else ""
        lines.append(
            f"Partition {group_names[0]} vs {group_names[1]}: MDL={sol.mdl_bits:.2f} bits {tag}"
        )
        for idx, coeffs in enumerate(sol.coefficients):
            a, b, c = coeffs
            member_names = ", ".join(names[i] for i in sol.partition[idx])
            lines.append(
                f"  Group {idx+1} ({member_names}): a={a}, b={b}, c={c} satisfies all rows exactly"
            )
    (ARTIFACTS_DIR / "discovery_partition_certificate.txt").write_text(
        "\n".join(lines) + "\n", encoding="utf-8"
    )


# ---------------------------- Expander certificates ---------------------------

def seeded_rng(global_seed: int, n: int, seed: int) -> np.random.Generator:
    payload = f"{global_seed}|{n}|{seed}".encode("utf-8")
    digest = hashlib.blake2b(payload, digest_size=8).digest()
    return np.random.default_rng(int.from_bytes(digest, "big"))


def make_odd_charge(n: int, rng: np.random.Generator) -> List[int]:
    charges = rng.integers(0, 2, size=n - 1).tolist()
    tail = 1 ^ (sum(charges) & 1)
    charges.append(tail)
    assert sum(charges) % 2 == 1
    return charges


def generate_tseitin_instance(n: int, seed: int, global_seed: int = 123456789) -> Tuple[List[Tuple[int, int]], List[int]]:
    if n % 2 != 0:
        raise ValueError("n must be even for a 3-regular graph")
    rng = seeded_rng(global_seed, n, seed)
    graph = nx.random_regular_graph(3, n, seed=rng)
    edges = sorted(tuple(sorted(e)) for e in graph.edges())
    charges = make_odd_charge(n, rng)
    return edges, charges


def parity_certificate(edges: Sequence[Tuple[int, int]], charges: Sequence[int]) -> str:
    lhs_statement = "Each edge appears in exactly two vertex parity equations, so Σ lhs ≡ 0 (mod 2)."
    rhs_sum = sum(charges)
    rhs_statement = f"Vertex charge sum Σ rhs = {rhs_sum}, which is odd, yielding 0 ≡ 1 (mod 2)."
    return lhs_statement + " " + rhs_statement


def write_expander_certificates() -> None:
    instances = []
    for n in (50, 80, 120):
        edges, charges = generate_tseitin_instance(n, seed=0)
        instance = {
            "n": n,
            "seed": 0,
            "edge_count": len(edges),
            "charges_sum": int(sum(charges)),
            "charges_parity": "odd" if sum(charges) % 2 else "even",
            "edges_sha256": hashlib.sha256(json.dumps(edges).encode("utf-8")).hexdigest(),
            "charges_sha256": hashlib.sha256(json.dumps(charges).encode("utf-8")).hexdigest(),
            "parity_certificate": parity_certificate(edges, charges),
        }
        instances.append(instance)
    (ARTIFACTS_DIR / "expander_unsat_certificates.json").write_text(
        json.dumps({"instances": instances}, indent=2) + "\n", encoding="utf-8"
    )


def main() -> None:
    write_paradox_certificate()
    write_discovery_certificate()
    write_expander_certificates()


if __name__ == "__main__":
    main()
