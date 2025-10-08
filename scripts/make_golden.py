from __future__ import annotations

import argparse
import hashlib
import json
import random
from itertools import product
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey

ROOT = Path(__file__).resolve().parents[1]
import sys

if str(ROOT) not in sys.path:
    sys.path.append(str(ROOT))

from tools.receipts import compute_global_digest, compute_step_hash

SIGNING_KEY = Ed25519PrivateKey.from_private_bytes(
    bytes.fromhex("48d08feaed0790e6f63cd549f64c1cf05d9c57fdb73cfcfa88c30762b46d0cd9")
)
KERNEL_PUBKEY_HEX = SIGNING_KEY.public_key().public_bytes(
    encoding=serialization.Encoding.Raw,
    format=serialization.PublicFormat.Raw,
).hex()


# ---------------------------------------------------------------------------
# CNF helpers

def parity3_cnf(x1: int, x2: int, x3: int, rhs: int) -> List[List[int]]:
    """Return clauses encoding x1 XOR x2 XOR x3 = rhs."""

    if rhs % 2 == 0:
        return [
            [-x1, -x2, -x3],
            [x1, x2, -x3],
            [x1, -x2, x3],
            [-x1, x2, x3],
        ]
    return [
        [x1, x2, x3],
        [-x1, -x2, x3],
        [-x1, x2, -x3],
        [x1, -x2, -x3],
    ]


def generate_tseitin_cnf() -> List[List[int]]:
    """Small Tseitin contradiction over a single AND gate."""

    return [
        [-1, -2, 4],  # y4 = x1 ∧ x2
        [1, -4],
        [2, -4],
        [4],
        [-4],
    ]


def generate_horn_cnf() -> List[List[int]]:
    """Horn instance: x1 → x2 together with the fact x1."""

    return [
        [-1, 2],
        [1],
    ]


def max_variable(clauses: Sequence[Sequence[int]]) -> int:
    return max((abs(lit) for clause in clauses for lit in clause), default=0)


def evaluate_clause(clause: Sequence[int], assignment: Dict[int, bool]) -> bool:
    return any((assignment[abs(lit)] if lit > 0 else not assignment[abs(lit)]) for lit in clause)


def exhaustive_truth_table(clauses: Sequence[Sequence[int]]):
    """Enumerate all assignments, returning either a model or a full table."""

    variables = max_variable(clauses)
    failures: List[Dict[str, object]] = []
    for bits in product([False, True], repeat=variables):
        assignment = {idx + 1: bits[idx] for idx in range(variables)}
        satisfied = True
        violated = None
        for idx, clause in enumerate(clauses):
            if not evaluate_clause(clause, assignment):
                satisfied = False
                violated = idx
                break
        if satisfied:
            return {
                "result": "sat",
                "variables": variables,
                "checked_assignments": len(failures) + 1,
                "model": assignment,
                "failures": failures,
            }
        failures.append(
            {
                "assignment": {str(var): int(val) for var, val in assignment.items()},
                "violated_clause": violated,
            }
        )
    return {
        "result": "unsat",
        "variables": variables,
        "checked_assignments": len(failures),
        "model": None,
        "truth_table": {"variables": variables, "entries": failures},
    }


def write_dimacs(path: Path, clauses: Sequence[Sequence[int]], variables: int) -> str:
    path.parent.mkdir(parents=True, exist_ok=True)
    lines = [f"p cnf {variables} {len(clauses)}"]
    for clause in clauses:
        lines.append(" ".join(str(lit) for lit in clause) + " 0")
    content = "\n".join(lines) + "\n"
    path.write_text(content, encoding="utf-8")
    return hashlib.sha256(content.encode("utf-8")).hexdigest()


def write_json(path: Path, data: dict) -> str:
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w", encoding="utf-8") as fh:
        json.dump(data, fh, indent=2, sort_keys=True)
        fh.write("\n")
    return hashlib.sha256(json.dumps(data, sort_keys=True).encode("utf-8")).hexdigest()


def write_model(path: Path, model: Dict[int, bool]) -> str:
    path.parent.mkdir(parents=True, exist_ok=True)
    literals = [str(var if value else -var) for var, value in sorted(model.items())]
    content = " ".join(literals + ["0"]) + "\n"
    path.write_text(content, encoding="utf-8")
    return hashlib.sha256(content.encode("utf-8")).hexdigest()


def _relative(path: Path) -> str:
    return str(path.relative_to(ROOT))


def _sign_digest(digest_hex: str) -> str:
    return SIGNING_KEY.sign(bytes.fromhex(digest_hex)).hex()


def _stamp_receipt(steps: Iterable[dict]) -> dict:
    steps_list = [dict(step) for step in steps]
    step_hashes = [step["step_hash"] for step in steps_list]
    digest = compute_global_digest(step_hashes)
    return {
        "spec_version": "1.0",
        "kernel_pubkey": KERNEL_PUBKEY_HEX,
        "steps": steps_list,
        "global_digest": digest,
        "signature": _sign_digest(digest),
    }


# ---------------------------------------------------------------------------
# Solver summaries used in certificates

def solve_sighted_xor(rows: Sequence[Tuple[Sequence[int], int]]):
    seen: Dict[Tuple[int, ...], int] = {}
    operations = 0
    inconsistent = False
    for coeffs, rhs in rows:
        key = tuple(int(c % 2) for c in coeffs)
        parity = rhs % 2
        operations += 1
        previous = seen.get(key)
        if previous is None:
            seen[key] = parity
        elif previous != parity:
            inconsistent = True
            operations += 1
            break
    rank_A = len(seen)
    rank_aug = rank_A + (1 if inconsistent else 0)
    return {
        "method": "gaussian_elimination_mod2",
        "operations": operations,
        "rank_A": rank_A,
        "rank_aug": rank_aug,
        "rank_gap": rank_aug - rank_A,
        "result": "unsat" if inconsistent else "sat",
    }


def solve_horn_forward(cnf: Sequence[Sequence[int]]):
    rules: List[Tuple[set[int], int | None]] = []
    agenda: List[int] = []
    for clause in cnf:
        positives = [lit for lit in clause if lit > 0]
        negatives = {abs(lit) for lit in clause if lit < 0}
        if len(positives) > 1:
            raise ValueError("not a Horn clause")
        head = positives[0] if positives else None
        rules.append((negatives, head))
        if head is not None and not negatives:
            agenda.append(head)
    operations = 0
    true_atoms: set[int] = set()
    while agenda:
        atom = agenda.pop()
        if atom in true_atoms:
            continue
        true_atoms.add(atom)
        for premise, head in rules:
            operations += 1
            if not premise.issubset(true_atoms):
                continue
            if head is None:
                return {
                    "method": "horn_forward_chaining",
                    "operations": operations,
                    "conflict_premise": sorted(premise),
                    "result": "unsat",
                }
            if head not in true_atoms:
                agenda.append(head)
    return {
        "method": "horn_forward_chaining",
        "operations": operations,
        "model_atoms": sorted(true_atoms),
        "result": "sat",
    }


def solve_tseitin_units(cnf: Sequence[Sequence[int]]):
    units: List[Tuple[int, int]] = [
        (clause[0], idx) for idx, clause in enumerate(cnf) if len(clause) == 1
    ]
    assignment: Dict[int, bool] = {}
    sources: Dict[int, int] = {}
    operations = 0
    while units:
        lit, source = units.pop()
        var = abs(lit)
        val = lit > 0
        operations += 1
        previous = assignment.get(var)
        if previous is None:
            assignment[var] = val
            sources[var] = source
            continue
        if previous != val:
            return {
                "method": "unit_propagation_conflict",
                "operations": operations,
                "conflict": {"variable": var, "clauses": [sources[var], source]},
                "result": "unsat",
            }
    return {
        "method": "unit_propagation_conflict",
        "operations": operations,
        "assignment": {str(k): int(v) for k, v in assignment.items()},
        "result": "unknown",
    }


# ---------------------------------------------------------------------------
# Step builders

def build_xor_step(tag: str, idx: int) -> dict:
    clauses: List[List[int]] = []
    clauses.extend(parity3_cnf(1, 2, 3, 0))
    clauses.extend(parity3_cnf(1, 2, 3, 1))
    analysis = exhaustive_truth_table(clauses)
    if analysis["result"] != "unsat":
        raise RuntimeError("XOR instance unexpectedly satisfiable")
    cnf_path = ROOT / "spec" / "golden" / f"{tag}.cnf"
    cnf_hash = write_dimacs(cnf_path, clauses, analysis["variables"])
    table_path = ROOT / "spec" / "golden" / f"{tag}_truth_table.json"
    table_hash = write_json(table_path, analysis["truth_table"])
    solver = solve_sighted_xor((([1, 1, 1], 0), ([1, 1, 1], 1)))
    mu_delta = max(1, analysis["checked_assignments"] - solver["operations"])
    certificate = {
        "problem": "xor_inconsistent_triple",
        "cnf": {
            "path": _relative(cnf_path),
            "variables": analysis["variables"],
            "clauses": len(clauses),
            "sha256": cnf_hash,
        },
        "blind_search": {
            "checked_assignments": analysis["checked_assignments"],
            "truth_table": {
                "path": _relative(table_path),
                "sha256": table_hash,
            },
        },
        "sighted_solver": solver,
        "mu_accounting": {
            "blind_cost": analysis["checked_assignments"],
            "sighted_cost": solver["operations"],
            "mu_delta": mu_delta,
        },
    }
    certificate_hash = hashlib.sha256(
        json.dumps(certificate, sort_keys=True).encode("utf-8")
    ).hexdigest()
    step = {
        "idx": idx,
        "transition": "xor_partition_resolution",
        "mu_delta": mu_delta,
        "solver": "xor_partition_solver",
        "solver_cmdline": "python scripts/make_golden.py",
        "cnf_blob_uri": _relative(cnf_path),
        "proof_portable": "TRUTH_TABLE_UNSAT",
        "proof_blob_uri": _relative(table_path),
        "certificate": certificate,
        "certificate_hash": certificate_hash,
    }
    step["step_hash"] = compute_step_hash(step)
    return step


def build_tseitin_step(tag: str, idx: int) -> dict:
    clauses = generate_tseitin_cnf()
    analysis = exhaustive_truth_table(clauses)
    if analysis["result"] != "unsat":
        raise RuntimeError("Tseitin instance unexpectedly satisfiable")
    cnf_path = ROOT / "spec" / "golden" / f"{tag}.cnf"
    cnf_hash = write_dimacs(cnf_path, clauses, analysis["variables"])
    table_path = ROOT / "spec" / "golden" / f"{tag}_truth_table.json"
    table_hash = write_json(table_path, analysis["truth_table"])
    solver = solve_tseitin_units(clauses)
    mu_delta = max(1, analysis["checked_assignments"] - solver["operations"])
    certificate = {
        "problem": "tseitin_unit_conflict",
        "cnf": {
            "path": _relative(cnf_path),
            "variables": analysis["variables"],
            "clauses": len(clauses),
            "sha256": cnf_hash,
        },
        "blind_search": {
            "checked_assignments": analysis["checked_assignments"],
            "truth_table": {
                "path": _relative(table_path),
                "sha256": table_hash,
            },
        },
        "sighted_solver": solver,
        "mu_accounting": {
            "blind_cost": analysis["checked_assignments"],
            "sighted_cost": solver["operations"],
            "mu_delta": mu_delta,
        },
    }
    certificate_hash = hashlib.sha256(
        json.dumps(certificate, sort_keys=True).encode("utf-8")
    ).hexdigest()
    step = {
        "idx": idx,
        "transition": "tseitin_unit_propagation",
        "mu_delta": mu_delta,
        "solver": "tseitin_unit_solver",
        "solver_cmdline": "python scripts/make_golden.py",
        "cnf_blob_uri": _relative(cnf_path),
        "proof_portable": "TRUTH_TABLE_UNSAT",
        "proof_blob_uri": _relative(table_path),
        "certificate": certificate,
        "certificate_hash": certificate_hash,
    }
    step["step_hash"] = compute_step_hash(step)
    return step


def build_horn_step(tag: str, idx: int) -> dict:
    clauses = generate_horn_cnf()
    analysis = exhaustive_truth_table(clauses)
    if analysis["result"] != "sat" or analysis["model"] is None:
        raise RuntimeError("Horn instance should be satisfiable")
    cnf_path = ROOT / "spec" / "golden" / f"{tag}.cnf"
    cnf_hash = write_dimacs(cnf_path, clauses, analysis["variables"])
    model_path = ROOT / "spec" / "golden" / f"{tag}_model.txt"
    model_hash = write_model(model_path, analysis["model"])
    solver = solve_horn_forward(clauses)
    mu_delta = max(1, analysis["checked_assignments"] - solver["operations"])
    certificate = {
        "problem": "horn_forward_reasoning",
        "cnf": {
            "path": _relative(cnf_path),
            "variables": analysis["variables"],
            "clauses": len(clauses),
            "sha256": cnf_hash,
        },
        "blind_search": {
            "checked_assignments": analysis["checked_assignments"],
            "first_failures": analysis.get("failures", [])[:2],
        },
        "sighted_solver": solver,
        "mu_accounting": {
            "blind_cost": analysis["checked_assignments"],
            "sighted_cost": solver["operations"],
            "mu_delta": mu_delta,
        },
        "model": {
            "path": _relative(model_path),
            "sha256": model_hash,
        },
    }
    certificate_hash = hashlib.sha256(
        json.dumps(certificate, sort_keys=True).encode("utf-8")
    ).hexdigest()
    step = {
        "idx": idx,
        "transition": "horn_forward_reasoning",
        "mu_delta": mu_delta,
        "solver": "horn_forward_solver",
        "solver_cmdline": "python scripts/make_golden.py",
        "cnf_blob_uri": _relative(cnf_path),
        "model_blob_uri": _relative(model_path),
        "certificate": certificate,
        "certificate_hash": certificate_hash,
    }
    step["step_hash"] = compute_step_hash(step)
    return step


# ---------------------------------------------------------------------------
# Receipt generators

def generate_xor_receipt() -> None:
    step = build_xor_step("xor_small", 0)
    receipt = _stamp_receipt([step])
    write_json(ROOT / "spec" / "golden" / "xor_small.json", receipt)


def generate_tseitin_receipt() -> None:
    step = build_tseitin_step("tseitin_small", 0)
    receipt = _stamp_receipt([step])
    write_json(ROOT / "spec" / "golden" / "tseitin_small.json", receipt)


def generate_horn_receipt() -> None:
    step = build_horn_step("horn_small", 0)
    receipt = _stamp_receipt([step])
    write_json(ROOT / "spec" / "golden" / "horn_small.json", receipt)


def generate_order_invariant_xor(shuffle: bool, out_path: str) -> None:
    stem = Path(out_path).stem
    step_a = build_xor_step(f"{stem}_step0", 0)
    step_b = build_xor_step(f"{stem}_step1", 1)
    steps = [step_a, step_b]
    if shuffle:
        random.shuffle(steps)
    receipt = _stamp_receipt(steps)
    write_json(Path(out_path), receipt)
    print(f"Wrote {out_path}: mu={sum(step['mu_delta'] for step in steps)}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Generate Thiele golden receipts")
    parser.add_argument("--generate-order-invariant", action="store_true")
    parser.add_argument("--order-outA", default="spec/golden/xor_small_orderA.json")
    parser.add_argument("--order-outB", default="spec/golden/xor_small_orderB.json")
    args = parser.parse_args()
    if args.generate_order_invariant:
        generate_order_invariant_xor(shuffle=False, out_path=args.order_outA)
        generate_order_invariant_xor(shuffle=True, out_path=args.order_outB)
    else:
        generate_xor_receipt()
        generate_tseitin_receipt()
        generate_horn_receipt()
        generate_order_invariant_xor(shuffle=False, out_path=args.order_outA)
        generate_order_invariant_xor(shuffle=True, out_path=args.order_outB)
