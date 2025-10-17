# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

import argparse
import hashlib
import json
import os
import sys
import tempfile
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.append(str(ROOT))

from tools.receipts import ReceiptValidator, ReceiptValidationError

validator = ReceiptValidator()

def run_cmd(argv):
    try:
        subprocess.run(argv, check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        return True
    except subprocess.CalledProcessError:
        return False

def fetch_blob(uri):
    # For now, assume uri is a path to a file or inline blob
    if uri is None:
        return b""
    if os.path.exists(uri):
        with open(uri, "rb") as f:
            return f.read()
    # If inline, treat as base64 or utf-8 string
    try:
        return uri.encode("utf-8")
    except Exception:
        return b""

def parse_cnf(blob):
    # Minimal DIMACS parser: returns list of clauses (list of ints)
    lines = blob.decode("utf-8").splitlines()
    clauses = []
    for line in lines:
        line = line.strip()
        if not line or line.startswith("c") or line.startswith("p"):
            continue
        clause = [int(x) for x in line.split() if x != "0"]
        if clause:
            clauses.append(clause)
    return clauses

def parse_model(blob):
    # Parse model as space-separated ints (DIMACS style)
    return [int(x) for x in blob.decode("utf-8").split() if x]

def model_satisfies(cnf, model):
    # Model is a list of literals (positive for True, negative for False)
    model_set = set(model)
    for clause in cnf:
        if not any(lit in model_set for lit in clause):
            return False
    return True


def _load_json_blob(uri: str | None):
    if uri is None:
        return None
    blob = fetch_blob(uri)
    try:
        return json.loads(blob.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError):
        return None


def _normalise_truth_assignment(raw_assignment, variables: int):
    if not isinstance(raw_assignment, dict):
        return None
    assignment: dict[int, bool] = {}
    for key, value in raw_assignment.items():
        try:
            var = int(key)
        except (TypeError, ValueError):
            return None
        if not (1 <= var <= variables):
            return None
        if isinstance(value, bool):
            assignment[var] = value
        elif value in (0, 1):
            assignment[var] = bool(value)
        else:
            return None
    if len(assignment) != variables:
        return None
    return assignment


def _literal_truth(lit: int, assignment: dict[int, bool]) -> bool:
    value = assignment.get(abs(lit))
    if value is None:
        raise ValueError("assignment missing variable")
    return value if lit > 0 else not value


def _clause_satisfied(clause, assignment: dict[int, bool]) -> bool:
    return any(_literal_truth(lit, assignment) for lit in clause)

def verify_solver_artifacts(step: dict) -> bool:
    pf = step.get("proof_portable")
    uri = step.get("proof_blob_uri")
    model_uri = step.get("model_blob_uri")
    cnf_uri = step.get("cnf_blob_uri")
    if pf == "DRAT":
        with tempfile.TemporaryDirectory() as td:
            cnf = os.path.join(td, "f.cnf")
            drat = os.path.join(td, "p.drat")
            open(cnf,"wb").write(fetch_blob(cnf_uri))
            open(drat,"wb").write(fetch_blob(uri))
            return run_cmd(["drat-trim", cnf, drat, "-o", os.devnull])
    elif pf == "LRAT":
        with tempfile.TemporaryDirectory() as td:
            cnf = os.path.join(td, "f.cnf")
            lrat = os.path.join(td, "p.lrat")
            open(cnf,"wb").write(fetch_blob(cnf_uri))
            open(lrat,"wb").write(fetch_blob(uri))
            return run_cmd(["lrat-check", cnf, lrat])
    elif pf == "TRUTH_TABLE_UNSAT":
        if cnf_uri is None or uri is None:
            return False
        cnf = parse_cnf(fetch_blob(cnf_uri))
        proof = _load_json_blob(uri)
        if not isinstance(proof, dict):
            return False
        variables = proof.get("variables")
        entries = proof.get("entries")
        if not isinstance(variables, int) or variables <= 0:
            return False
        if not isinstance(entries, list):
            return False
        expected = 1 << variables
        if len(entries) != expected:
            return False
        seen = set()
        for entry in entries:
            if not isinstance(entry, dict):
                return False
            assignment = _normalise_truth_assignment(entry.get("assignment"), variables)
            clause_idx = entry.get("violated_clause")
            if assignment is None or not isinstance(clause_idx, int):
                return False
            if clause_idx < 0 or clause_idx >= len(cnf):
                return False
            key = tuple(assignment[i] for i in range(1, variables + 1))
            if key in seen:
                return False
            seen.add(key)
            clause = cnf[clause_idx]
            if _clause_satisfied(clause, assignment):
                return False
        return len(seen) == expected
    elif model_uri:
        cnf = parse_cnf(fetch_blob(cnf_uri))
        model = parse_model(fetch_blob(model_uri))
        return model_satisfies(cnf, model)
    return True

def verify_dir(directory: str) -> float:
    total = 0.0
    for name in sorted(os.listdir(directory)):
        if not name.endswith('.json'):
            continue
        path = os.path.join(directory, name)
        total += verify_path(path)
    print(f"total mu {total}")
    return total


def verify_path(path: str) -> float:
    """Verify a single JSON receipt file. Returns the computed mu_total for the file.
    The function accepts two receipt shapes:
      - low-level receipts with a 'steps' list (legacy verifier behavior)
      - high-level benchmark receipts that contain 'mu_bits_ledger'
    Non-receipt JSON files are skipped with a warning.
    """
    name = os.path.basename(path)
    with open(path, 'r') as fh:
        data = json.load(fh)

    # If the JSON contains explicit 'steps' then run the detailed step verifier
    if 'steps' in data:
        if all(field in data for field in ("global_digest", "kernel_pubkey", "signature")):
            try:
                mu_total = validator.validate(data)
            except ReceiptValidationError as exc:
                raise ValueError(f"{name}: {exc}") from exc
            for step in data.get('steps', []):
                if not verify_solver_artifacts(step):
                    raise ValueError(
                        f"solver artifact check failed in {name} at step {step.get('idx', '?')}"
                    )
            print(f"{name}: mu {mu_total}")
            return mu_total

        mu_total = 0.0
        for step in data.get('steps', []):
            step_label = step.get('step_id', step.get('idx'))
            if step.get('step_hash') is None:
                raise ValueError(f"{name}: missing step_hash for step {step_label}")
            recorded_hash = step.get('certificate_hash')
            if recorded_hash is not None:
                certificate = step.get('certificate', "")
                if isinstance(certificate, str):
                    actual_hash = hashlib.sha256(certificate.encode('utf-8')).hexdigest()
                else:
                    actual_hash = hashlib.sha256(
                        json.dumps(certificate, sort_keys=True).encode('utf-8')
                    ).hexdigest()
                if recorded_hash != actual_hash:
                    raise ValueError(
                        f"{name}: certificate hash mismatch at step {step_label},"
                        " expected integrity of stored certificate"
                    )
            mu = step.get('mu_delta', 0)
            if mu == 'INF' or data.get('mu_total') == 'INF':
                raise ValueError(
                    f"Paradox detected in {name}: infinite μ charge requires manual review"
                )
            if not verify_solver_artifacts(step):
                raise ValueError(
                    f"solver artifact check failed in {name} at step {step.get('idx', '?')}"
                )
            mu_total += float(mu)
        print(f"{name}: mu {mu_total}")
        return mu_total

    # High-level benchmark receipt: accept mu_bits_ledger if present
    if 'mu_bits_ledger' in data:
        ledger = data.get('mu_bits_ledger', {})
        blind = ledger.get('blind')
        sighted = ledger.get('sighted')
        # derive a sensible numeric mu_total if possible
        try:
            mu_total = 0.0
            if isinstance(blind, (int, float)):
                mu_total += float(blind)
            if isinstance(sighted, (int, float)):
                mu_total += float(sighted)
            print(f"{name}: mu {mu_total}")
            return mu_total
        except Exception:
            print(f"[WARN] could not parse mu_bits_ledger in {name}; skipping")
            return 0.0

    # Support artefacts such as exported truth tables can be silently acknowledged
    if isinstance(data, dict) and {"variables", "entries"}.issubset(data.keys()):
        print(f"[INFO] acknowledged support artefact {name}")
        return 0.0

    if isinstance(data, list) and data and isinstance(data[0], dict):
        if all('blind_results' in row and 'sighted_results' in row for row in data):
            print(f"[INFO] acknowledged benchmark receipt {name}")
            return 0.0

    # Unknown/irrelevant JSON file
    print(f"[WARN] skipping {name}: unrecognized receipt format")
    return 0.0


def main() -> int:
    p = argparse.ArgumentParser(description='verify Thiele receipts')
    p.add_argument('path', help='A receipt file or a directory of receipts')
    args = p.parse_args()
    try:
        if os.path.isdir(args.path):
            verify_dir(args.path)
        elif os.path.isfile(args.path):
            verify_path(args.path)
        else:
            print(f"[ERROR] path not found: {args.path}")
            return 2
    except ValueError as e:
        print(str(e))
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())

