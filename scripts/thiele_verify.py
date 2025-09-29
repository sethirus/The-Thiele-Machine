import argparse
import hashlib
import json
import os
import sys
import tempfile
import subprocess

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
        mu_total = 0.0
        has_inf = False
        for step in data.get('steps', []):
            step_hash = step.get('step_hash')
            if step_hash is None:
                print(f"[WARN] skipping {name}: missing step_hash (not a low-level receipt)")
                return 0.0
            mu = step.get('mu_delta', 0)
            if mu == 'INF' or data.get('mu_total') == 'INF':
                has_inf = True
                break
            if not verify_solver_artifacts(step):
                raise ValueError(f"solver artifact check failed in {name} at step {step.get('idx', '?')}")
            mu_total += float(mu)
        if has_inf:
            mu_total = float('inf')
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
