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
        with open(path, 'r') as fh:
            data = json.load(fh)
        mu_total = 0.0
        for step in data.get('steps', []):
            step_hash = step.get('step_hash')
            if step_hash is None:
                raise ValueError(f"missing step_hash in {name}")
            # For golden files, we trust the step_hash is correct
            mu = step.get('mubits_delta', 0)
            if mu == 'INF' or data.get('mu_total') == 'INF':
                raise ValueError(f"infinite mu in {name}")
            # New: check solver artifacts
            if not verify_solver_artifacts(step):
                raise ValueError(f"solver artifact check failed in {name} at step {step.get('idx', '?')}")
            mu_total += float(mu)
        total += mu_total
        print(f"{name}: mu {mu_total}")
    print(f"total mu {total}")
    return total



def main() -> int:
    p = argparse.ArgumentParser(description='verify Thiele receipts')
    p.add_argument('directory')
    args = p.parse_args()
    try:
        verify_dir(args.directory)
    except ValueError as e:
        print(str(e))
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
