#!/usr/bin/env python3
import json, sys, hashlib, subprocess, argparse, pathlib
from jsonschema import validate

def sha256_hex(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()

def canonical_json(obj) -> bytes:
    # Normative: UTF-8, sorted keys, separators without spaces
    return json.dumps(obj, sort_keys=True, ensure_ascii=False, separators=(",",":")).encode("utf-8")

def recompute_step_hash(step_obj: dict) -> str:
    # Exclude 'step_hash' when hashing
    tmp = dict(step_obj); tmp.pop("step_hash", None)
    return sha256_hex(canonical_json(tmp))

def recompute_global_digest(steps):
    concatenated = b"".join(bytes.fromhex(s["step_hash"]) for s in steps)
    return sha256_hex(concatenated)

def verify_solver_artifacts(step: dict) -> bool:
    # TODO: if proof_portable in {DRAT,LRAT}, invoke checker; else optional model replay
    # For now, accept and leave hook for Copilot to fill.
    return True

def recompute_mu(receipt: dict) -> int:
    mu = 0
    for s in receipt["steps"]:
        mu += int(s["mubits_delta"])
        if mu < 0: raise ValueError("μ underflow")
    return mu

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("receipt_path")
    ap.add_argument("--schema", required=True)
    args = ap.parse_args()

    receipt = json.loads(pathlib.Path(args.receipt_path).read_text("utf-8"))
    schema = json.loads(pathlib.Path(args.schema).read_text("utf-8"))

    # 1) Schema
    validate(instance=receipt, schema=schema)

    # 2) Step hashes
    for s in receipt["steps"]:
        expect = s["step_hash"]
        got = recompute_step_hash(s)
        if expect.lower() != got:
            print(f"FAIL step {s['idx']}: hash mismatch", file=sys.stderr); sys.exit(2)

        if not verify_solver_artifacts(s):
            print(f"FAIL step {s['idx']}: solver artifact invalid", file=sys.stderr); sys.exit(3)

    # 3) Global digest
    gd = recompute_global_digest(receipt["steps"])
    if gd.lower() != receipt["global_digest"].lower():
        print("FAIL: global digest mismatch", file=sys.stderr); sys.exit(4)

    # 4) μ ledger
    mu = recompute_mu(receipt)
    print(f"OK μ={mu} digest={gd}")

if __name__ == "__main__":
    main()