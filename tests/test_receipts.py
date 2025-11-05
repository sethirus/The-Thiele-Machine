# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

import json
import os
import sys
import tempfile

import pytest
from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey

sys.path.append(os.path.dirname(os.path.dirname(__file__)))

from scripts.thiele_verify import verify_dir
from tools.receipts import compute_step_hash, compute_global_digest


def _write_receipt(directory: str, mutate=None) -> str:
    private_key = Ed25519PrivateKey.generate()
    public_hex = private_key.public_key().public_bytes(
        encoding=serialization.Encoding.Raw,
        format=serialization.PublicFormat.Raw,
    ).hex()

    step = {
        "idx": 0,
        "transition": "unit_test",
        "mu_delta": 1,
        "solver": "unit-solver",
        "solver_cmdline": "pytest",
    }
    step_hash = compute_step_hash(step)
    step_with_hash = dict(step)
    step_with_hash["step_hash"] = step_hash

    digest = compute_global_digest([step_hash])
    signature = private_key.sign(bytes.fromhex(digest)).hex()

    receipt = {
        "spec_version": "1.0",
        "kernel_pubkey": public_hex,
        "steps": [step_with_hash],
        "global_digest": digest,
        "signature": signature,
    }

    if mutate is not None:
        mutate(receipt)

    path = os.path.join(directory, "receipt.json")
    with open(path, "w", encoding="utf-8") as fh:
        json.dump(receipt, fh, indent=2)
    return path


def test_valid_receipt():
    with tempfile.TemporaryDirectory() as tmp:
        _write_receipt(tmp)
        total = verify_dir(tmp)
        assert total == 1.0


def test_tampered_signature():
    with tempfile.TemporaryDirectory() as tmp:
        def mutate(data: dict) -> None:
            data["signature"] = "00" + data["signature"][2:]

        _write_receipt(tmp, mutate=mutate)
        with pytest.raises(ValueError):
            verify_dir(tmp)


def test_step_hash_mismatch():
    with tempfile.TemporaryDirectory() as tmp:
        def mutate(data: dict) -> None:
            data["steps"][0]["step_hash"] = "0" * 64

        _write_receipt(tmp, mutate=mutate)
        with pytest.raises(ValueError):
            verify_dir(tmp)


def test_truth_table_unsat_step():
    with tempfile.TemporaryDirectory() as tmp:
        cnf_path = os.path.join(tmp, "contradiction.cnf")
        with open(cnf_path, "w", encoding="utf-8") as fh:
            fh.write("p cnf 1 2\n1 0\n-1 0\n")

        truth_path = os.path.join(tmp, "truth.json")
        table = {
            "variables": 1,
            "entries": [
                {"assignment": {"1": 0}, "violated_clause": 0},
                {"assignment": {"1": 1}, "violated_clause": 1},
            ],
        }
        with open(truth_path, "w", encoding="utf-8") as fh:
            json.dump(table, fh, indent=2)

        private_key = Ed25519PrivateKey.generate()
        public_hex = private_key.public_key().public_bytes(
            encoding=serialization.Encoding.Raw,
            format=serialization.PublicFormat.Raw,
        ).hex()

        step = {
            "idx": 0,
            "transition": "truth_table_conflict",
            "mu_delta": 1,
            "solver": "unit-checker",
            "solver_cmdline": "pytest",
            "cnf_blob_uri": cnf_path,
            "proof_portable": "TRUTH_TABLE_UNSAT",
            "proof_blob_uri": truth_path,
        }
        step["step_hash"] = compute_step_hash(step)
        digest = compute_global_digest([step["step_hash"]])
        signature = private_key.sign(bytes.fromhex(digest)).hex()

        receipt = {
            "spec_version": "1.0",
            "kernel_pubkey": public_hex,
            "steps": [step],
            "global_digest": digest,
            "signature": signature,
        }

        path = os.path.join(tmp, "truth_receipt.json")
        with open(path, "w", encoding="utf-8") as fh:
            json.dump(receipt, fh, indent=2)

        total = verify_dir(tmp)
        assert total == 1.0
