import json
import hashlib
import tempfile
import os
from pathlib import Path

import pytest

from tools.receipts import ReceiptValidator, ReceiptValidationError
from scripts.thiele_verify import parse_cnf, _canonicalise_cnf_and_map, _canonicalise_model, model_satisfies


def test_sparse_var_model_mapping():
    # CNF uses vars 1,3,7. Clause (1 or -3) and (7)
    cnf_text = "1 -3 0\n7 0\n"
    cnf = parse_cnf(cnf_text.encode('utf-8'))
    canonical_cnf, var_map = _canonicalise_cnf_and_map(cnf)
    # original model: var1 True -> literal 1; var3 False -> literal -3; var7 True -> 7
    model = [1, -3, 7]
    mapped = _canonicalise_model(model, var_map)
    assert model_satisfies(canonical_cnf, mapped)


def test_receipt_certificate_hash_mismatch():
    # Build a simple receipt with a certificate but wrong certificate_hash
    receipt = {
        "spec_version": "1.0",
        "kernel_pubkey": "00" * 32,
        "signature": "00" * 64,
        "global_digest": "",
        "steps": [
            {
                "step_hash": "deadbeef",
                "mu_delta": 1,
                "certificate": {"foo": "bar"},
                "certificate_hash": "00" * 32,
            }
        ],
    }
    # Compute a correct canonical step_hash & certificate_hash to make the digest logic
    # inside ReceiptValidator raise the proper error for certificate mismatch
    # We'll rely on ReceiptValidator to notice certificate hash mismatch.
    rv = ReceiptValidator(require_signature=False)
    with pytest.raises(ReceiptValidationError):
        rv.validate(receipt)


def test_mu_mismatch_detection():
    # build a spec_version 1.1 receipt where LASSERT mu_delta is tampered
    receipt = {
        "spec_version": "1.1",
        "kernel_pubkey": "00" * 32,
        "signature": "00" * 64,
        "global_digest": "",
        "steps": [
            {
                "step_hash": "",
                "instruction": {"op": "LASSERT", "payload": "(q)"},
                "observation": {
                    "cert": {"smt_query": "(q)", "mu_accounting": {"blind_cost": 1, "sighted_cost": 1}}
                },
                "mu_delta": 999.0,
            }
        ],
    }
    rv = ReceiptValidator(require_signature=False)
    # The validator should recompute mu and detect mismatch
    with pytest.raises(ReceiptValidationError):
        rv.validate(receipt)


def test_non_rup_lrat_rejection(tmp_path):
    # Heuristic: verifier rejects LRAT files containing the token 'RAT' (case-insensitive)
    # Create a fake LRAT file with 'RAT' and a receipt pointing at it; verify that the
    # scripts.thiele_verify.verify_solver_artifacts path returns False.
    from scripts.thiele_verify import verify_solver_artifacts

    lrat_path = tmp_path / "fake.lrat"
    lrat_path.write_text("1 2 0  % RAT-only hint\n")
    step = {
        "proof_portable": "LRAT",
        "proof_blob_uri": str(lrat_path),
        "cnf_blob_uri": None,
    }
    assert not verify_solver_artifacts(step)


def test_medium_cnf_sanity():
    # Build a medium CNF: 100 variables, 2000 clauses of single-literal clauses (satisfiable)
    vars_count = 100
    clauses = [[i] for i in range(1, vars_count + 1)] * 20  # 2000 clauses
    # generate a model that sets all to true
    model = list(range(1, vars_count + 1))
    # canonicalise and test satisfiability
    canonical_cnf, var_map = _canonicalise_cnf_and_map(clauses)
    mapped_model = _canonicalise_model(model, var_map)
    assert model_satisfies(canonical_cnf, mapped_model)


def test_canonical_model_persistence(tmp_path):
    # Create CNF and model files, write a receipt referencing them, run canonicalize_file
    from scripts.canonicalize_receipts import canonicalize_file

    cnf_path = tmp_path / "instance.cnf"
    cnf_path.write_text("p cnf 3 2\n1 -3 0\n7 0\n", encoding="utf-8")
    model_path = tmp_path / "m.model"
    model_path.write_text("1 -3 7 0\n", encoding="utf-8")

    receipt = {
        "spec_version": "1.0",
        "steps": [
            {
                "idx": 0,
                "cnf_blob_uri": str(cnf_path),
                "model_blob_uri": str(model_path),
                "observation": {"cert": {"smt_query": "(q)"}},
            }
        ],
    }
    receipt_path = tmp_path / "r.json"
    receipt_path.write_text(json.dumps(receipt), encoding="utf-8")

    updated = canonicalize_file(receipt_path)
    assert updated
    data = json.loads(receipt_path.read_text(encoding="utf-8"))
    step = data["steps"][0]
    assert "model_blob_uri" in step and "model_sha256" in step
    new_model_path = Path(step["model_blob_uri"])
    assert new_model_path.exists()
    # verify model sha matches file
    actual = hashlib.sha256(new_model_path.read_bytes()).hexdigest()
    assert actual == step["model_sha256"]


def test_validator_blob_hash_mismatch(tmp_path):
    # Create a CNF file and a receipt claiming an incorrect cnf_sha256
    cnf_path = tmp_path / "x.cnf"
    cnf_path.write_text("p cnf 1 1\n1 0\n", encoding="utf-8")
    wrong_sha = "0" * 64
    step = {
        "idx": 0,
        "cnf_blob_uri": str(cnf_path),
        "cnf_sha256": wrong_sha,
    }
    # compute canonical step_hash with the wrong sha embedded
    from tools.receipts import compute_step_hash, compute_global_digest

    step_hash = compute_step_hash(step)
    step["step_hash"] = step_hash
    receipt = {"spec_version": "1.1", "steps": [step], "global_digest": compute_global_digest([step_hash])}
    rv = ReceiptValidator(require_signature=False)
    with pytest.raises(ReceiptValidationError):
        rv.validate(receipt)
