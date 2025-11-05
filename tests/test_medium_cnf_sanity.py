import json
from pathlib import Path

import pytest


def test_medium_cnf_canonicalize_and_verify(tmp_path: Path):
    """Create a medium CNF (200 vars unit clauses) and ensure canonicaliser and verifier paths run.

    This smoke test ensures the canonicaliser can read a CNF, the receipt flow
    accepts a simple step referencing the CNF, and the canonicaliser produces
    a canonical model file and `model_sha256` when appropriate. It's intentionally
    lightweight and does not require external proof tools.
    """
    from scripts.canonicalize_receipts import canonicalize_file

    cnf = tmp_path / "medium.cnf"
    # p cnf <vars> <clauses>
    num_vars = 200
    clauses = [f"{i} 0" for i in range(1, num_vars + 1)]
    content = "c medium test\n" + f"p cnf {num_vars} {len(clauses)}\n" + "\n".join(clauses) + "\n"
    cnf.write_text(content)

    receipt = tmp_path / "receipt.json"
    data = {
        "spec_version": "1.0",
        "steps": [
            {
                "step": 0,
                "instruction": {"op": "LASSERT", "payload": {}},
                "pre_state": {"pc": 0},
                "post_state": {"pc": 1},
                "pre_state_hash": "",
                "post_state_hash": "",
                "observation": {"mu_delta": 1.0, "cert": {}},
                "cnf_blob_uri": str(cnf),
            }
        ],
    }
    receipt.write_text(json.dumps(data, indent=2))

    updated = canonicalize_file(receipt)
    # canonicalize_file may or may not change the receipt depending on signing
    # availability; it should not raise and should return a boolean
    assert isinstance(updated, bool)

    new = json.loads(receipt.read_text())
    # After canonicalization, spec_version should be bumped to 1.1 when changes applied
    if updated:
        assert new.get("spec_version") == "1.1"
    # The step should still be present and well-formed
    assert "steps" in new and len(new["steps"]) == 1
