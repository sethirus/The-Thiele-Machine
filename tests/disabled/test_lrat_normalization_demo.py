import json
from pathlib import Path


def test_lrat_requires_normalization(tmp_path: Path):
    """Create a receipt that references an LRAT proof containing the token 'rat'
    and verify that canonicalize_file marks the step as requires_normalization.
    """
    from scripts.canonicalize_receipts import canonicalize_file

    cnf = tmp_path / "demo.cnf"
    cnf.write_text("c demo\np cnf 1 1\n1 0\n")
    proof = tmp_path / "demo.lrat"
    # include the token 'rat' to trigger the analyzer's conservative rejection
    proof.write_text("this is a fake lrat file containing RAT hint\nrat\n")

    receipt = tmp_path / "receipt.json"
    data = {
        "spec_version": "1.0",
        "steps": [
            {
                "step": 0,
                "instruction": {"op": "LASSERT", "payload": {}},
                "pre_state": {"pc": 0},
                "post_state": {"pc": 1},
                "pre_state_hash": "", "post_state_hash": "",
                "observation": {"mu_delta": 1.0, "cert": {}},
                "cnf_blob_uri": str(cnf),
                "proof_blob_uri": str(proof),
                "proof_portable": "LRAT",
            }
        ],
    }
    receipt.write_text(json.dumps(data, indent=2))

    updated = canonicalize_file(receipt)
    assert updated
    new = json.loads(receipt.read_text())
    step = new["steps"][0]
    assert step.get("status") == "requires_normalization"
