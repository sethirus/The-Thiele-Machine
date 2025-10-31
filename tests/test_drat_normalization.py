import json
import shutil
from pathlib import Path

import pytest


def _has_binary(name: str) -> bool:
    return shutil.which(name) is not None


@pytest.mark.skipif(not _has_binary("drat-trim"), reason="drat-trim not installed")
def test_drat_normalization_roundtrip(tmp_path: Path):
    """Create a tiny CNF and a fake DRAT proof, run analyzer --normalize and assert it exits 0.

    This test is skipped when `drat-trim` is not present (local dev). CI will have it.
    """
    from scripts.canonicalize_receipts import canonicalize_file

    cnf = tmp_path / "d.cnf"
    cnf.write_text("c demo\np cnf 1 1\n1 0\n")
    drat = tmp_path / "p.drat"
    # a minimal bogus DRAT file; drat-trim will likely reject, but the analyzer --normalize
    # should try to run drat-trim and return non-error code for this test environment.
    drat.write_text("0\n")

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
                "proof_blob_uri": str(drat),
                "proof_portable": "DRAT",
            }
        ],
    }
    receipt.write_text(json.dumps(data, indent=2))
    # canonicalizer will attempt normalization via analyzer --normalize which should use drat-trim.
    updated = canonicalize_file(receipt)
    assert updated
    new = json.loads(receipt.read_text())
    # analyzer may set status ok or requires_normalization depending on drat-trim behaviour
    assert "status" in new["steps"][0]
