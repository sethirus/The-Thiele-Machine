import json
import hashlib
from pathlib import Path


def _sha256_json(obj) -> str:
    payload = json.dumps(obj, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def test_demo_isomorphism_end_to_end(tmp_path: Path):
    """Create a tiny CNF/model/receipt, canonicalize it and verify it end-to-end."""
    from scripts.canonicalize_receipts import canonicalize_file
    from scripts.verify_receipt import verify_receipt_file

    # Create tiny CNF with sparse var ids (10 and 20)
    cnf = """c demo CNF
p cnf 20 2
10 0
20 0
"""
    cnf_path = tmp_path / "demo.cnf"
    cnf_path.write_text(cnf)

    # Model satisfying both unit clauses
    model_path = tmp_path / "demo.model"
    model_path.write_text("10 20 0\n")

    # Pre/post states and their hashes (use the same canonicalisation as verifier)
    pre_state = {"pc": 0}
    post_state = {"pc": 1}
    pre_hash = _sha256_json(pre_state)
    post_hash = _sha256_json(post_state)

    receipt = {
        "spec_version": "1.0",
        "global_digest": None,
        "steps": [
            {
                "step": 0,
                "instruction": {"op": "LASSERT", "payload": {}},
                "pre_state": pre_state,
                "post_state": post_state,
                "pre_state_hash": pre_hash,
                "post_state_hash": post_hash,
                "observation": {"mu_delta": 1.0, "cert": {}},
                "cnf_blob_uri": str(cnf_path),
                "model_blob_uri": str(model_path),
            }
        ],
    }

    receipt_path = tmp_path / "receipt.json"
    receipt_path.write_text(json.dumps(receipt, indent=2))

    # Run canonicalizer
    updated = canonicalize_file(receipt_path)
    assert updated, "Canonicalizer should have updated the receipt"

    # Reload receipt and check canonical fields were added
    data = json.loads(receipt_path.read_text())
    assert data.get("spec_version") == "1.1"
    steps = data.get("steps", [])
    assert len(steps) == 1
    step = steps[0]
    assert "model_blob_uri" in step and "cert_store" in step["model_blob_uri"]
    assert "model_sha256" in step
    assert "signature" in step
    assert "step_hash" in step
    assert "global_digest" in data and data["global_digest"]

    # Ensure there is a top-level signature: canonicalize_file sets per-step
    # signatures and global_digest but not a top-level signature. Sign the
    # global digest with the deterministic kernel secret so the ReceiptValidator
    # can verify the whole receipt.
    from tools.receipts import ReceiptValidator
    from nacl import signing

    if "signature" not in data:
        secret_path = Path("kernel_secret.key")
        assert secret_path.exists(), "kernel secret key should have been generated"
        sk = signing.SigningKey(secret_path.read_bytes())
        sig = sk.sign(bytes.fromhex(data["global_digest"]))
        data["signature"] = sig.signature.hex()
        # persist the signed receipt so debug is easier on failure
        receipt_path.write_text(json.dumps(data, ensure_ascii=False, sort_keys=True, indent=2))

    validator = ReceiptValidator(require_signature=True)
    # should not raise and should return the accumulated μ
    mu_total = validator.validate(data)
    assert abs(mu_total - 1.0) < 1e-9
