from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def test_rfc9162_item51_has_immutable_freeze():
    text = (ROOT / "research/rounds/2026-10-01-part5-item5.1-round1-freeze.md").read_text()
    for section in ("2.1.1", "2.1.3.2", "2.1.4.2"):
        assert f"RFC 9162 Section {section}" in text
    assert "rfc9162-merkle-target.v.sha256" in text


def test_rfc9162_model_contains_real_algorithm_state():
    text = (ROOT / "coq/kernel/reductions/RFC9162MerkleTarget.v").read_text()
    for symbol in (
        "hash_leaf",
        "hash_node",
        "inclusion_fold",
        "verify_inclusion",
        "consistency_fold",
        "verify_consistency",
    ):
        assert f"{symbol}" in text
    assert "Nat.odd fn" in text
    assert "Nat.div2" in text


def test_rfc9162_result_does_not_claim_hash_security():
    text = (ROOT / "research/rounds/2026-10-01-part5-item5.1-round1-results.md").read_text()
    assert "collision resistance is not proved" in text
    assert "RFC 9162" in text
    assert "Adversarial read: PASS" in text
