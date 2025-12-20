from __future__ import annotations

from pathlib import Path

from thielecpu.audit_demo import run_mu_audit_demo


def test_audit_demo_reveal_changes_information_mu(tmp_path: Path) -> None:
    report = run_mu_audit_demo(tmp_path / "audit")

    # Both runs compute the same payload; we only check the accounting signal.
    assert report["diff"]["mu_information_delta"] > 0

    # Receipts exist and at least one signature verifies.
    assert report["a_reveal"]["receipts_len"] >= 1
    assert report["diff"]["receipt_signature_verified"] is True
