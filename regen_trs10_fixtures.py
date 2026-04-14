#!/usr/bin/env python3
"""Regenerate stale TRS-1.0 execution receipt fixtures.

Affected fixtures (post_state_digest is stale due to VM state normalization change):
  1. tests/fixtures/trs10/execution/valid/receipt.json
  2. tests/fixtures/trs10/stress/large/execution-receipt.json
  3. tests/fixtures/trs10/compat/v1/golden/execution-receipt.json
  4. tests/fixtures/trs10/execution/invalid/mu/receipt.json  (intentionally wrong mu_delta=5)

Usage:
    python regen_trs10_fixtures.py
"""
from __future__ import annotations

import json
from pathlib import Path

from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey

from build.thiele_vm import run_vm_trace
from thielecpu.receipt import (
    build_execution_receipt_payload,
    canonicalize_program_source,
    split_init_lines,
)
from tools.trs10_standalone.protocol import canonical_json_bytes, payload_digest

TEST_PRIVATE_KEY_HEX = "082c001813feb4d26e8bb941414b0e577c7ece64fcfa71d0012dc653abccfbff"
FIXTURE_ROOT = Path("tests/fixtures/trs10")


def _load_private_key() -> Ed25519PrivateKey:
    return Ed25519PrivateKey.from_private_bytes(bytes.fromhex(TEST_PRIVATE_KEY_HEX))


def _sign_payload(payload: dict, private_key: Ed25519PrivateKey) -> dict:
    digest = payload_digest(payload)
    receipt = dict(payload)
    receipt["global_digest"] = digest
    receipt["sig_scheme"] = "ed25519"
    receipt["signature"] = private_key.sign(digest.encode("utf-8")).hex()
    return receipt


def _build_fresh_receipt(program_path: Path, key_id: str = "fixture-suite") -> dict:
    canonical = canonicalize_program_source(program_path)
    canonical_lines = canonical["canonical_lines"]
    init_lines = split_init_lines(canonical_lines)
    fuel = canonical["fuel"]

    pre_state = run_vm_trace(init_lines, fuel=fuel)
    post_state = run_vm_trace(canonical_lines, fuel=fuel)

    payload = build_execution_receipt_payload(
        program_path=program_path,
        pre_state=pre_state,
        post_state=post_state,
        key_id=key_id,
    )
    return _sign_payload(payload, _load_private_key())


def _write_receipt(path: Path, receipt: dict) -> None:
    path.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"  wrote {path}")


def main() -> None:
    # 1. execution/valid/receipt.json
    print("1. execution/valid/receipt.json")
    r = _build_fresh_receipt(FIXTURE_ROOT / "execution/valid/demo.asm")
    _write_receipt(FIXTURE_ROOT / "execution/valid/receipt.json", r)

    # 2. stress/large/execution-receipt.json
    print("2. stress/large/execution-receipt.json")
    r = _build_fresh_receipt(FIXTURE_ROOT / "stress/large/long_demo.asm")
    _write_receipt(FIXTURE_ROOT / "stress/large/execution-receipt.json", r)

    # 3. compat/v1/golden/execution-receipt.json
    print("3. compat/v1/golden/execution-receipt.json")
    r = _build_fresh_receipt(FIXTURE_ROOT / "compat/v1/golden/demo.asm")
    _write_receipt(FIXTURE_ROOT / "compat/v1/golden/execution-receipt.json", r)

    # 4. execution/invalid/mu/receipt.json — tampered mu_delta=5 (intentionally wrong)
    print("4. execution/invalid/mu/receipt.json (tampered mu_delta=5)")
    r = _build_fresh_receipt(FIXTURE_ROOT / "execution/invalid/mu/demo.asm")
    # Tamper: set mu_delta to wrong value, then re-digest and re-sign
    payload = {k: v for k, v in r.items() if k not in ("global_digest", "sig_scheme", "signature")}
    payload["execution"] = dict(payload["execution"])
    payload["execution"]["mu_delta"] = 5  # intentionally wrong
    r_tampered = _sign_payload(payload, _load_private_key())
    _write_receipt(FIXTURE_ROOT / "execution/invalid/mu/receipt.json", r_tampered)

    print("\nDone. Run tests to verify:")
    print("  python -m pytest tests/test_trs10_fixture_corpus.py tests/test_trs10_node_verifier.py -q")


if __name__ == "__main__":
    main()
