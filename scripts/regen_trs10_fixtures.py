#!/usr/bin/env python3
"""Regenerate the TRS-1.0 fixture corpus under tests/fixtures/trs10/.

Updates demo programs to the canonical baseline (INIT_PT 0 128, PNEW {0,128})
and re-signs all valid + invalid receipts against the same fixture key. Invalid
fixtures are derived from the regenerated valid receipt, then a single field is
tampered to keep the failure mode stable.
"""

from __future__ import annotations

import json
import re
import shutil
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from build.thiele_vm import run_vm_trace
from thielecpu.receipt import (
    EXECUTION_STATE_MODEL,
    TRS10_VERSION,
    SIG_SCHEME,
    build_execution_receipt_payload,
    build_receipt_payload,
    canonicalize_program_source,
    digest_vm_state,
    load_private_key_from_hex_file,
    sign_receipt_payload,
    split_init_lines,
    payload_digest,
)
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey

FIXTURE_ROOT = ROOT / "tests" / "fixtures" / "trs10"
TEST_PRIVATE_KEY_HEX = "082c001813feb4d26e8bb941414b0e577c7ece64fcfa71d0012dc653abccfbff"
KEY_ID = "fixture-suite"


def _private_key() -> Ed25519PrivateKey:
    return Ed25519PrivateKey.from_private_bytes(bytes.fromhex(TEST_PRIVATE_KEY_HEX))


def _write_receipt(path: Path, receipt: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _rewrite_asm_baseline(asm_path: Path) -> None:
    if not asm_path.exists():
        return
    text = asm_path.read_text(encoding="utf-8")
    new_text = text
    new_text = re.sub(r"INIT_PT\s+0\s+256\b", "INIT_PT 0 128", new_text)
    new_text = re.sub(r"PNEW\s+\{0,256\}", "PNEW {0,128}", new_text)
    if new_text != text:
        asm_path.write_text(new_text, encoding="utf-8")


def _build_signed_execution_receipt(program_path: Path) -> dict:
    canonical_program = canonicalize_program_source(program_path)
    canonical_lines = canonical_program["canonical_lines"]
    init_lines = split_init_lines(canonical_lines)
    fuel = canonical_program["fuel"]
    pre_state = run_vm_trace(init_lines, fuel=fuel)
    post_state = run_vm_trace(canonical_lines, fuel=fuel)

    payload = build_execution_receipt_payload(
        program_path=program_path,
        pre_state=pre_state,
        post_state=post_state,
        key_id=KEY_ID,
    )
    return sign_receipt_payload(payload, private_key=_private_key())


def _build_signed_fileset_receipt(files: list[Path], *, metadata=...) -> dict:
    payload = build_receipt_payload(files, metadata=metadata, key_id=KEY_ID)
    return sign_receipt_payload(payload, private_key=_private_key())


def _resign(payload: dict) -> dict:
    digest = payload_digest(payload)
    signature = _private_key().sign(digest.encode("utf-8"))
    return {
        **payload,
        "global_digest": digest,
        "sig_scheme": SIG_SCHEME,
        "signature": signature.hex(),
    }


def _payload_only(receipt: dict) -> dict:
    keys = ("version", "kind", "program", "execution", "files", "metadata", "key_id")
    return {k: receipt[k] for k in keys if k in receipt}


def regen_execution_valid() -> dict:
    asm = FIXTURE_ROOT / "execution" / "valid" / "demo.asm"
    _rewrite_asm_baseline(asm)
    receipt = _build_signed_execution_receipt(asm)
    _write_receipt(FIXTURE_ROOT / "execution" / "valid" / "receipt.json", receipt)
    return receipt


def regen_execution_invalid_signature(valid_receipt: dict) -> None:
    target_dir = FIXTURE_ROOT / "execution" / "invalid" / "signature"
    target_asm = target_dir / "demo.asm"
    _rewrite_asm_baseline(target_asm)
    receipt = dict(valid_receipt)
    receipt["signature"] = "00" * 64
    _write_receipt(target_dir / "receipt.json", receipt)


def regen_execution_invalid_digest(valid_receipt: dict) -> None:
    target_dir = FIXTURE_ROOT / "execution" / "invalid" / "digest"
    _rewrite_asm_baseline(target_dir / "demo.asm")
    receipt = dict(valid_receipt)
    receipt["global_digest"] = "00" * 32
    _write_receipt(target_dir / "receipt.json", receipt)


def regen_execution_invalid_schema(valid_receipt: dict) -> None:
    target_dir = FIXTURE_ROOT / "execution" / "invalid" / "schema"
    _rewrite_asm_baseline(target_dir / "demo.asm")
    receipt = json.loads(json.dumps(valid_receipt))
    receipt["execution"].pop("mu_delta", None)
    payload = _payload_only(receipt)
    _write_receipt(target_dir / "receipt.json", _resign(payload))


def regen_execution_invalid_source_tamper(valid_receipt: dict) -> None:
    """Receipt is signed against a clean asm; the on-disk asm differs (extra trailing whitespace)."""
    target_dir = FIXTURE_ROOT / "execution" / "invalid" / "source_tamper"
    _rewrite_asm_baseline(target_dir / "demo.asm")
    receipt = json.loads(json.dumps(valid_receipt))
    target_asm = target_dir / "demo.asm"
    target_asm.write_text(target_asm.read_text(encoding="utf-8") + "; tampered\n", encoding="utf-8")
    _write_receipt(target_dir / "receipt.json", receipt)


def regen_execution_invalid_fuel(valid_receipt: dict) -> None:
    target_dir = FIXTURE_ROOT / "execution" / "invalid" / "fuel"
    _rewrite_asm_baseline(target_dir / "demo.asm")
    receipt = json.loads(json.dumps(valid_receipt))
    receipt["program"]["fuel"] = receipt["program"]["fuel"] + 1
    _write_receipt(target_dir / "receipt.json", _resign(_payload_only(receipt)))


def regen_execution_invalid_pre_state(valid_receipt: dict) -> None:
    target_dir = FIXTURE_ROOT / "execution" / "invalid" / "pre_state"
    _rewrite_asm_baseline(target_dir / "demo.asm")
    receipt = json.loads(json.dumps(valid_receipt))
    receipt["execution"]["pre_state_digest"] = "ff" * 32
    _write_receipt(target_dir / "receipt.json", _resign(_payload_only(receipt)))


def regen_execution_invalid_replay(valid_receipt: dict) -> None:
    target_dir = FIXTURE_ROOT / "execution" / "invalid" / "replay"
    _rewrite_asm_baseline(target_dir / "demo.asm")
    receipt = json.loads(json.dumps(valid_receipt))
    receipt["execution"]["post_state_digest"] = "ff" * 32
    _write_receipt(target_dir / "receipt.json", _resign(_payload_only(receipt)))


def regen_execution_invalid_mu(valid_receipt: dict) -> None:
    target_dir = FIXTURE_ROOT / "execution" / "invalid" / "mu"
    _rewrite_asm_baseline(target_dir / "demo.asm")
    receipt = json.loads(json.dumps(valid_receipt))
    receipt["execution"]["mu_delta"] = receipt["execution"]["mu_delta"] + 1
    _write_receipt(target_dir / "receipt.json", _resign(_payload_only(receipt)))


def regen_execution_invalid_nondeterminism(valid_receipt: dict) -> None:
    target_dir = FIXTURE_ROOT / "execution" / "invalid" / "nondeterminism"
    _rewrite_asm_baseline(target_dir / "demo.asm")
    receipt = json.loads(json.dumps(valid_receipt))
    receipt["execution"]["state_model"] = "thiele.vmstate.unsupported"
    _write_receipt(target_dir / "receipt.json", _resign(_payload_only(receipt)))


def regen_canonicalization_pairs() -> None:
    for sub in ("distinct", "equivalent"):
        for prog in ("program_a.asm", "program_b.asm"):
            _rewrite_asm_baseline(FIXTURE_ROOT / "execution" / "canonicalization" / sub / prog)


def regen_stress_large() -> dict:
    asm = FIXTURE_ROOT / "stress" / "large" / "long_demo.asm"
    _rewrite_asm_baseline(asm)
    receipt = _build_signed_execution_receipt(asm)
    _write_receipt(FIXTURE_ROOT / "stress" / "large" / "execution-receipt.json", receipt)
    return receipt


def regen_compat_v1() -> dict:
    asm = FIXTURE_ROOT / "compat" / "v1" / "golden" / "demo.asm"
    _rewrite_asm_baseline(asm)
    receipt = _build_signed_execution_receipt(asm)
    _write_receipt(FIXTURE_ROOT / "compat" / "v1" / "golden" / "execution-receipt.json", receipt)
    return receipt


def main() -> int:
    valid = regen_execution_valid()
    regen_execution_invalid_signature(valid)
    regen_execution_invalid_digest(valid)
    regen_execution_invalid_schema(valid)
    regen_execution_invalid_source_tamper(valid)
    regen_execution_invalid_fuel(valid)
    regen_execution_invalid_pre_state(valid)
    regen_execution_invalid_replay(valid)
    regen_execution_invalid_mu(valid)
    regen_execution_invalid_nondeterminism(valid)
    regen_canonicalization_pairs()
    regen_stress_large()
    regen_compat_v1()
    print("regenerated execution + canonicalization + stress + compat fixtures")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
