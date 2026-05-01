from __future__ import annotations

import json
from pathlib import Path

import pytest
from cryptography.exceptions import InvalidSignature

from tools.trs10_standalone import verify_receipt_dict

pytestmark = pytest.mark.trs


PROJECT_ROOT = Path(__file__).resolve().parent.parent
FIXTURE_ROOT = PROJECT_ROOT / "tests" / "fixtures" / "trs10"
TEST_PUBLIC_KEY_HEX = "254b57576959e5fb37d087a60d5a72bb75dcf82240cbd62577059695dda0ebea"


def _load_receipt(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


@pytest.mark.parametrize(
    ("relative_dir", "receipt_name"),
    [
        ("fileset/valid", "receipt.json"),
        ("execution/valid", "receipt.json"),
        ("stress/large", "fileset-receipt.json"),
        ("stress/large", "execution-receipt.json"),
        ("compat/v1/golden", "fileset-receipt.json"),
        ("compat/v1/golden", "execution-receipt.json"),
    ],
)
def test_fixture_corpus_valid_receipts_verify(relative_dir: str, receipt_name: str) -> None:
    fixture_dir = FIXTURE_ROOT / relative_dir
    receipt = _load_receipt(fixture_dir / receipt_name)
    verify_receipt_dict(receipt, trusted_public_key_hex=TEST_PUBLIC_KEY_HEX, base_dir=fixture_dir)


@pytest.mark.parametrize(
    ("relative_dir", "expected_exception", "message_fragment"),
    [
        ("fileset/invalid/signature", InvalidSignature, None),
        ("fileset/invalid/digest", ValueError, "global_digest"),
        ("fileset/invalid/payload_tamper", ValueError, "global_digest"),
        ("fileset/invalid/schema", ValueError, "missing field"),
        ("fileset/invalid/kind_confusion", ValueError, "Hybrid"),
        ("fileset/invalid/path_traversal", ValueError, "unsupported path form"),
        ("fileset/invalid/metadata", ValueError, "global_digest"),
        ("fileset/invalid/json_edge", ValueError, "fileset.size must be an integer"),
        ("fileset/invalid/content", ValueError, "Digest mismatch"),
        ("fileset/invalid/size", ValueError, "Size mismatch"),
        ("execution/invalid/signature", InvalidSignature, None),
        ("execution/invalid/digest", ValueError, "global_digest"),
        ("execution/invalid/schema", ValueError, "missing field"),
        ("execution/invalid/source_tamper", ValueError, "source_sha256"),
        ("execution/invalid/fuel", ValueError, "fuel"),
        ("execution/invalid/pre_state", ValueError, "pre_state_digest"),
        ("execution/invalid/replay", ValueError, "post_state_digest"),
        ("execution/invalid/mu", ValueError, "mu_delta"),
        ("execution/invalid/nondeterminism", ValueError, "Unsupported execution state model"),
    ],
)
def test_fixture_corpus_invalid_receipts_fail(
    relative_dir: str,
    expected_exception: type[Exception],
    message_fragment: str | None,
) -> None:
    fixture_dir = FIXTURE_ROOT / relative_dir
    receipt = _load_receipt(fixture_dir / "receipt.json")

    with pytest.raises(expected_exception) as exc_info:
        verify_receipt_dict(receipt, trusted_public_key_hex=TEST_PUBLIC_KEY_HEX, base_dir=fixture_dir)

    if message_fragment is not None:
        assert message_fragment in str(exc_info.value)


def test_fixture_corpus_manifest_tracks_implemented_cases() -> None:
    manifest = json.loads((FIXTURE_ROOT / "manifest.json").read_text(encoding="utf-8"))
    implemented = {entry["id"] for entry in manifest["planned_cases"] if entry["status"] == "implemented"}
    assert {"A1", "A2", "A3", "A4", "A5", "A6", "A7", "A8", "A9", "A10", "A11", "A12", "A13", "A14", "A15", "A16", "A17", "A18", "A19", "A20"} <= implemented
