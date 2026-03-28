from __future__ import annotations

import subprocess
from pathlib import Path

import pytest


PROJECT_ROOT = Path(__file__).resolve().parent.parent
FIXTURE_ROOT = PROJECT_ROOT / "tests" / "fixtures" / "trs10"
NODE_VERIFIER = PROJECT_ROOT / "tools" / "trs10_node" / "verify_trs10.mjs"
TEST_PUBLIC_KEY_HEX = "254b57576959e5fb37d087a60d5a72bb75dcf82240cbd62577059695dda0ebea"


def _run_node_verifier(receipt_path: Path, *, base_dir: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [
            "node",
            str(NODE_VERIFIER),
            str(receipt_path),
            "--trusted-pubkey",
            TEST_PUBLIC_KEY_HEX,
            "--base-dir",
            str(base_dir),
        ],
        cwd=PROJECT_ROOT,
        capture_output=True,
        text=True,
    )


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
def test_node_verifier_accepts_valid_corpus(relative_dir: str, receipt_name: str) -> None:
    fixture_dir = FIXTURE_ROOT / relative_dir
    result = _run_node_verifier(fixture_dir / receipt_name, base_dir=fixture_dir)
    assert result.returncode == 0, result.stderr + result.stdout
    assert "Receipt verification succeeded" in result.stdout


@pytest.mark.parametrize(
    ("relative_dir", "message_fragment"),
    [
        ("fileset/invalid/signature", "invalid signature"),
        ("fileset/invalid/digest", "global_digest"),
        ("fileset/invalid/payload_tamper", "global_digest"),
        ("fileset/invalid/schema", "missing field"),
        ("fileset/invalid/kind_confusion", "Hybrid"),
        ("fileset/invalid/path_traversal", "unsupported path form"),
        ("fileset/invalid/metadata", "global_digest"),
        ("fileset/invalid/json_edge", "fileset.size must be an integer"),
        ("fileset/invalid/content", "Digest mismatch"),
        ("fileset/invalid/size", "Size mismatch"),
        ("execution/invalid/signature", "invalid signature"),
        ("execution/invalid/digest", "global_digest"),
        ("execution/invalid/schema", "missing field"),
        ("execution/invalid/source_tamper", "source_sha256"),
        ("execution/invalid/fuel", "fuel"),
        ("execution/invalid/pre_state", "pre_state_digest"),
        ("execution/invalid/replay", "post_state_digest"),
        ("execution/invalid/mu", "mu_delta"),
        ("execution/invalid/nondeterminism", "Unsupported execution state model"),
    ],
)
def test_node_verifier_rejects_invalid_corpus(relative_dir: str, message_fragment: str) -> None:
    fixture_dir = FIXTURE_ROOT / relative_dir
    result = _run_node_verifier(fixture_dir / "receipt.json", base_dir=fixture_dir)
    assert result.returncode != 0
    assert message_fragment in (result.stdout + result.stderr)