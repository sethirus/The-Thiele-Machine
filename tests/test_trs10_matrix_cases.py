from __future__ import annotations

import json
import subprocess
import sys
import tempfile
from pathlib import Path

import pytest

from tools.trs10_standalone.execution import StandaloneProgramCanonicalizer

pytestmark = pytest.mark.trs


PROJECT_ROOT = Path(__file__).resolve().parent.parent
FIXTURE_ROOT = PROJECT_ROOT / "tests" / "fixtures" / "trs10"
CREATE_RECEIPT_SCRIPT = PROJECT_ROOT / "scripts" / "create_receipt.py"
NODE_CANONICALIZER = PROJECT_ROOT / "tools" / "trs10_node" / "canonicalize_program.mjs"
TEST_PRIVATE_KEY_HEX = "082c001813feb4d26e8bb941414b0e577c7ece64fcfa71d0012dc653abccfbff"


def _node_canonical_facts(program_path: Path) -> dict:
    result = subprocess.run(
        ["node", str(NODE_CANONICALIZER), str(program_path)],
        cwd=PROJECT_ROOT,
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, result.stderr + result.stdout
    return json.loads(result.stdout)


def test_basename_collision_receipt_creation_fails() -> None:
    fixture_dir = FIXTURE_ROOT / "fileset" / "input" / "basename_collision"
    left = fixture_dir / "left" / "shared.txt"
    right = fixture_dir / "right" / "shared.txt"

    with tempfile.TemporaryDirectory() as tmpdir:
        output = Path(tmpdir) / "receipt.json"
        key_path = Path(tmpdir) / "signing.key"
        key_path.write_text(TEST_PRIVATE_KEY_HEX, encoding="utf-8")
        result = subprocess.run(
            [
                sys.executable,
                str(CREATE_RECEIPT_SCRIPT),
                str(left),
                str(right),
                "--output",
                str(output),
                "--sign",
                str(key_path),
                "--key-id",
                "test-suite",
            ],
            cwd=PROJECT_ROOT,
            capture_output=True,
            text=True,
        )

    assert result.returncode != 0
    assert "Duplicate file basename" in (result.stdout + result.stderr)


@pytest.mark.strict_node
def test_canonicalization_equivalence_pair_matches_across_verifiers() -> None:
    fixture_dir = FIXTURE_ROOT / "execution" / "canonicalization" / "equivalent"
    program_a = fixture_dir / "program_a.asm"
    program_b = fixture_dir / "program_b.asm"

    canonicalizer = StandaloneProgramCanonicalizer()
    python_a = canonicalizer.canonicalize(program_a)
    python_b = canonicalizer.canonicalize(program_b)
    node_a = _node_canonical_facts(program_a)
    node_b = _node_canonical_facts(program_b)

    assert python_a.canonical_sha256 == python_b.canonical_sha256
    assert node_a["canonicalSha256"] == node_b["canonicalSha256"]
    assert python_a.canonical_sha256 == node_a["canonicalSha256"]
    assert python_b.canonical_sha256 == node_b["canonicalSha256"]


@pytest.mark.strict_node
def test_canonicalization_distinct_pair_stays_distinct_across_verifiers() -> None:
    fixture_dir = FIXTURE_ROOT / "execution" / "canonicalization" / "distinct"
    program_a = fixture_dir / "program_a.asm"
    program_b = fixture_dir / "program_b.asm"

    canonicalizer = StandaloneProgramCanonicalizer()
    python_a = canonicalizer.canonicalize(program_a)
    python_b = canonicalizer.canonicalize(program_b)
    node_a = _node_canonical_facts(program_a)
    node_b = _node_canonical_facts(program_b)

    assert python_a.canonical_sha256 != python_b.canonical_sha256
    assert node_a["canonicalSha256"] != node_b["canonicalSha256"]
    assert python_a.canonical_sha256 == node_a["canonicalSha256"]
    assert python_b.canonical_sha256 == node_b["canonicalSha256"]