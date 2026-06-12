from __future__ import annotations

import hashlib
import json
import subprocess
import sys
import tempfile
from pathlib import Path

import pytest

pytestmark = [pytest.mark.trs, pytest.mark.strict_extracted]


PROJECT_ROOT = Path(__file__).resolve().parent.parent
CREATE_EXECUTION_RECEIPT = PROJECT_ROOT / "scripts" / "create_execution_receipt.py"
VERIFY_RECEIPT = PROJECT_ROOT / "tools" / "verify_trs10.py"
TEST_PRIVATE_KEY_HEX = "082c001813feb4d26e8bb941414b0e577c7ece64fcfa71d0012dc653abccfbff"
TEST_PUBLIC_KEY_HEX = "254b57576959e5fb37d087a60d5a72bb75dcf82240cbd62577059695dda0ebea"


def _write_program(path: Path) -> None:
    path.write_text(
        "\n".join(
            [
                "FUEL 64",
                "INIT_PT 0 128",
                "INIT_ACTIVE_MODULE 0",
                "PNEW {0,256} 1",
                "LOAD_IMM r1 42 1",
                "LOAD_IMM r2 58 1",
                "ADD r3 r1 r2 1",
                "HALT 0",
            ]
        )
        + "\n",
        encoding="utf-8",
    )


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _run(cmd: list[str], cwd: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)


def test_execution_receipt_roundtrip_is_deterministic() -> None:
    with tempfile.TemporaryDirectory() as tmpdir:
        workspace = Path(tmpdir)
        program_path = workspace / "demo.asm"
        receipt_a = workspace / "receipt-a.json"
        receipt_b = workspace / "receipt-b.json"
        key_path = workspace / "signing.key"

        _write_program(program_path)
        key_path.write_text(TEST_PRIVATE_KEY_HEX, encoding="utf-8")

        create_cmd = [
            sys.executable,
            str(CREATE_EXECUTION_RECEIPT),
            str(program_path),
            "--output",
            str(receipt_a),
            "--sign",
            str(key_path),
            "--key-id",
            "test-suite",
        ]
        first = _run(create_cmd, PROJECT_ROOT)
        assert first.returncode == 0, first.stderr

        create_cmd[4] = str(receipt_b)
        second = _run(create_cmd, PROJECT_ROOT)
        assert second.returncode == 0, second.stderr

        receipt1 = json.loads(receipt_a.read_text(encoding="utf-8"))
        receipt2 = json.loads(receipt_b.read_text(encoding="utf-8"))

        assert receipt1["kind"] == "execution"
        assert receipt1["version"] == "TRS-1.0"
        assert receipt1["program"]["path"] == "demo.asm"
        assert receipt1["program"]["source_sha256"] == _sha256(program_path)
        assert len(receipt1["program"]["canonical_sha256"]) == 64
        assert receipt1["execution"]["mu_delta"] == (
            receipt1["execution"]["mu_end"] - receipt1["execution"]["mu_start"]
        )
        assert len(receipt1["execution"]["pre_state_digest"]) == 64
        assert len(receipt1["execution"]["post_state_digest"]) == 64
        assert receipt1["global_digest"] == receipt2["global_digest"]

        verify = _run(
            [
                sys.executable,
                str(VERIFY_RECEIPT),
                str(receipt_a),
                "--trusted-pubkey",
                TEST_PUBLIC_KEY_HEX,
            ],
            PROJECT_ROOT,
        )
        assert verify.returncode == 0, verify.stderr + verify.stdout


def test_execution_receipt_detects_program_tamper() -> None:
    with tempfile.TemporaryDirectory() as tmpdir:
        workspace = Path(tmpdir)
        program_path = workspace / "demo.asm"
        receipt_path = workspace / "receipt.json"
        key_path = workspace / "signing.key"

        _write_program(program_path)
        key_path.write_text(TEST_PRIVATE_KEY_HEX, encoding="utf-8")

        created = _run(
            [
                sys.executable,
                str(CREATE_EXECUTION_RECEIPT),
                str(program_path),
                "--output",
                str(receipt_path),
                "--sign",
                str(key_path),
                "--key-id",
                "test-suite",
            ],
            PROJECT_ROOT,
        )
        assert created.returncode == 0, created.stderr

        program_path.write_text(program_path.read_text(encoding="utf-8").replace("58", "59", 1), encoding="utf-8")

        verified = _run(
            [
                sys.executable,
                str(VERIFY_RECEIPT),
                str(receipt_path),
                "--trusted-pubkey",
                TEST_PUBLIC_KEY_HEX,
            ],
            PROJECT_ROOT,
        )
        assert verified.returncode != 0
        assert "source_sha256" in (verified.stdout + verified.stderr) or "canonical_sha256" in (verified.stdout + verified.stderr)