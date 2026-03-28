from __future__ import annotations

import json
import subprocess
import sys
import tempfile
from pathlib import Path

from tools.trs10_standalone import verify_receipt_dict


PROJECT_ROOT = Path(__file__).resolve().parent.parent
CREATE_RECEIPT_SCRIPT = PROJECT_ROOT / "create_receipt.py"
CREATE_EXECUTION_RECEIPT = PROJECT_ROOT / "create_execution_receipt.py"
TEST_PRIVATE_KEY_HEX = "082c001813feb4d26e8bb941414b0e577c7ece64fcfa71d0012dc653abccfbff"
TEST_PUBLIC_KEY_HEX = "254b57576959e5fb37d087a60d5a72bb75dcf82240cbd62577059695dda0ebea"


def _create_receipt(file_path: Path, receipt_path: Path, key_path: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [
            sys.executable,
            str(CREATE_RECEIPT_SCRIPT),
            str(file_path),
            "--output",
            str(receipt_path),
            "--sign",
            str(key_path),
            "--key-id",
            "test-suite",
        ],
        cwd=PROJECT_ROOT,
        capture_output=True,
        text=True,
    )


def _create_execution_receipt(program_path: Path, receipt_path: Path, key_path: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
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
        cwd=PROJECT_ROOT,
        capture_output=True,
        text=True,
    )


def _write_program(path: Path) -> None:
    path.write_text(
        "\n".join(
            [
                "FUEL 64",
                "INIT_PT 0 256",
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


def test_standalone_verifier_roundtrips_fileset_receipt() -> None:
    with tempfile.TemporaryDirectory() as tmpdir:
        workspace = Path(tmpdir)
        data_path = workspace / "artifact.txt"
        receipt_path = workspace / "receipt.json"
        key_path = workspace / "signing.key"

        data_path.write_text("hello trs10\n", encoding="utf-8")
        key_path.write_text(TEST_PRIVATE_KEY_HEX, encoding="utf-8")

        created = _create_receipt(data_path, receipt_path, key_path)
        assert created.returncode == 0, created.stderr

        receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
        verify_receipt_dict(receipt, trusted_public_key_hex=TEST_PUBLIC_KEY_HEX, base_dir=workspace)


def test_standalone_verifier_rejects_tampered_fileset_digest() -> None:
    with tempfile.TemporaryDirectory() as tmpdir:
        workspace = Path(tmpdir)
        data_path = workspace / "artifact.txt"
        receipt_path = workspace / "receipt.json"
        key_path = workspace / "signing.key"

        data_path.write_text("hello trs10\n", encoding="utf-8")
        key_path.write_text(TEST_PRIVATE_KEY_HEX, encoding="utf-8")

        created = _create_receipt(data_path, receipt_path, key_path)
        assert created.returncode == 0, created.stderr

        receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
        receipt["global_digest"] = "0" * 64

        try:
            verify_receipt_dict(receipt, trusted_public_key_hex=TEST_PUBLIC_KEY_HEX, base_dir=workspace)
        except ValueError as exc:
            assert "global_digest" in str(exc)
        else:
            raise AssertionError("Standalone verifier accepted a receipt with a tampered global_digest")


def test_standalone_verifier_roundtrips_execution_receipt() -> None:
    with tempfile.TemporaryDirectory() as tmpdir:
        workspace = Path(tmpdir)
        program_path = workspace / "demo.asm"
        receipt_path = workspace / "receipt.json"
        key_path = workspace / "signing.key"

        _write_program(program_path)
        key_path.write_text(TEST_PRIVATE_KEY_HEX, encoding="utf-8")

        created = _create_execution_receipt(program_path, receipt_path, key_path)
        assert created.returncode == 0, created.stderr

        receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
        verify_receipt_dict(receipt, trusted_public_key_hex=TEST_PUBLIC_KEY_HEX, base_dir=workspace)


def test_standalone_verifier_package_does_not_import_main_receipt_helper() -> None:
    package_root = PROJECT_ROOT / "tools" / "trs10_standalone"
    for path in package_root.rglob("*.py"):
        text = path.read_text(encoding="utf-8")
        lines = [line.strip() for line in text.splitlines()]
        assert all(
            line not in {"import thielecpu.receipt", "from thielecpu import receipt"}
            and "from thielecpu.receipt import " not in line
            for line in lines
        ), f"Standalone verifier must not import thielecpu.receipt: {path}"