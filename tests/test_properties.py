#!/usr/bin/env python3
"""
Property-based tests for Thiele Receipts using Hypothesis.

Tests that certain properties hold for all valid inputs:
- Creating + verifying a receipt always succeeds for valid inputs
- Receipts are deterministic (same input = same output)
- Global digest is consistent
- Metadata is preserved
"""

import json
import os
import hashlib
import subprocess
import sys
import tempfile
from pathlib import Path
import pytest
from hypothesis import given, strategies as st, settings, HealthCheck, assume

pytestmark = pytest.mark.slow

# Add project root to path
PROJECT_ROOT = Path(__file__).parent.parent
CREATE_RECEIPT_SCRIPT = PROJECT_ROOT / "scripts" / "create_receipt.py"
VERIFY_RECEIPT_SCRIPT = PROJECT_ROOT / "tools" / "verify_trs10.py"
TEST_PRIVATE_KEY_HEX = "082c001813feb4d26e8bb941414b0e577c7ece64fcfa71d0012dc653abccfbff"
TEST_PUBLIC_KEY_HEX = "254b57576959e5fb37d087a60d5a72bb75dcf82240cbd62577059695dda0ebea"
sys.path.insert(0, str(PROJECT_ROOT))


# ==================== Strategy Definitions ====================

# Generate valid filenames (no path traversal, no special chars)
valid_filename = st.text(
    alphabet=st.characters(
        whitelist_categories=('Lu', 'Ll', 'Nd'),
        whitelist_characters='-_.'
    ),
    min_size=1,
    max_size=50
).filter(lambda x: x and not x.startswith('.') and '..' not in x)

# Generate file extensions
file_extension = st.sampled_from(['.txt', '.json', '.py', '.md', '.dat', ''])

# Generate file contents (text)
text_content = st.text(
    alphabet=st.characters(blacklist_categories=('Cs',)),  # Exclude surrogates
    min_size=0,
    max_size=10000
)

# Generate file contents (binary)
binary_content = st.binary(min_size=0, max_size=10000)

# Generate metadata
metadata_value = st.recursive(
    st.one_of(
        st.none(),
        st.booleans(),
        st.integers(min_value=-1000000, max_value=1000000),
        st.floats(allow_nan=False, allow_infinity=False, width=32),
        st.text(max_size=100)
    ),
    lambda children: st.lists(children, max_size=5) | st.dictionaries(
        st.text(min_size=1, max_size=20), children, max_size=5
    )
)


# ==================== Helper Functions ====================

def create_test_file(workspace, filename, content):
    """Create a test file in the workspace."""
    if isinstance(content, str):
        filepath = workspace / filename
        filepath.write_text(content, encoding='utf-8')
    else:
        filepath = workspace / filename
        filepath.write_bytes(content)
    return filepath


def _require_receipt_tooling() -> None:
    if not CREATE_RECEIPT_SCRIPT.exists():
        pytest.skip(f"Receipt creation CLI not available: {CREATE_RECEIPT_SCRIPT}")
    if not VERIFY_RECEIPT_SCRIPT.exists():
        pytest.skip(f"Receipt verification CLI not available: {VERIFY_RECEIPT_SCRIPT}")


def _assert_completed(result: subprocess.CompletedProcess[str], context: str) -> None:
    assert result.returncode == 0, (
        f"{context} failed with exit code {result.returncode}\n"
        f"STDOUT:\n{result.stdout}\n"
        f"STDERR:\n{result.stderr}"
    )


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(65536), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _assert_receipt_matches_files(receipt: dict, files: list[Path]) -> None:
    assert "files" in receipt, "Receipt missing files list"
    entries = receipt["files"]
    assert len(entries) == len(files), (
        f"Receipt lists {len(entries)} files but expected {len(files)}"
    )

    entries_by_name = {Path(entry["path"]).name: entry for entry in entries}
    expected_names = {path.name for path in files}
    assert set(entries_by_name) == expected_names, (
        f"Receipt paths {sorted(entries_by_name)} do not match expected {sorted(expected_names)}"
    )

    for path in files:
        entry = entries_by_name[path.name]
        assert entry["sha256"] == _sha256(path), (
            f"Incorrect SHA-256 recorded for {path.name}"
        )
        assert entry["size"] == path.stat().st_size, (
            f"Incorrect size recorded for {path.name}"
        )


def cli_create_receipt(files, output_path, metadata=...):
    """Create a receipt using the CLI tool."""
    _require_receipt_tooling()
    cmd = [
        sys.executable,
        str(CREATE_RECEIPT_SCRIPT),
    ]
    
    # Add files
    cmd.extend([str(f) for f in files])
    
    # Add output
    cmd.extend(["--output", str(output_path)])

    # Add metadata if provided
    if metadata is not ...:
        try:
            cmd.extend(["--metadata", json.dumps(metadata)])
        except (TypeError, ValueError):
            # Skip invalid metadata
            pass

    with tempfile.NamedTemporaryFile('w', delete=False) as key_file:
        key_file.write(TEST_PRIVATE_KEY_HEX)
        key_path = key_file.name

    cmd.extend(["--sign", key_path, "--key-id", "test-suite"])

    try:
        result = subprocess.run(cmd, capture_output=True, text=True, cwd=PROJECT_ROOT)
    finally:
        os.unlink(key_path)

    return result


def cli_verify_receipt(receipt_path):
    """Verify a receipt using the CLI tool."""
    _require_receipt_tooling()
    cmd = [
        sys.executable,
        str(VERIFY_RECEIPT_SCRIPT),
        str(receipt_path),
        "--trusted-pubkey",
        TEST_PUBLIC_KEY_HEX,
    ]
    
    return subprocess.run(cmd, capture_output=True, text=True, cwd=PROJECT_ROOT)


# ==================== Property-Based Tests ====================

class TestReceiptProperties:
    """Property-based tests for receipt generation and verification."""

    @given(
        content=text_content,
        filename=valid_filename,
        extension=file_extension
    )
    @settings(max_examples=5, suppress_health_check=[HealthCheck.function_scoped_fixture])
    def test_property_single_file_roundtrip(self, content, filename, extension):
        """
        Property: Creating and verifying a receipt for any valid file succeeds.
        """
        with tempfile.TemporaryDirectory() as tmpdir:
            workspace = Path(tmpdir)
            
            # Create test file
            full_filename = filename + extension
            test_file = create_test_file(workspace, full_filename, content)
            receipt_path = workspace / "receipt.json"
            
            # Create receipt
            created = cli_create_receipt([test_file], receipt_path)
            _assert_completed(created, f"Receipt creation failed for file: {full_filename}")
            assert receipt_path.exists(), f"Receipt file missing for file: {full_filename}"

            with receipt_path.open(encoding="utf-8") as handle:
                receipt = json.load(handle)
            _assert_receipt_matches_files(receipt, [test_file])

            # Verify receipt
            verified = cli_verify_receipt(receipt_path)
            _assert_completed(verified, f"Verification failed for file: {full_filename}")

    @given(
        num_files=st.integers(min_value=1, max_value=10),
        contents=st.lists(text_content, min_size=1, max_size=10)
    )
    @settings(max_examples=5, suppress_health_check=[HealthCheck.function_scoped_fixture])
    def test_property_multiple_files_roundtrip(self, num_files, contents):
        """
        Property: Creating and verifying receipts for multiple files succeeds.
        """
        with tempfile.TemporaryDirectory() as tmpdir:
            workspace = Path(tmpdir)
            
            # Limit to available contents
            num_files = min(num_files, len(contents))
            
            # Create test files
            files = []
            for i in range(num_files):
                filename = f"file_{i}.txt"
                test_file = create_test_file(workspace, filename, contents[i])
                files.append(test_file)
            
            receipt_path = workspace / "receipt.json"
            
            # Create receipt
            created = cli_create_receipt(files, receipt_path)
            _assert_completed(created, f"Receipt creation failed for {num_files} files")
            assert receipt_path.exists(), f"Receipt file missing for {num_files} files"

            with receipt_path.open(encoding="utf-8") as handle:
                receipt = json.load(handle)
            _assert_receipt_matches_files(receipt, files)

            # Verify receipt
            verified = cli_verify_receipt(receipt_path)
            _assert_completed(verified, f"Verification failed for {num_files} files")

    @given(
        content=text_content,
        metadata=metadata_value
    )
    @settings(max_examples=5, suppress_health_check=[HealthCheck.function_scoped_fixture])
    def test_property_metadata_preserved(self, content, metadata):
        """
        Property: Metadata included in receipt is preserved exactly.
        """
        with tempfile.TemporaryDirectory() as tmpdir:
            workspace = Path(tmpdir)
            
            # Create test file
            test_file = create_test_file(workspace, "test.txt", content)
            receipt_path = workspace / "receipt.json"
            
            # Create receipt with metadata
            created = cli_create_receipt([test_file], receipt_path, metadata=metadata)
            _assert_completed(created, "Receipt creation with metadata failed")
            assert receipt_path.exists(), "Receipt file missing after metadata creation"

            # Check metadata is in receipt
            with receipt_path.open(encoding="utf-8") as handle:
                receipt = json.load(handle)

            _assert_receipt_matches_files(receipt, [test_file])
            assert "metadata" in receipt
            assert receipt["metadata"] == metadata

    @given(
        content=text_content,
        filename=valid_filename
    )
    @settings(max_examples=5, suppress_health_check=[HealthCheck.function_scoped_fixture])
    def test_property_deterministic_receipts(self, content, filename):
        """
        Property: Same file produces same global digest (deterministic).
        """
        with tempfile.TemporaryDirectory() as tmpdir:
            workspace = Path(tmpdir)
            
            # Create test file
            test_file = create_test_file(workspace, filename + ".txt", content)
            receipt1_path = workspace / "receipt1.json"
            receipt2_path = workspace / "receipt2.json"
            
            # Create two receipts from same file
            created1 = cli_create_receipt([test_file], receipt1_path)
            created2 = cli_create_receipt([test_file], receipt2_path)

            _assert_completed(created1, "First receipt creation failed for deterministic test")
            _assert_completed(created2, "Second receipt creation failed for deterministic test")
            assert receipt1_path.exists(), "First deterministic receipt file missing"
            assert receipt2_path.exists(), "Second deterministic receipt file missing"

            with receipt1_path.open(encoding="utf-8") as handle:
                receipt1 = json.load(handle)

            with receipt2_path.open(encoding="utf-8") as handle:
                receipt2 = json.load(handle)

            _assert_receipt_matches_files(receipt1, [test_file])
            _assert_receipt_matches_files(receipt2, [test_file])

            # Global digests should be identical
            assert receipt1["global_digest"] == receipt2["global_digest"]

            # File hashes should be identical
            assert receipt1["files"][0]["sha256"] == receipt2["files"][0]["sha256"]

    @given(
        binary_data=binary_content,
        filename=valid_filename
    )
    @settings(max_examples=5, suppress_health_check=[HealthCheck.function_scoped_fixture])
    def test_property_binary_files(self, binary_data, filename):
        """
        Property: Binary files are handled correctly (no corruption).
        """
        with tempfile.TemporaryDirectory() as tmpdir:
            workspace = Path(tmpdir)
            
            # Create binary file
            test_file = create_test_file(workspace, filename + ".bin", binary_data)
            receipt_path = workspace / "receipt.json"
            
            # Create receipt
            created = cli_create_receipt([test_file], receipt_path)
            _assert_completed(created, "Binary receipt creation failed")
            assert receipt_path.exists(), "Binary receipt file missing"

            with receipt_path.open(encoding="utf-8") as handle:
                receipt = json.load(handle)
            _assert_receipt_matches_files(receipt, [test_file])

            # Verify receipt
            verified = cli_verify_receipt(receipt_path)
            _assert_completed(verified, "Binary file verification failed")

    @given(
        content1=text_content,
        content2=text_content
    )
    @settings(max_examples=5, suppress_health_check=[HealthCheck.function_scoped_fixture])
    def test_property_different_content_different_digest(self, content1, content2):
        """
        Property: Different file contents produce different digests (collision resistance).
        """
        assume(content1 != content2)
        
        with tempfile.TemporaryDirectory() as tmpdir:
            workspace = Path(tmpdir)
            
            # Create two different files
            file1 = create_test_file(workspace, "file1.txt", content1)
            file2 = create_test_file(workspace, "file2.txt", content2)
            
            receipt1_path = workspace / "receipt1.json"
            receipt2_path = workspace / "receipt2.json"
            
            # Create receipts
            created1 = cli_create_receipt([file1], receipt1_path)
            created2 = cli_create_receipt([file2], receipt2_path)

            _assert_completed(created1, "First receipt creation failed for collision test")
            _assert_completed(created2, "Second receipt creation failed for collision test")
            assert receipt1_path.exists(), "First collision-test receipt file missing"
            assert receipt2_path.exists(), "Second collision-test receipt file missing"

            with receipt1_path.open(encoding="utf-8") as handle:
                receipt1 = json.load(handle)

            with receipt2_path.open(encoding="utf-8") as handle:
                receipt2 = json.load(handle)

            _assert_receipt_matches_files(receipt1, [file1])
            _assert_receipt_matches_files(receipt2, [file2])

            # Digests should be different (collision resistance)
            assert receipt1["global_digest"] != receipt2["global_digest"]

    @given(
        content=text_content,
        filename=valid_filename
    )
    @settings(max_examples=5, suppress_health_check=[HealthCheck.function_scoped_fixture])
    def test_property_receipt_structure_valid(self, content, filename):
        """
        Property: All generated receipts have valid TRS-1.0 structure.
        """
        with tempfile.TemporaryDirectory() as tmpdir:
            workspace = Path(tmpdir)
            
            # Create test file
            test_file = create_test_file(workspace, filename + ".txt", content)
            receipt_path = workspace / "receipt.json"
            
            # Create receipt
            created = cli_create_receipt([test_file], receipt_path)
            _assert_completed(created, "Receipt creation failed for structure test")
            assert receipt_path.exists(), "Receipt file missing for structure test"

            with receipt_path.open(encoding="utf-8") as handle:
                receipt = json.load(handle)

            _assert_receipt_matches_files(receipt, [test_file])

            # Required fields
            assert "version" in receipt
            assert receipt["version"].startswith("TRS-1")
            assert "files" in receipt
            assert isinstance(receipt["files"], list)
            assert len(receipt["files"]) >= 1
            assert "global_digest" in receipt
            assert isinstance(receipt["global_digest"], str)
            assert len(receipt["global_digest"]) == 64  # SHA-256 hex

            # File entry structure
            for file_entry in receipt["files"]:
                assert "path" in file_entry
                assert "sha256" in file_entry
                assert "size" in file_entry
                assert isinstance(file_entry["sha256"], str)
                assert len(file_entry["sha256"]) == 64
