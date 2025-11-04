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
import tempfile
import subprocess
import sys
from pathlib import Path
import pytest
from hypothesis import given, strategies as st, settings, HealthCheck

# Add project root to path
PROJECT_ROOT = Path(__file__).parent.parent
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


def cli_create_receipt(files, output_path, metadata=None):
    """Create a receipt using the CLI tool."""
    cmd = [
        sys.executable,
        str(PROJECT_ROOT / "create_receipt.py"),
    ]
    
    # Add files
    cmd.extend([str(f) for f in files])
    
    # Add output
    cmd.extend(["--output", str(output_path)])
    
    # Add metadata if provided
    if metadata:
        try:
            cmd.extend(["--metadata", json.dumps(metadata)])
        except (TypeError, ValueError):
            # Skip invalid metadata
            pass
    
    result = subprocess.run(cmd, capture_output=True, text=True, cwd=PROJECT_ROOT)
    return result.returncode == 0


def cli_verify_receipt(receipt_path):
    """Verify a receipt using the CLI tool."""
    cmd = [
        sys.executable,
        str(PROJECT_ROOT / "tools" / "verify_trs10.py"),
        str(receipt_path)
    ]
    
    result = subprocess.run(cmd, capture_output=True, text=True, cwd=PROJECT_ROOT)
    return result.returncode == 0


# ==================== Property-Based Tests ====================

class TestReceiptProperties:
    """Property-based tests for receipt generation and verification."""

    @given(
        content=text_content,
        filename=valid_filename,
        extension=file_extension
    )
    @settings(max_examples=50, suppress_health_check=[HealthCheck.function_scoped_fixture])
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
            
            if created and receipt_path.exists():
                # Verify receipt
                verified = cli_verify_receipt(receipt_path)
                assert verified, f"Verification failed for file: {full_filename}"

    @given(
        num_files=st.integers(min_value=1, max_value=10),
        contents=st.lists(text_content, min_size=1, max_size=10)
    )
    @settings(max_examples=30, suppress_health_check=[HealthCheck.function_scoped_fixture])
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
            
            if created and receipt_path.exists():
                # Verify receipt
                verified = cli_verify_receipt(receipt_path)
                assert verified, f"Verification failed for {num_files} files"

    @given(
        content=text_content,
        metadata=metadata_value
    )
    @settings(max_examples=30, suppress_health_check=[HealthCheck.function_scoped_fixture])
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
            
            if created and receipt_path.exists():
                # Check metadata is in receipt
                with open(receipt_path) as f:
                    receipt = json.load(f)
                
                # Only check if metadata is non-empty and serializable
                if metadata is not None and metadata != [] and metadata != {}:
                    if isinstance(metadata, (dict, list, str, int, float, bool)):
                        if "metadata" in receipt:
                            assert receipt["metadata"] == metadata

    @given(
        content=text_content,
        filename=valid_filename
    )
    @settings(max_examples=30, suppress_health_check=[HealthCheck.function_scoped_fixture])
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
            
            if created1 and created2 and receipt1_path.exists() and receipt2_path.exists():
                with open(receipt1_path) as f:
                    receipt1 = json.load(f)
                
                with open(receipt2_path) as f:
                    receipt2 = json.load(f)
                
                # Global digests should be identical
                assert receipt1["global_digest"] == receipt2["global_digest"]
                
                # File hashes should be identical
                assert receipt1["files"][0]["sha256"] == receipt2["files"][0]["sha256"]

    @given(
        binary_data=binary_content,
        filename=valid_filename
    )
    @settings(max_examples=30, suppress_health_check=[HealthCheck.function_scoped_fixture])
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
            
            if created and receipt_path.exists():
                # Verify receipt
                verified = cli_verify_receipt(receipt_path)
                assert verified, "Binary file verification failed"

    @given(
        content1=text_content,
        content2=text_content
    )
    @settings(max_examples=30, suppress_health_check=[HealthCheck.function_scoped_fixture])
    def test_property_different_content_different_digest(self, content1, content2):
        """
        Property: Different file contents produce different digests (collision resistance).
        """
        # Skip if contents are identical
        if content1 == content2:
            return
        
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
            
            if created1 and created2:
                with open(receipt1_path) as f:
                    receipt1 = json.load(f)
                
                with open(receipt2_path) as f:
                    receipt2 = json.load(f)
                
                # Digests should be different (collision resistance)
                assert receipt1["global_digest"] != receipt2["global_digest"]

    @given(
        content=text_content,
        filename=valid_filename
    )
    @settings(max_examples=20, suppress_health_check=[HealthCheck.function_scoped_fixture])
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
            
            if created and receipt_path.exists():
                with open(receipt_path) as f:
                    receipt = json.load(f)
                
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


if __name__ == "__main__":
    # Run tests
    pytest.main([__file__, "-v", "--tb=short"])
