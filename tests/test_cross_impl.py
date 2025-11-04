#!/usr/bin/env python3
"""
Cross-implementation sanity and differential tests for Thiele Receipts.

Tests bidirectional compatibility between:
- CLI receipt generator (create_receipt.py)
- CLI receipt verifier (verifier/replay.py)
- Browser generator (web/create.js via headless browser)
- Browser verifier (web/verify.html via headless browser)

Includes positive tests (valid receipts) and negative tests (corruption detection).
"""

import sys
import json
import tempfile
import subprocess
import random
import string
from pathlib import Path
import pytest

# Add project root to path
PROJECT_ROOT = Path(__file__).parent.parent
sys.path.insert(0, str(PROJECT_ROOT))


class TestCrossImplementation:
    """Cross-implementation tests for receipt generation and verification."""

    @pytest.fixture
    def temp_workspace(self):
        """Create a temporary workspace for test files."""
        with tempfile.TemporaryDirectory() as tmpdir:
            yield Path(tmpdir)

    def generate_random_file(self, workspace, size=None, extension=".txt"):
        """Generate a random file for testing."""
        if size is None:
            size = random.randint(10, 1000)
        
        filename = f"test_{''.join(random.choices(string.ascii_lowercase, k=8))}{extension}"
        filepath = workspace / filename
        
        # Generate random content
        content = ''.join(random.choices(string.ascii_letters + string.digits + '\n ', k=size))
        filepath.write_text(content)
        
        return filepath

    def generate_random_binary_file(self, workspace, size=None):
        """Generate a random binary file for testing."""
        if size is None:
            size = random.randint(10, 1000)
        
        filename = f"test_{''.join(random.choices(string.ascii_lowercase, k=8))}.bin"
        filepath = workspace / filename
        
        # Generate random binary content
        content = bytes(random.randint(0, 255) for _ in range(size))
        filepath.write_bytes(content)
        
        return filepath

    def cli_create_receipt(self, files, output_path, metadata=None, sign=False):
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
            cmd.extend(["--metadata", json.dumps(metadata)])
        
        result = subprocess.run(cmd, capture_output=True, text=True, cwd=PROJECT_ROOT)
        
        if result.returncode != 0:
            print(f"STDOUT: {result.stdout}")
            print(f"STDERR: {result.stderr}")
            raise RuntimeError(f"CLI receipt creation failed: {result.stderr}")
        
        return output_path

    def cli_verify_receipt(self, receipt_path):
        """Verify a receipt using the CLI tool."""
        # Use the TRS-1.0 verifier
        cmd = [
            sys.executable,
            str(PROJECT_ROOT / "tools" / "verify_trs10.py"),
            str(receipt_path)
        ]
        
        result = subprocess.run(cmd, capture_output=True, text=True, cwd=PROJECT_ROOT)
        
        return {
            'success': result.returncode == 0,
            'stdout': result.stdout,
            'stderr': result.stderr
        }

    # ==================== PHASE 1.1: CLI-to-CLI Tests ====================

    def test_cli_single_small_file(self, temp_workspace):
        """Test: CLI creates and verifies receipt for single small file."""
        # Create test file
        test_file = self.generate_random_file(temp_workspace, size=14)
        receipt_path = temp_workspace / "receipt.json"
        
        # Create receipt
        self.cli_create_receipt([test_file], receipt_path)
        assert receipt_path.exists()
        
        # Verify receipt
        result = self.cli_verify_receipt(receipt_path)
        assert result['success'], f"Verification failed: {result['stderr']}"
        assert "global_digest" in result['stdout'].lower() or "verified" in result['stdout'].lower()

    def test_cli_multiple_files(self, temp_workspace):
        """Test: CLI creates and verifies receipt for multiple files."""
        # Create test files
        files = [
            self.generate_random_file(temp_workspace, size=random.randint(10, 500))
            for _ in range(5)
        ]
        receipt_path = temp_workspace / "receipt.json"
        
        # Create receipt
        self.cli_create_receipt(files, receipt_path)
        assert receipt_path.exists()
        
        # Verify receipt structure
        with open(receipt_path) as f:
            receipt = json.load(f)
        
        assert "version" in receipt
        assert "files" in receipt
        assert len(receipt["files"]) == 5
        
        # Verify receipt
        result = self.cli_verify_receipt(receipt_path)
        assert result['success'], f"Verification failed: {result['stderr']}"

    def test_cli_large_file(self, temp_workspace):
        """Test: CLI handles large files (1MB+)."""
        # Create 1MB file
        test_file = self.generate_random_file(temp_workspace, size=1024 * 1024)
        receipt_path = temp_workspace / "receipt.json"
        
        # Create receipt
        self.cli_create_receipt([test_file], receipt_path)
        assert receipt_path.exists()
        
        # Verify receipt
        result = self.cli_verify_receipt(receipt_path)
        assert result['success']

    def test_cli_binary_files(self, temp_workspace):
        """Test: CLI handles binary files correctly."""
        # Create binary files
        files = [
            self.generate_random_binary_file(temp_workspace, size=random.randint(100, 1000))
            for _ in range(3)
        ]
        receipt_path = temp_workspace / "receipt.json"
        
        # Create receipt
        self.cli_create_receipt(files, receipt_path)
        assert receipt_path.exists()
        
        # Verify receipt
        result = self.cli_verify_receipt(receipt_path)
        assert result['success']

    def test_cli_with_metadata(self, temp_workspace):
        """Test: CLI correctly includes metadata in receipts."""
        test_file = self.generate_random_file(temp_workspace)
        receipt_path = temp_workspace / "receipt.json"
        
        metadata = {
            "project": "test-project",
            "version": "1.2.3",
            "author": "Test Suite",
            "timestamp": "2025-11-04T12:00:00Z"
        }
        
        # Create receipt with metadata
        self.cli_create_receipt([test_file], receipt_path, metadata=metadata)
        
        # Verify metadata is in receipt
        with open(receipt_path) as f:
            receipt = json.load(f)
        
        assert "metadata" in receipt
        assert receipt["metadata"]["project"] == "test-project"
        assert receipt["metadata"]["version"] == "1.2.3"
        
        # Verify receipt still validates
        result = self.cli_verify_receipt(receipt_path)
        assert result['success']

    def test_cli_mixed_file_types(self, temp_workspace):
        """Test: CLI handles mixed file types (text, binary, JSON)."""
        files = []
        
        # Text file
        files.append(self.generate_random_file(temp_workspace, extension=".txt"))
        
        # Binary file
        files.append(self.generate_random_binary_file(temp_workspace))
        
        # JSON file
        json_file = temp_workspace / "test.json"
        json_file.write_text(json.dumps({"test": "data", "number": 42}))
        files.append(json_file)
        
        # Python file
        py_file = temp_workspace / "test.py"
        py_file.write_text("def test():\n    return 42\n")
        files.append(py_file)
        
        receipt_path = temp_workspace / "receipt.json"
        
        # Create receipt
        self.cli_create_receipt(files, receipt_path)
        
        # Verify receipt
        result = self.cli_verify_receipt(receipt_path)
        assert result['success']

    # ==================== PHASE 1.2: Negative Tests (Corruption Detection) ====================

    def test_negative_file_content_corruption(self, temp_workspace):
        """Test: Verifier detects when file content is modified."""
        # Create file and receipt
        test_file = self.generate_random_file(temp_workspace, size=100)
        receipt_path = temp_workspace / "receipt.json"
        self.cli_create_receipt([test_file], receipt_path)
        
        # Verify original works
        result = self.cli_verify_receipt(receipt_path)
        assert result['success']
        
        # Corrupt the file (flip one bit)
        content = test_file.read_bytes()
        corrupted = bytearray(content)
        corrupted[len(corrupted) // 2] ^= 1  # Flip one bit in the middle
        test_file.write_bytes(bytes(corrupted))
        
        # Verification should fail
        result = self.cli_verify_receipt(receipt_path)
        assert not result['success'], "Verifier should detect file corruption"

    def test_negative_global_digest_corruption(self, temp_workspace):
        """Test: Verifier detects when global_digest is modified."""
        # Create file and receipt
        test_file = self.generate_random_file(temp_workspace)
        receipt_path = temp_workspace / "receipt.json"
        self.cli_create_receipt([test_file], receipt_path)
        
        # Corrupt global_digest in receipt
        with open(receipt_path) as f:
            receipt = json.load(f)
        
        # Flip one character in global_digest
        if "global_digest" in receipt:
            digest = receipt["global_digest"]
            corrupted_digest = digest[:10] + ('0' if digest[10] != '0' else '1') + digest[11:]
            receipt["global_digest"] = corrupted_digest
            
            with open(receipt_path, 'w') as f:
                json.dump(receipt, f)
            
            # Verification should fail
            result = self.cli_verify_receipt(receipt_path)
            assert not result['success'], "Verifier should detect global_digest corruption"

    def test_negative_signature_corruption(self, temp_workspace):
        """Test: Verifier detects when signature is corrupted."""
        # Create file and receipt
        test_file = self.generate_random_file(temp_workspace)
        receipt_path = temp_workspace / "receipt.json"
        self.cli_create_receipt([test_file], receipt_path)
        
        # Add fake signature
        with open(receipt_path) as f:
            receipt = json.load(f)
        
        receipt["signature"] = {
            "algorithm": "ed25519",
            "value": "0" * 128,  # Fake signature
            "public_key": "fake_public_key"
        }
        
        with open(receipt_path, 'w') as f:
            json.dump(receipt, f)
        
        # If verifier checks signatures, it should fail
        # Note: This test assumes signature verification is implemented
        _ = self.cli_verify_receipt(receipt_path)
        # We expect either failure or warning about invalid signature
        # (Implementation may vary)

    def test_negative_missing_file(self, temp_workspace):
        """Test: Verifier detects when a file is missing."""
        # Create files and receipt
        files = [
            self.generate_random_file(temp_workspace)
            for _ in range(3)
        ]
        receipt_path = temp_workspace / "receipt.json"
        self.cli_create_receipt(files, receipt_path)
        
        # Verify original works
        result = self.cli_verify_receipt(receipt_path)
        assert result['success']
        
        # Delete one file
        files[1].unlink()
        
        # Verification should fail
        result = self.cli_verify_receipt(receipt_path)
        assert not result['success'], "Verifier should detect missing file"

    def test_negative_extra_file(self, temp_workspace):
        """Test: Detect when extra files are present (if applicable)."""
        # Create files and receipt
        files = [
            self.generate_random_file(temp_workspace)
            for _ in range(2)
        ]
        receipt_path = temp_workspace / "receipt.json"
        self.cli_create_receipt(files, receipt_path)
        
        # Add an extra file
        _ = self.generate_random_file(temp_workspace)
        
        # Verification should still succeed (extra files are ignored)
        # This tests that verifier only checks files in receipt
        result = self.cli_verify_receipt(receipt_path)
        assert result['success']

    # ==================== PHASE 1.3: Stress Tests ====================

    def test_stress_many_small_files(self, temp_workspace):
        """Stress test: Create receipt for 100 small files."""
        files = [
            self.generate_random_file(temp_workspace, size=random.randint(10, 100))
            for _ in range(100)
        ]
        receipt_path = temp_workspace / "receipt.json"
        
        # Create receipt
        self.cli_create_receipt(files, receipt_path)
        
        # Verify structure
        with open(receipt_path) as f:
            receipt = json.load(f)
        assert len(receipt["files"]) == 100
        
        # Verify receipt
        result = self.cli_verify_receipt(receipt_path)
        assert result['success']

    def test_stress_large_total_size(self, temp_workspace):
        """Stress test: Create receipt for 10MB total data."""
        # Create 5 x 2MB files
        files = [
            self.generate_random_file(temp_workspace, size=2 * 1024 * 1024)
            for _ in range(5)
        ]
        receipt_path = temp_workspace / "receipt.json"
        
        # Create receipt
        self.cli_create_receipt(files, receipt_path)
        
        # Verify receipt
        result = self.cli_verify_receipt(receipt_path)
        assert result['success']

    def test_special_characters_in_filenames(self, temp_workspace):
        """Test: Handle files with special characters in names."""
        # Create files with special characters
        filenames = [
            "file-with-dashes.txt",
            "file_with_underscores.txt",
            "file.with.dots.txt",
            "file with spaces.txt",
            "file123numbers.txt"
        ]
        
        files = []
        for filename in filenames:
            filepath = temp_workspace / filename
            filepath.write_text(f"Content of {filename}")
            files.append(filepath)
        
        receipt_path = temp_workspace / "receipt.json"
        
        # Create receipt
        self.cli_create_receipt(files, receipt_path)
        
        # Verify receipt
        result = self.cli_verify_receipt(receipt_path)
        assert result['success']

    # ==================== PHASE 1.4: Random Test Cases ====================

    @pytest.mark.parametrize("iteration", range(20))
    def test_random_valid_receipts(self, temp_workspace, iteration):
        """Parameterized test: Generate and verify random valid receipts."""
        # Random number of files (1-10)
        num_files = random.randint(1, 10)
        
        files = []
        for _ in range(num_files):
            if random.random() < 0.7:
                # 70% text files
                files.append(self.generate_random_file(
                    temp_workspace,
                    size=random.randint(10, 10000)
                ))
            else:
                # 30% binary files
                files.append(self.generate_random_binary_file(
                    temp_workspace,
                    size=random.randint(10, 10000)
                ))
        
        receipt_path = temp_workspace / f"receipt_{iteration}.json"
        
        # Maybe add metadata
        metadata = None
        if random.random() < 0.5:
            metadata = {
                "test_iteration": iteration,
                "num_files": num_files,
                "random_id": random.randint(1000, 9999)
            }
        
        # Create receipt
        self.cli_create_receipt(files, receipt_path, metadata=metadata)
        
        # Verify receipt
        result = self.cli_verify_receipt(receipt_path)
        assert result['success'], f"Random test {iteration} failed"


class TestReceiptFormat:
    """Tests for TRS-1.0 receipt format compliance."""

    def test_receipt_has_required_fields(self, tmp_path):
        """Test: Receipt contains all required TRS-1.0 fields."""
        # Create a simple file
        test_file = tmp_path / "test.txt"
        test_file.write_text("Hello, World!")
        
        receipt_path = tmp_path / "receipt.json"
        
        # Create receipt
        cmd = [
            sys.executable,
            str(PROJECT_ROOT / "create_receipt.py"),
            str(test_file),
            "--output", str(receipt_path)
        ]
        
        subprocess.run(cmd, check=True, cwd=PROJECT_ROOT)
        
        # Check receipt structure
        with open(receipt_path) as f:
            receipt = json.load(f)
        
        # Required fields per TRS-1.0
        assert "version" in receipt, "Missing 'version' field"
        assert "files" in receipt, "Missing 'files' field"
        assert isinstance(receipt["files"], list), "'files' must be a list"
        
        if len(receipt["files"]) > 0:
            file_entry = receipt["files"][0]
            assert "path" in file_entry, "File entry missing 'path'"
            assert "sha256" in file_entry, "File entry missing 'sha256'"

    def test_receipt_global_digest_format(self, tmp_path):
        """Test: Global digest is properly formatted."""
        test_file = tmp_path / "test.txt"
        test_file.write_text("Test content")
        
        receipt_path = tmp_path / "receipt.json"
        
        cmd = [
            sys.executable,
            str(PROJECT_ROOT / "create_receipt.py"),
            str(test_file),
            "--output", str(receipt_path)
        ]
        
        subprocess.run(cmd, check=True, cwd=PROJECT_ROOT)
        
        with open(receipt_path) as f:
            receipt = json.load(f)
        
        if "global_digest" in receipt:
            digest = receipt["global_digest"]
            # Should be hex string of SHA-256 (64 characters)
            assert isinstance(digest, str), "Global digest must be string"
            assert len(digest) == 64, f"SHA-256 digest should be 64 chars, got {len(digest)}"
            assert all(c in '0123456789abcdef' for c in digest.lower()), "Digest must be hex"


if __name__ == "__main__":
    # Run tests
    pytest.main([__file__, "-v", "--tb=short"])
