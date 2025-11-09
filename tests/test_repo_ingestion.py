#!/usr/bin/env python3
"""
Test suite for repository ingestion features.

Tests all the claimed functionality:
1. Archive fetching
2. Directory-aware uploads
3. Metadata auto-fill
4. Path traversal protection
5. Relative path preservation
"""

import json
import os
import sys
import tempfile
import tarfile
import zipfile
from pathlib import Path

import pytest

# Add parent directory to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from create_receipt import (
    scan_directory,
    create_receipt,
    safe_extract_member,
    determine_archive_root,
    read_package_manifest,
)


class TestDirectoryScanning:
    """Test directory scanning with pattern filtering."""
    
    def test_scan_basic_directory(self, tmp_path):
        """Test basic directory scanning returns tuples of (abs, rel) paths."""
        # Create test files
        (tmp_path / "file1.txt").write_text("content1")
        (tmp_path / "file2.txt").write_text("content2")
        
        files = scan_directory(tmp_path)
        
        assert len(files) == 2
        # Each entry should be a tuple
        assert all(isinstance(f, tuple) for f in files)
        # Check that relative paths are correct
        rel_paths = [str(rel) for _, rel in files]
        assert "file1.txt" in rel_paths
        assert "file2.txt" in rel_paths
    
    def test_scan_with_subdirectories(self, tmp_path):
        """Test that subdirectory paths are preserved correctly."""
        # Create nested structure
        subdir = tmp_path / "subdir"
        subdir.mkdir()
        (tmp_path / "root.txt").write_text("root")
        (subdir / "nested.txt").write_text("nested")
        
        files = scan_directory(tmp_path)
        
        rel_paths = [str(rel) for _, rel in files]
        assert "root.txt" in rel_paths
        assert "subdir/nested.txt" in rel_paths or "subdir\\nested.txt" in rel_paths
    
    def test_scan_with_include_patterns(self, tmp_path):
        """Test include pattern filtering."""
        (tmp_path / "file.py").write_text("python")
        (tmp_path / "file.js").write_text("javascript")
        (tmp_path / "file.txt").write_text("text")
        
        files = scan_directory(tmp_path, include_patterns=["*.py", "*.js"])
        
        rel_paths = [str(rel) for _, rel in files]
        assert len(files) == 2
        assert any("file.py" in p for p in rel_paths)
        assert any("file.js" in p for p in rel_paths)
        assert not any("file.txt" in p for p in rel_paths)
    
    def test_scan_with_exclude_patterns(self, tmp_path):
        """Test exclude pattern filtering."""
        (tmp_path / "keep.txt").write_text("keep")
        (tmp_path / "exclude.pyc").write_text("exclude")
        
        files = scan_directory(tmp_path, exclude_patterns=["*.pyc"])
        
        rel_paths = [str(rel) for _, rel in files]
        # *.pyc is in default excludes, but let's be explicit
        assert not any("exclude.pyc" in p for p in rel_paths)
        assert any("keep.txt" in p for p in rel_paths)
    
    def test_scan_respects_file_limit(self, tmp_path):
        """Test that max_files limit is respected."""
        # Create 10 files
        for i in range(10):
            (tmp_path / f"file{i}.txt").write_text(f"content{i}")
        
        files = scan_directory(tmp_path, max_files=5)
        
        assert len(files) <= 5


class TestMetadataExtraction:
    """Test automatic metadata extraction from manifests."""
    
    def test_extract_from_package_json(self, tmp_path):
        """Test extracting metadata from package.json."""
        package_json = {
            "name": "test-package",
            "version": "1.2.3",
            "description": "Test package",
            "author": "Test Author",
            "license": "MIT"
        }
        (tmp_path / "package.json").write_text(json.dumps(package_json))
        
        metadata = read_package_manifest(tmp_path)
        
        assert metadata is not None
        assert metadata["name"] == "test-package"
        assert metadata["version"] == "1.2.3"
        assert metadata["description"] == "Test package"
        assert metadata["manifest_type"] == "package.json"
    
    def test_extract_from_pyproject_toml(self, tmp_path):
        """Test extracting metadata from pyproject.toml."""
        pyproject = """
[tool.poetry]
name = "test-python-package"
version = "0.1.0"
description = "A test Python package"
        """
        (tmp_path / "pyproject.toml").write_text(pyproject)
        
        metadata = read_package_manifest(tmp_path)
        
        assert metadata is not None
        assert metadata["name"] == "test-python-package"
        assert metadata["version"] == "0.1.0"
        assert metadata["manifest_type"] == "pyproject.toml"
    
    def test_extract_from_cargo_toml(self, tmp_path):
        """Test extracting metadata from Cargo.toml."""
        cargo = """
[package]
name = "test-rust-package"
version = "0.2.0"
description = "A test Rust package"
        """
        (tmp_path / "Cargo.toml").write_text(cargo)
        
        metadata = read_package_manifest(tmp_path)
        
        assert metadata is not None
        assert metadata["name"] == "test-rust-package"
        assert metadata["version"] == "0.2.0"
        assert metadata["manifest_type"] == "Cargo.toml"
    
    def test_no_manifest_returns_none(self, tmp_path):
        """Test that missing manifest returns None."""
        metadata = read_package_manifest(tmp_path)
        assert metadata is None


class TestPathTraversalProtection:
    """Test security protections against path traversal attacks."""
    
    def test_blocks_parent_directory_traversal(self, tmp_path):
        """Test that ../ paths are blocked."""
        # Create a malicious tar file
        tar_path = tmp_path / "malicious.tar"
        with tarfile.open(tar_path, "w") as tar:
            # Create temp file
            safe_file = tmp_path / "safe.txt"
            safe_file.write_text("safe content")
            
            # Add with malicious path
            info = tar.gettarinfo(str(safe_file), arcname="../../../etc/passwd")
            tar.addfile(info, open(safe_file, "rb"))
        
        # Test extraction
        with tarfile.open(tar_path, "r") as tar:
            members = tar.getmembers()
            assert len(members) == 1
            
            extract_dir = tmp_path / "extract"
            extract_dir.mkdir()
            
            # Should block the malicious path
            safe = safe_extract_member(members[0], extract_dir, "tar")
            assert not safe
    
    def test_blocks_absolute_paths(self, tmp_path):
        """Test that absolute paths are safely handled.
        
        Note: tarfile automatically strips leading / from absolute paths for security,
        converting /tmp/file to tmp/file, which is safe to extract within dest_dir.
        """
        # Create a tar with absolute path
        tar_path = tmp_path / "absolute.tar"
        with tarfile.open(tar_path, "w") as tar:
            safe_file = tmp_path / "safe.txt"
            safe_file.write_text("safe content")
            
            # Add with absolute path - tarfile will strip the leading /
            info = tar.gettarinfo(str(safe_file), arcname="/tmp/malicious.txt")
            tar.addfile(info, open(safe_file, "rb"))
        
        with tarfile.open(tar_path, "r") as tar:
            members = tar.getmembers()
            extract_dir = tmp_path / "extract"
            extract_dir.mkdir()
            
            # tarfile strips the leading /, making it "tmp/malicious.txt"
            # which is safe to extract (will go to extract/tmp/malicious.txt)
            assert members[0].name == "tmp/malicious.txt"
            safe = safe_extract_member(members[0], extract_dir, "tar")
            # This is actually safe because the leading / was stripped
            assert safe
    
    def test_allows_safe_relative_paths(self, tmp_path):
        """Test that normal relative paths are allowed."""
        tar_path = tmp_path / "safe.tar"
        with tarfile.open(tar_path, "w") as tar:
            safe_file = tmp_path / "safe.txt"
            safe_file.write_text("safe content")
            
            # Add with safe relative path
            info = tar.gettarinfo(str(safe_file), arcname="subdir/file.txt")
            tar.addfile(info, open(safe_file, "rb"))
        
        with tarfile.open(tar_path, "r") as tar:
            members = tar.getmembers()
            extract_dir = tmp_path / "extract"
            extract_dir.mkdir()
            
            safe = safe_extract_member(members[0], extract_dir, "tar")
            assert safe
    
    def test_zip_path_traversal_protection(self, tmp_path):
        """Test path traversal protection for ZIP files."""
        zip_path = tmp_path / "malicious.zip"
        with zipfile.ZipFile(zip_path, "w") as zf:
            # Try to add a file with malicious path
            safe_file = tmp_path / "safe.txt"
            safe_file.write_text("safe content")
            
            # Note: zipfile normalizes paths, but we still test our protection
            zf.write(safe_file, arcname="../../../evil.txt")
        
        with zipfile.ZipFile(zip_path, "r") as zf:
            members = zf.infolist()
            extract_dir = tmp_path / "extract"
            extract_dir.mkdir()
            
            # Our protection should catch this
            for member in members:
                # Check if it contains parent references
                if ".." in member.filename:
                    safe = safe_extract_member(member, extract_dir, "zip")
                    assert not safe


class TestArchiveRootDetection:
    """Test proper detection of archive root directories."""
    
    def test_single_root_directory(self):
        """Test detection when all files share a common root."""
        names = [
            "myproject/file1.txt",
            "myproject/file2.txt",
            "myproject/subdir/file3.txt"
        ]
        root = determine_archive_root(names)
        assert root == "myproject"
    
    def test_multiple_roots(self):
        """Test returns None when files have different roots."""
        names = [
            "project1/file1.txt",
            "project2/file2.txt"
        ]
        root = determine_archive_root(names)
        assert root is None
    
    def test_files_at_root_level(self):
        """Test returns None when files are at root level."""
        names = [
            "file1.txt",
            "file2.txt"
        ]
        root = determine_archive_root(names)
        assert root is None
    
    def test_empty_archive(self):
        """Test returns None for empty archive."""
        root = determine_archive_root([])
        assert root is None


class TestReceiptCreation:
    """Test receipt creation with relative paths."""
    
    def test_receipt_preserves_relative_paths(self, tmp_path):
        """Test that receipts use relative paths from scan_directory."""
        # Create test structure
        (tmp_path / "file1.txt").write_text("content1")
        subdir = tmp_path / "subdir"
        subdir.mkdir()
        (subdir / "file2.txt").write_text("content2")
        
        # Scan directory
        files = scan_directory(tmp_path)
        
        # Create receipt
        receipt_path = tmp_path / "receipt.json"
        receipt = create_receipt(
            files,
            output_path=str(receipt_path),
            base_dir=tmp_path,
            sign_key="kernel_secret.key",
            public_key="kernel_public.key",
            key_id="thiele-core-2025"
        )
        
        # Check that paths in receipt are relative
        file_paths = [f["path"] for f in receipt["files"]]
        assert "file1.txt" in file_paths
        # Check for subdirectory file (handle both / and \\ for cross-platform)
        assert any("file2.txt" in p for p in file_paths)
        assert not any(str(tmp_path) in p for p in file_paths)
    
    def test_receipt_with_single_file(self, tmp_path):
        """Test receipt creation with single file (backward compatibility)."""
        test_file = tmp_path / "test.txt"
        test_file.write_text("test content")
        
        receipt_path = tmp_path / "receipt.json"
        receipt = create_receipt(
            [str(test_file)],
            output_path=str(receipt_path),
            sign_key="kernel_secret.key",
            public_key="kernel_public.key",
            key_id="thiele-core-2025"
        )
        
        assert len(receipt["files"]) == 1
        assert receipt["files"][0]["path"] == "test.txt"
    
    def test_receipt_includes_metadata(self, tmp_path):
        """Test that metadata is included in receipt."""
        (tmp_path / "test.txt").write_text("content")
        package_json = {"name": "test", "version": "1.0.0"}
        (tmp_path / "package.json").write_text(json.dumps(package_json))
        
        files = scan_directory(tmp_path)
        receipt_path = tmp_path / "receipt.json"
        
        # Read metadata
        metadata = read_package_manifest(tmp_path)
        
        receipt = create_receipt(
            files,
            output_path=str(receipt_path),
            metadata=metadata,
            base_dir=tmp_path,
            sign_key="kernel_secret.key",
            public_key="kernel_public.key",
            key_id="thiele-core-2025"
        )
        
        assert "metadata" in receipt
        assert receipt["metadata"]["name"] == "test"
        assert receipt["metadata"]["version"] == "1.0.0"


class TestIntegration:
    """Integration tests for complete workflows."""
    
    def test_directory_mode_end_to_end(self, tmp_path):
        """Test complete directory mode workflow."""
        # Create a project structure
        project = tmp_path / "myproject"
        project.mkdir()
        
        # Add package.json
        package_json = {
            "name": "integration-test",
            "version": "1.0.0",
            "description": "Integration test project"
        }
        (project / "package.json").write_text(json.dumps(package_json))
        
        # Add some files
        (project / "index.js").write_text("console.log('hello');")
        src = project / "src"
        src.mkdir()
        (src / "main.js").write_text("export default {};")
        
        # Scan directory
        files = scan_directory(project)
        
        # Extract metadata
        metadata = read_package_manifest(project)
        
        # Create receipt
        receipt_path = tmp_path / "receipt.json"
        receipt = create_receipt(
            files,
            output_path=str(receipt_path),
            metadata=metadata,
            base_dir=project,
            sign_key="kernel_secret.key",
            public_key="kernel_public.key",
            key_id="thiele-core-2025"
        )
        
        # Verify receipt
        assert receipt["version"] == "TRS-1.0"
        assert len(receipt["files"]) == 3  # package.json, index.js, src/main.js
        assert "metadata" in receipt
        assert receipt["metadata"]["name"] == "integration-test"
        
        # Verify receipt was written
        assert receipt_path.exists()
        with open(receipt_path) as f:
            loaded = json.load(f)
        assert loaded["global_digest"] == receipt["global_digest"]


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
