# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

"""Tests for web demos to ensure they work correctly."""

import json
import os
from pathlib import Path

import pytest


# Path to web demos directory
WEB_DEMOS_DIR = Path(__file__).parent.parent / "web" / "demos"


class TestWebDemos:
    """Test suite for web demonstration pages."""
    
    def test_demos_directory_exists(self):
        """Verify the web/demos directory exists."""
        assert WEB_DEMOS_DIR.exists(), f"Demos directory not found at {WEB_DEMOS_DIR}"
        assert WEB_DEMOS_DIR.is_dir(), f"{WEB_DEMOS_DIR} is not a directory"
    
    def test_demo_html_files_exist(self):
        """Verify all required HTML demo files exist."""
        required_files = [
            "index.html",
            "install.html",
            "zk.html",
            "trusting-trust.html"
        ]
        
        for filename in required_files:
            filepath = WEB_DEMOS_DIR / filename
            assert filepath.exists(), f"Required demo file {filename} not found"
            assert filepath.stat().st_size > 0, f"{filename} is empty"
    
    def test_install_js_exists(self):
        """Verify install.js file exists for the install demo."""
        install_js = WEB_DEMOS_DIR / "install.js"
        assert install_js.exists(), "install.js not found"
        assert install_js.stat().st_size > 0, "install.js is empty"
    
    def test_sample_data_files_exist(self):
        """Verify sample data files exist for demos."""
        sample_files = [
            "sample-receipt.json",
            "sample-zkproof.json",
            "sample-gcc-receipt.json",
            "sample-clang-receipt.json"
        ]
        
        for filename in sample_files:
            filepath = WEB_DEMOS_DIR / filename
            assert filepath.exists(), f"Sample file {filename} not found"
            assert filepath.stat().st_size > 0, f"{filename} is empty"
    
    def test_sample_receipt_json_valid(self):
        """Verify sample-receipt.json is valid JSON."""
        filepath = WEB_DEMOS_DIR / "sample-receipt.json"
        with open(filepath, 'r') as f:
            data = json.load(f)
        
        # Verify required fields
        assert "version" in data, "Missing 'version' field"
        assert "files" in data, "Missing 'files' field"
        assert isinstance(data["files"], list), "'files' should be a list"
        assert len(data["files"]) > 0, "'files' should not be empty"
    
    def test_sample_zkproof_json_valid(self):
        """Verify sample-zkproof.json is valid JSON."""
        filepath = WEB_DEMOS_DIR / "sample-zkproof.json"
        with open(filepath, 'r') as f:
            data = json.load(f)
        
        # Verify required ZK proof fields
        assert "version" in data, "Missing 'version' field"
        assert data["version"] == "TRS-ZK-1", "Invalid version for ZK proof"
        assert "manifest_sha256" in data, "Missing 'manifest_sha256' field"
        assert "merkle_root" in data, "Missing 'merkle_root' field"
        assert "zk_receipt" in data, "Missing 'zk_receipt' field"
        assert "files" in data, "Missing 'files' field"
    
    def test_sample_compiler_receipts_valid(self):
        """Verify compiler receipt samples are valid JSON."""
        for compiler in ["gcc", "clang"]:
            filepath = WEB_DEMOS_DIR / f"sample-{compiler}-receipt.json"
            with open(filepath, 'r') as f:
                data = json.load(f)
            
            # Verify compiler-specific fields
            assert "compiler" in data, f"Missing 'compiler' field in {compiler} receipt"
            assert data["compiler"] == compiler, f"Incorrect compiler field in {compiler} receipt"
            assert "files" in data, f"Missing 'files' field in {compiler} receipt"
            assert any(f["path"] == "toycc" for f in data["files"]), f"Missing toycc in {compiler} receipt"
    
    def test_compiler_receipts_have_matching_hashes(self):
        """Verify GCC and Clang receipts produce matching binary hashes (for demo)."""
        gcc_path = WEB_DEMOS_DIR / "sample-gcc-receipt.json"
        clang_path = WEB_DEMOS_DIR / "sample-clang-receipt.json"
        
        with open(gcc_path, 'r') as f:
            gcc_data = json.load(f)
        with open(clang_path, 'r') as f:
            clang_data = json.load(f)
        
        # Find the toycc binary in both receipts
        gcc_binary = next((f for f in gcc_data["files"] if f["path"] == "toycc"), None)
        clang_binary = next((f for f in clang_data["files"] if f["path"] == "toycc"), None)
        
        assert gcc_binary is not None, "toycc not found in GCC receipt"
        assert clang_binary is not None, "toycc not found in Clang receipt"
        
        # They should have the same SHA256 (demonstrating trusting trust success)
        assert gcc_binary["sha256"] == clang_binary["sha256"], \
            "GCC and Clang should produce identical binaries in the demo"
    
    def test_index_html_links_to_demos(self):
        """Verify index.html contains links to all demos."""
        index_path = WEB_DEMOS_DIR / "index.html"
        with open(index_path, 'r') as f:
            content = f.read()
        
        # Check for links to each demo
        assert 'href="install.html"' in content, "index.html missing link to install demo"
        assert 'href="zk.html"' in content, "index.html missing link to zk demo"
        assert 'href="trusting-trust.html"' in content, "index.html missing link to trusting-trust demo"
        
        # Check for sample data links
        assert 'sample-receipt.json' in content, "index.html missing reference to sample-receipt.json"
        assert 'sample-zkproof.json' in content, "index.html missing reference to sample-zkproof.json"
    
    def test_html_files_have_proper_structure(self):
        """Verify HTML files have proper structure (DOCTYPE, html, head, body)."""
        html_files = ["index.html", "install.html", "zk.html", "trusting-trust.html"]
        
        for filename in html_files:
            filepath = WEB_DEMOS_DIR / filename
            with open(filepath, 'r') as f:
                content = f.read()
            
            # Basic HTML structure checks
            assert '<!DOCTYPE html>' in content or '<!doctype html>' in content.lower(), \
                f"{filename} missing DOCTYPE declaration"
            assert '<html' in content.lower(), f"{filename} missing html tag"
            assert '<head>' in content.lower() or '<head ' in content.lower(), \
                f"{filename} missing head tag"
            assert '<body>' in content.lower() or '<body ' in content.lower(), \
                f"{filename} missing body tag"
            assert '<title>' in content.lower(), f"{filename} missing title tag"
    
    def test_demos_reference_github_repo(self):
        """Verify demos contain reference to the GitHub repository."""
        html_files = ["index.html", "install.html", "zk.html", "trusting-trust.html"]
        
        for filename in html_files:
            filepath = WEB_DEMOS_DIR / filename
            with open(filepath, 'r') as f:
                content = f.read()
            
            assert 'github.com/sethirus/The-Thiele-Machine' in content, \
                f"{filename} should reference the GitHub repository"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
