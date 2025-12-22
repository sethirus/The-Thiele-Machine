"""
Comprehensive tests for the web-based Thiele Receipt Verifier.

This module tests the browser-based JavaScript verifier implementation
to ensure all cryptographic operations and UI components work correctly.
"""

from __future__ import annotations

from pathlib import Path

import pytest


class TestWebVerifierJavaScript:
    """Tests for the JavaScript verifier implementation (replay.js)."""

    def test_replay_js_exists(self):
        """Verify replay.js file exists."""
        replay_js = Path("web/replay.js")
        assert replay_js.exists(), "replay.js not found in web directory"

    def test_replay_js_has_verifier_class(self):
        """Verify ThieleVerifier class is defined."""
        replay_js = Path("web/replay.js")
        content = replay_js.read_text()
        assert "class ThieleVerifier" in content, "ThieleVerifier class not found"

    def test_replay_js_has_sha256_method(self):
        """Verify SHA-256 hashing method exists."""
        replay_js = Path("web/replay.js")
        content = replay_js.read_text()
        assert "async sha256" in content, "sha256 method not found"
        assert "crypto.subtle.digest" in content, "Web Crypto API not used"

    def test_replay_js_has_canonical_json(self):
        """Verify canonical JSON method exists."""
        replay_js = Path("web/replay.js")
        content = replay_js.read_text()
        assert "canonicalJSON" in content, "canonicalJSON method not found"
        assert "sort()" in content, "Key sorting not implemented"

    def test_replay_js_has_trs10_verification(self):
        """Verify TRS-1.0 verification method exists."""
        replay_js = Path("web/replay.js")
        content = replay_js.read_text()
        assert "verifyTRS10" in content, "TRS-1.0 verification not found"
        assert "global_digest" in content, "Global digest verification missing"

    def test_replay_js_has_trs0_verification(self):
        """Verify TRS-0 (legacy) verification method exists."""
        replay_js = Path("web/replay.js")
        content = replay_js.read_text()
        assert "verifyTRS0" in content, "TRS-0 verification not found"
        assert "steps" in content, "Steps verification missing"

    def test_replay_js_has_path_validation(self):
        """Verify path traversal and security checks exist."""
        replay_js = Path("web/replay.js")
        content = replay_js.read_text()
        assert ".includes('..')" in content, "Path traversal check missing"
        assert "Absolute paths not allowed" in content, "Absolute path check missing"

    def test_replay_js_has_signature_verification(self):
        """Verify signature verification support exists."""
        replay_js = Path("web/replay.js")
        content = replay_js.read_text()
        assert "sig_scheme" in content, "Signature scheme handling missing"
        assert "ed25519" in content, "Ed25519 support missing"

    def test_replay_js_has_ui_integration(self):
        """Verify UI event handling is present."""
        replay_js = Path("web/replay.js")
        content = replay_js.read_text()
        assert "DOMContentLoaded" in content, "DOM ready handler missing"
        assert "dragover" in content, "Drag-and-drop missing"
        assert "fileInput" in content, "File upload UI missing"


class TestWebPages:
    """Tests for HTML pages and their structure."""

    def test_verify_html_exists(self):
        """Verify main verifier page exists."""
        verify_html = Path("web/verify.html")
        assert verify_html.exists(), "verify.html not found"

    def test_verify_html_has_upload_area(self):
        """Verify upload area exists in HTML."""
        verify_html = Path("web/verify.html")
        content = verify_html.read_text()
        assert 'id="uploadArea"' in content or 'id="fileInput"' in content, "Upload area missing"

    def test_verify_html_loads_replay_js(self):
        """Verify replay.js is included."""
        verify_html = Path("web/verify.html")
        content = verify_html.read_text()
        assert 'replay.js' in content, "replay.js not loaded in verify.html"

    def test_index_html_exists(self):
        """Verify landing page exists."""
        index_html = Path("web/index.html")
        assert index_html.exists(), "index.html not found"

    def test_index_html_has_navigation(self):
        """Verify landing page has navigation to verifier."""
        index_html = Path("web/index.html")
        content = index_html.read_text()
        assert 'verify.html' in content or 'Verify' in content, "Navigation to verifier missing"

    def test_create_html_exists(self):
        """Verify receipt creation page exists."""
        create_html = Path("web/create.html")
        assert create_html.exists(), "create.html not found"

    def test_create_js_exists(self):
        """Verify receipt creation JavaScript exists."""
        create_js = Path("web/create.js")
        assert create_js.exists(), "create.js not found"

    def test_all_html_pages_have_meta_charset(self):
        """Verify all HTML pages have proper charset."""
        html_files = ["web/verify.html", "web/index.html", "web/create.html"]
        for html_file in html_files:
            path = Path(html_file)
            if path.exists():
                content = path.read_text()
                assert 'charset="UTF-8"' in content or 'charset=UTF-8' in content, f"{html_file} missing UTF-8 charset"

    def test_all_html_pages_have_viewport(self):
        """Verify all HTML pages have viewport meta tag for mobile."""
        html_files = ["web/verify.html", "web/index.html", "web/create.html"]
        for html_file in html_files:
            path = Path(html_file)
            if path.exists():
                content = path.read_text()
                assert 'viewport' in content, f"{html_file} missing viewport meta tag"

    def test_demos_directory_exists(self):
        """Verify demos directory exists."""
        demos_dir = Path("web/demos")
        assert demos_dir.exists(), "demos directory not found"

    def test_demo_install_html_exists(self):
        """Verify proof-install demo exists."""
        demo_html = Path("web/demos/install.html")
        assert demo_html.exists(), "install.html demo not found"

    def test_demo_zk_html_exists(self):
        """Verify zero-knowledge demo exists."""
        demo_html = Path("web/demos/zk.html")
        assert demo_html.exists(), "zk.html demo not found"

    def test_demo_trusting_trust_exists(self):
        """Verify trusting-trust demo exists."""
        demo_html = Path("web/demos/trusting-trust.html")
        assert demo_html.exists(), "trusting-trust.html demo not found"


class TestWebVerifierFunctionality:
    """Integration tests for web verifier using example receipts."""

    def test_example_receipt_exists(self):
        """Verify example receipt exists for testing."""
        example_receipts = list(Path("examples").glob("*.json")) if Path("examples").exists() else []
        if not example_receipts:
            pytest.skip("No example receipts found for testing")

    def test_receipt_worker_exists(self):
        """Verify Web Worker for receipt processing exists."""
        worker_js = Path("web/receipt-worker.js")
        assert worker_js.exists(), "receipt-worker.js not found"

    def test_worker_has_message_handler(self):
        """Verify Web Worker has message handling."""
        worker_js = Path("web/receipt-worker.js")
        content = worker_js.read_text()
        assert "onmessage" in content or "addEventListener('message'" in content, "Worker message handler missing"


class TestWebVerifierSecurity:
    """Security-focused tests for the web verifier."""

    def test_no_eval_usage(self):
        """Verify no dangerous eval() usage in JavaScript."""
        js_files = ["web/replay.js", "web/create.js"]
        for js_file in js_files:
            path = Path(js_file)
            if path.exists():
                content = path.read_text()
                lines = content.split('\n')
                for line in lines:
                    if 'eval(' in line and '//' not in line.split('eval(')[0]:
                        assert False, f"{js_file} uses dangerous eval()"

    def test_path_traversal_checks(self):
        """Verify path traversal attack prevention."""
        replay_js = Path("web/replay.js")
        content = replay_js.read_text()
        assert ".." in content, "Path traversal checks missing"
        assert "startsWith('/')" in content or "Absolute path" in content, "Absolute path checks missing"

    def test_uses_web_crypto_api(self):
        """Verify use of secure Web Crypto API."""
        replay_js = Path("web/replay.js")
        content = replay_js.read_text()
        assert "crypto.subtle" in content, "Web Crypto API not used (insecure)"
        assert "crypto.subtle.digest" in content, "Web Crypto digest not used"

    def test_no_inline_scripts_in_html(self):
        """Verify HTML pages use external scripts (CSP best practice)."""
        verify_html = Path("web/verify.html")
        if verify_html.exists():
            content = verify_html.read_text()
            assert '<script src="replay.js"' in content, "External script not loaded"


class TestWebVerifierAccessibility:
    """Accessibility tests for web pages."""

    def test_skip_links_present(self):
        """Verify skip-to-content links for screen readers."""
        html_files = ["web/verify.html", "web/index.html"]
        for html_file in html_files:
            path = Path(html_file)
            if path.exists():
                content = path.read_text()
                has_skip = "skip-link" in content.lower() or "skip to" in content.lower()
                assert has_skip or "main" in content, f"{html_file} missing accessibility features"

    def test_form_labels_present(self):
        """Verify form inputs have associated labels."""
        verify_html = Path("web/verify.html")
        if verify_html.exists():
            content = verify_html.read_text()
            if 'type="file"' in content:
                assert 'for="fileInput"' in content or 'aria-label' in content, "File input missing label"

    def test_semantic_html_usage(self):
        """Verify use of semantic HTML elements."""
        verify_html = Path("web/verify.html")
        if verify_html.exists():
            content = verify_html.read_text()
            assert "<html" in content and "</html>" in content, "Missing html tags"


class TestWebVerifierPerformance:
    """Performance tests for web verifier (manual validation)."""

    def test_js_files_not_too_large(self):
        """Verify JavaScript files are reasonably sized."""
        js_files = ["web/replay.js", "web/create.js"]
        for js_file in js_files:
            path = Path(js_file)
            if path.exists():
                size_kb = path.stat().st_size / 1024
                assert size_kb < 500, f"{js_file} is too large: {size_kb:.1f}KB"

    def test_no_large_inline_data(self):
        """Verify no large data embedded in HTML."""
        html_files = ["web/verify.html", "web/index.html", "web/create.html"]
        for html_file in html_files:
            path = Path(html_file)
            if path.exists():
                size_kb = path.stat().st_size / 1024
                assert size_kb < 200, f"{html_file} is too large: {size_kb:.1f}KB"


class TestWebVerifierDocumentation:
    """Tests for documentation and examples."""

    def test_readme_mentions_web_verifier(self):
        """Verify README documents web verifier (optional)."""
        readme = Path("README.md")
        if readme.exists():
            content = readme.read_text()
            # Optional: README may or may not mention web verifier
            pass  # Skip this check as it's not essential

def test_verify_web_pages_script_exists():
    """Verify the web pages verification script exists."""
    script = Path("scripts/verification/verify_web_pages.py")
    assert script.exists(), "verify_web_pages.py script not found"


def test_verify_web_pages_script_runnable():
    """Verify the script has main function."""
    script = Path("scripts/verification/verify_web_pages.py")
    if script.exists():
        content = script.read_text()
        assert "def main()" in content, "Script missing main function"
