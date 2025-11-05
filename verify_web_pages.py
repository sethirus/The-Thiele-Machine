#!/usr/bin/env python3
"""
Verification script for Thiele Machine web pages.
Tests that all pages and JavaScript files are properly configured.
"""

import os
import sys
from pathlib import Path

def verify_file_exists(path, description):
    """Verify a file exists and print status."""
    if path.exists():
        print(f"✓ {description}: {path}")
        return True
    else:
        print(f"✗ MISSING {description}: {path}")
        return False

def verify_file_contains(path, search_text, description):
    """Verify a file contains specific text."""
    if not path.exists():
        print(f"✗ File not found: {path}")
        return False
    
    content = path.read_text()
    if search_text in content:
        print(f"✓ {description}")
        return True
    else:
        print(f"✗ MISSING {description} in {path}")
        return False

def main():
    """Run all verifications."""
    print("=" * 70)
    print("Thiele Machine Web Pages Verification")
    print("=" * 70)
    print()
    
    docs_dir = Path("docs")
    all_checks_passed = True
    
    # Check docs directory exists
    print("1. Checking docs directory structure...")
    if not docs_dir.exists():
        print(f"✗ CRITICAL: docs directory not found!")
        print("   Run: cp -r web docs")
        return 1
    
    # Check main HTML pages
    print("\n2. Checking main HTML pages...")
    html_files = [
        ("index.html", "Landing page"),
        ("verify.html", "Verifier page"),
        ("create.html", "Create receipt page"),
        ("badge.html", "Badge generator"),
        ("qr.html", "QR code generator"),
    ]
    
    for filename, description in html_files:
        path = docs_dir / filename
        all_checks_passed &= verify_file_exists(path, description)
    
    # Check JavaScript files
    print("\n3. Checking JavaScript files...")
    js_files = [
        ("replay.js", "Verification engine"),
        ("create.js", "Receipt creation"),
    ]
    
    for filename, description in js_files:
        path = docs_dir / filename
        all_checks_passed &= verify_file_exists(path, description)
    
    # Check demos directory
    print("\n4. Checking demos directory...")
    demos_dir = docs_dir / "demos"
    demo_files = [
        ("index.html", "Demos landing page"),
        ("install.html", "Proof-Install demo"),
        ("install.js", "Install demo logic"),
        ("zk.html", "Zero-knowledge demo"),
        ("trusting-trust.html", "Trusting Trust demo"),
    ]
    
    for filename, description in demo_files:
        path = demos_dir / filename
        all_checks_passed &= verify_file_exists(path, description)
    
    # Check .nojekyll file
    print("\n5. Checking GitHub Pages configuration...")
    nojekyll = docs_dir / ".nojekyll"
    all_checks_passed &= verify_file_exists(nojekyll, ".nojekyll file")
    
    # Check script references
    print("\n6. Checking script references...")
    verify_html = docs_dir / "verify.html"
    all_checks_passed &= verify_file_contains(
        verify_html,
        '<script src="replay.js">',
        "verify.html includes replay.js"
    )
    
    install_html = demos_dir / "install.html"
    all_checks_passed &= verify_file_contains(
        install_html,
        '<script src="install.js">',
        "install.html includes install.js"
    )
    
    # Check for ThieleVerifier class
    print("\n7. Checking JavaScript implementation...")
    replay_js = docs_dir / "replay.js"
    all_checks_passed &= verify_file_contains(
        replay_js,
        "class ThieleVerifier",
        "ThieleVerifier class defined"
    )
    
    all_checks_passed &= verify_file_contains(
        replay_js,
        "async sha256",
        "SHA-256 implementation present"
    )
    
    # Print summary
    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)
    
    if all_checks_passed:
        print("✓ All checks passed!")
        print("\nGitHub Pages Configuration:")
        print("  1. Go to repository Settings → Pages")
        print("  2. Set Source to: Deploy from a branch")
        print("  3. Set Branch to: main")
        print("  4. Set Folder to: /docs")
        print("  5. Click Save")
        print("\nYour site will be available at:")
        print("  https://sethirus.github.io/The-Thiele-Machine/")
        return 0
    else:
        print("✗ Some checks failed. Please review the errors above.")
        return 1

if __name__ == "__main__":
    sys.exit(main())
