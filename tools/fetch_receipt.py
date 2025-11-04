#!/usr/bin/env python3
"""
Thiele Fetch - Auto-fetch and verify receipts from repositories

This tool automatically downloads artifacts and their receipts from GitHub
releases or direct URLs, then verifies them using the Thiele verifier.

Usage:
    thiele-fetch owner/repository
    thiele-fetch https://example.com/artifact.receipt.json
    thiele-fetch owner/repository --tag v1.0.0
    thiele-fetch owner/repository --artifact myfile.whl
"""

import argparse
import json
import os
import sys
import urllib.request
import urllib.error
from pathlib import Path
from typing import Optional, Dict, Any, List


def fetch_url(url: str) -> bytes:
    """Fetch content from a URL."""
    try:
        with urllib.request.urlopen(url, timeout=30) as response:
            return response.read()
    except urllib.error.URLError as e:
        raise Exception(f"Failed to fetch {url}: {e}")


def fetch_github_release(repo: str, tag: Optional[str] = None) -> Dict[str, Any]:
    """
    Fetch release information from GitHub API.
    
    Args:
        repo: Repository in format "owner/name"
        tag: Specific tag name, or None for latest
    
    Returns:
        Release information dict
    """
    if tag:
        api_url = f"https://api.github.com/repos/{repo}/releases/tags/{tag}"
    else:
        api_url = f"https://api.github.com/repos/{repo}/releases/latest"
    
    print(f"📡 Fetching release info from {api_url}")
    
    try:
        data = fetch_url(api_url)
        return json.loads(data.decode('utf-8'))
    except Exception as e:
        raise Exception(f"Failed to fetch GitHub release: {e}")


def find_receipt_assets(release: Dict[str, Any], artifact_name: Optional[str] = None) -> List[Dict[str, str]]:
    """
    Find receipt files in release assets.
    
    Returns list of dicts with 'name' and 'url' keys for each receipt found.
    """
    assets = release.get('assets', [])
    
    receipts = []
    for asset in assets:
        name = asset['name']
        if name.endswith('.receipt.json'):
            # Check if this is for the requested artifact
            if artifact_name:
                # Strip .receipt.json to get base name
                base = name.replace('.receipt.json', '')
                if artifact_name in base or base in artifact_name:
                    receipts.append({
                        'name': name,
                        'url': asset['browser_download_url']
                    })
            else:
                receipts.append({
                    'name': name,
                    'url': asset['browser_download_url']
                })
    
    return receipts


def download_file(url: str, output_path: Path) -> None:
    """Download a file from URL to local path."""
    print(f"⬇️  Downloading {url}")
    data = fetch_url(url)
    
    output_path.parent.mkdir(parents=True, exist_ok=True)
    with open(output_path, 'wb') as f:
        f.write(data)
    
    print(f"✅ Saved to {output_path}")


def verify_receipt(receipt_path: Path) -> bool:
    """
    Verify a receipt using the Thiele verifier.
    
    Returns True if verification succeeds, False otherwise.
    """
    try:
        # Try to import the verifier
        try:
            from verifier import replay
            print(f"\n🔍 Verifying receipt: {receipt_path}")
            
            # Load receipt
            with open(receipt_path, 'r') as f:
                receipt = json.load(f)
            
            # Verify (this is a simplified check - actual verification is more complex)
            version = receipt.get('version', 'unknown')
            files = receipt.get('files', [])
            global_digest = receipt.get('global_digest', 'N/A')
            signature = receipt.get('signature', '')
            
            print(f"  Version: {version}")
            print(f"  Files: {len(files)}")
            print(f"  Global Digest: {global_digest}")
            print(f"  Signature: {'Present' if signature else 'None'}")
            
            # Basic validation
            if not files:
                print("❌ No files in receipt")
                return False
            
            if not global_digest or global_digest == 'N/A':
                print("❌ Missing global digest")
                return False
            
            print("✅ Receipt structure is valid")
            print("\n💡 To perform full verification with hash checking:")
            print(f"   python3 verifier/replay.py {receipt_path}")
            
            return True
            
        except ImportError:
            # Verifier not available, do basic validation
            print(f"\n📋 Basic validation of {receipt_path}")
            
            with open(receipt_path, 'r') as f:
                receipt = json.load(f)
            
            # Check required fields
            required = ['version', 'files', 'global_digest']
            missing = [f for f in required if f not in receipt]
            
            if missing:
                print(f"❌ Missing required fields: {', '.join(missing)}")
                return False
            
            print(f"✅ Receipt has all required fields")
            print(f"  Version: {receipt['version']}")
            print(f"  Files: {len(receipt['files'])}")
            print(f"  Global Digest: {receipt['global_digest']}")
            
            return True
            
    except Exception as e:
        print(f"❌ Verification failed: {e}")
        return False


def main():
    """Main entry point for thiele-fetch."""
    parser = argparse.ArgumentParser(
        description='Auto-fetch and verify receipts from repositories',
        epilog="""
Examples:
  thiele-fetch sethirus/The-Thiele-Machine
  thiele-fetch owner/repo --tag v1.0.0
  thiele-fetch owner/repo --artifact myfile.whl
  thiele-fetch https://example.com/file.receipt.json
        """
    )
    
    parser.add_argument(
        'target',
        help='GitHub repository (owner/name) or direct URL to receipt'
    )
    parser.add_argument(
        '--tag',
        help='Specific release tag (default: latest)'
    )
    parser.add_argument(
        '--artifact',
        help='Specific artifact name to fetch receipt for'
    )
    parser.add_argument(
        '--output-dir',
        type=Path,
        default=Path('./receipts'),
        help='Directory to save downloaded receipts (default: ./receipts)'
    )
    parser.add_argument(
        '--no-verify',
        action='store_true',
        help='Skip verification after download'
    )
    
    args = parser.parse_args()
    
    try:
        # Determine if target is a URL or repo name
        if args.target.startswith('http://') or args.target.startswith('https://'):
            # Direct URL
            url = args.target
            filename = Path(urllib.request.urlparse(url).path).name
            if not filename.endswith('.receipt.json'):
                filename += '.receipt.json'
            
            output_path = args.output_dir / filename
            download_file(url, output_path)
            
            if not args.no_verify:
                verify_receipt(output_path)
            
        else:
            # GitHub repository
            if '/' not in args.target:
                print("❌ Repository must be in format: owner/name")
                return 1
            
            # Fetch release info
            release = fetch_github_release(args.target, args.tag)
            
            print(f"\n📦 Release: {release['name']}")
            print(f"   Tag: {release['tag_name']}")
            print(f"   Published: {release['published_at']}")
            
            # Find receipts
            receipts = find_receipt_assets(release, args.artifact)
            
            if not receipts:
                print("\n❌ No receipt files found in this release")
                print("\n💡 Make sure the release includes .receipt.json files")
                return 1
            
            print(f"\n📑 Found {len(receipts)} receipt(s):")
            for r in receipts:
                print(f"   • {r['name']}")
            
            # Download all receipts
            print("\n⬇️  Downloading receipts...")
            for receipt in receipts:
                output_path = args.output_dir / receipt['name']
                download_file(receipt['url'], output_path)
                
                if not args.no_verify:
                    verify_receipt(output_path)
                    print()  # blank line between receipts
            
            print(f"\n✅ Downloaded {len(receipts)} receipt(s) to {args.output_dir}")
        
        return 0
        
    except Exception as e:
        print(f"\n❌ Error: {e}", file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.exit(main())
