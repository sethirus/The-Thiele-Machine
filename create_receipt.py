#!/usr/bin/env python3
"""
Simple Thiele Receipt Creator

This script helps you create basic Thiele receipts for your files.
Use this to get started with receipt-based software distribution.

Usage:
    python3 create_receipt.py myfile.py
    python3 create_receipt.py myfile.py --output myfile_receipt.json
    python3 create_receipt.py myfile1.py myfile2.py --output multi_receipt.json
"""

import argparse
import hashlib
import json
import sys
import glob
import tempfile
import shutil
import zipfile
import tarfile
import urllib.request
import urllib.parse
from pathlib import Path
from datetime import datetime
from typing import List, Optional, Dict, Any

try:
    from nacl import signing
    HAS_NACL = True
except ImportError:
    HAS_NACL = False


def fetch_archive(url: str, dest_dir: Path) -> Path:
    """
    Fetch an archive from a URL and extract it.
    
    Supports:
    - GitHub release archives (.zip, .tar.gz)
    - Direct archive URLs
    - GitHub repository archives
    
    Args:
        url: URL to fetch (e.g., https://github.com/user/repo/archive/refs/tags/v1.0.0.tar.gz)
        dest_dir: Destination directory for extraction
    
    Returns:
        Path to extracted directory
    """
    print(f"📥 Fetching archive from: {url}")
    
    # Determine archive type from URL
    parsed = urllib.parse.urlparse(url)
    filename = Path(parsed.path).name
    
    if not filename:
        filename = "archive.tar.gz"
    
    # Download archive
    temp_archive = dest_dir / filename
    
    try:
        with urllib.request.urlopen(url, timeout=30) as response:
            total_size = int(response.headers.get('Content-Length', 0))
            chunk_size = 8192
            downloaded = 0
            
            with open(temp_archive, 'wb') as f:
                while True:
                    chunk = response.read(chunk_size)
                    if not chunk:
                        break
                    f.write(chunk)
                    downloaded += len(chunk)
                    
                    if total_size > 0:
                        percent = (downloaded / total_size) * 100
                        print(f"   Downloaded: {downloaded}/{total_size} bytes ({percent:.1f}%)", end='\r')
            
            if total_size > 0:
                print()  # New line after progress
        
        print(f"✓ Downloaded: {temp_archive.name} ({temp_archive.stat().st_size} bytes)")
        
    except Exception as e:
        print(f"❌ Failed to download archive: {e}", file=sys.stderr)
        raise
    
    # Extract archive
    print(f"📦 Extracting archive...")
    
    try:
        if filename.endswith('.zip'):
            with zipfile.ZipFile(temp_archive, 'r') as zip_ref:
                zip_ref.extractall(dest_dir)
                # Get the first directory in the zip
                names = zip_ref.namelist()
                if names:
                    first_dir = names[0].split('/')[0] if '/' in names[0] else names[0]
                    extracted_path = dest_dir / first_dir
                else:
                    extracted_path = dest_dir
                    
        elif filename.endswith(('.tar.gz', '.tgz', '.tar.bz2', '.tar.xz', '.tar')):
            with tarfile.open(temp_archive, 'r:*') as tar_ref:
                tar_ref.extractall(dest_dir)
                # Get the first directory in the tar
                names = tar_ref.getnames()
                if names:
                    first_dir = names[0].split('/')[0] if '/' in names[0] else names[0]
                    extracted_path = dest_dir / first_dir
                else:
                    extracted_path = dest_dir
        else:
            raise ValueError(f"Unsupported archive format: {filename}")
        
        # Clean up archive file
        temp_archive.unlink()
        
        print(f"✓ Extracted to: {extracted_path}")
        return extracted_path
        
    except Exception as e:
        print(f"❌ Failed to extract archive: {e}", file=sys.stderr)
        raise


def scan_directory(
    directory: Path,
    include_patterns: Optional[List[str]] = None,
    exclude_patterns: Optional[List[str]] = None,
    max_files: int = 10000,
    max_size_mb: float = 1000.0
) -> List[Path]:
    """
    Recursively scan a directory for files to include in receipt.
    
    Args:
        directory: Directory to scan
        include_patterns: Glob patterns to include (e.g., ['*.py', '*.js'])
        exclude_patterns: Glob patterns to exclude (e.g., ['node_modules/**', '.git/**'])
        max_files: Maximum number of files to include
        max_size_mb: Maximum total size in MB
    
    Returns:
        List of Path objects for files to include
    """
    default_excludes = [
        '.git/**',
        '.gitignore',
        'node_modules/**',
        '__pycache__/**',
        '*.pyc',
        '.venv/**',
        'venv/**',
        '.env',
        '.DS_Store',
        'Thumbs.db',
        '*.swp',
        '*.swo',
        '*~',
    ]
    
    exclude_patterns = (exclude_patterns or []) + default_excludes
    
    files = []
    total_size = 0
    max_size_bytes = max_size_mb * 1024 * 1024
    
    print(f"🔍 Scanning directory: {directory}")
    
    for item in directory.rglob('*'):
        # Skip directories
        if not item.is_file():
            continue
        
        # Check exclude patterns
        rel_path = item.relative_to(directory)
        excluded = False
        for pattern in exclude_patterns:
            if item.match(pattern) or rel_path.match(pattern):
                excluded = True
                break
        
        if excluded:
            continue
        
        # Check include patterns (if specified)
        if include_patterns:
            included = False
            for pattern in include_patterns:
                if item.match(pattern) or rel_path.match(pattern):
                    included = True
                    break
            if not included:
                continue
        
        # Check file size
        file_size = item.stat().st_size
        if total_size + file_size > max_size_bytes:
            print(f"⚠️  Size limit reached ({max_size_mb} MB), stopping scan")
            break
        
        # Check file count
        if len(files) >= max_files:
            print(f"⚠️  File limit reached ({max_files} files), stopping scan")
            break
        
        files.append(item)
        total_size += file_size
    
    print(f"✓ Found {len(files)} file(s) ({total_size / 1024 / 1024:.2f} MB)")
    return files


def canonical_json(obj):
    """
    Compute canonical JSON as per TRS-1.0 spec.
    Keys sorted alphabetically, compact format, UTF-8.
    """
    return json.dumps(obj, sort_keys=True, separators=(',', ':')).encode('utf-8')


def compute_file_hash(file_obj):
    """Compute hash of a file object as per TRS-1.0 spec."""
    canonical = canonical_json(file_obj)
    return hashlib.sha256(canonical).hexdigest()


def compute_global_digest(files):
    """
    Compute global digest from files array as per TRS-1.0 spec.
    
    Algorithm:
    1. For each file object, compute canonical JSON and SHA-256 hash
    2. Concatenate all hashes (as hex strings)
    3. Convert concatenated hex to bytes
    4. Compute SHA-256 of the bytes
    """
    file_hashes = [compute_file_hash(f) for f in files]
    concatenated = ''.join(file_hashes)
    # Convert hex string to bytes
    hex_bytes = bytes.fromhex(concatenated)
    return hashlib.sha256(hex_bytes).hexdigest()


def sha256_file(filepath):
    """Compute SHA256 hash of a file."""
    sha256 = hashlib.sha256()
    with open(filepath, 'rb') as f:
        for chunk in iter(lambda: f.read(4096), b''):
            sha256.update(chunk)
    return sha256.hexdigest()


def discover_build_outputs(project_dir: Path) -> List[Path]:
    """
    Auto-discover build outputs in a project directory.
    
    Looks for common build output directories and package manifests.
    
    Returns:
        List of Path objects for discovered build artifacts
    """
    artifacts = []
    project_dir = Path(project_dir).resolve()
    
    # Common build output directories
    build_dirs = [
        'dist',       # Python, general
        'build',      # General
        'target',     # Rust, Java
        'out',        # Various
        'bin',        # C/C++, Go
        'pkg',        # Go
        'releases',   # General
        'artifacts',  # General
    ]
    
    # Try to find build outputs
    for build_dir in build_dirs:
        build_path = project_dir / build_dir
        if build_path.exists() and build_path.is_dir():
            # Find common artifact types
            patterns = [
                '*.whl',      # Python wheel
                '*.tar.gz',   # Tarball
                '*.zip',      # Zip archive
                '*.exe',      # Windows executable
                '*.dll',      # Windows library
                '*.so',       # Linux library
                '*.dylib',    # macOS library
                '*.jar',      # Java archive
                '*.war',      # Java web archive
                '*.AppImage', # Linux AppImage
                '*.deb',      # Debian package
                '*.rpm',      # RPM package
                '*.dmg',      # macOS disk image
                '*.app',      # macOS app bundle
            ]
            
            for pattern in patterns:
                for artifact in build_path.glob(pattern):
                    if artifact.is_file():
                        artifacts.append(artifact)
    
    return artifacts


def read_package_manifest(project_dir: Path) -> Optional[Dict[str, Any]]:
    """
    Read package manifest files to extract metadata.
    
    Supports:
    - package.json (Node.js)
    - pyproject.toml (Python)
    - Cargo.toml (Rust)
    - setup.py (Python legacy)
    
    Returns:
        Dict with metadata or None if no manifest found
    """
    project_dir = Path(project_dir).resolve()
    metadata = {}
    
    # Try package.json (Node.js)
    package_json = project_dir / 'package.json'
    if package_json.exists():
        try:
            with open(package_json, 'r') as f:
                data = json.load(f)
            metadata['name'] = data.get('name')
            metadata['version'] = data.get('version')
            metadata['description'] = data.get('description')
            metadata['repository'] = data.get('repository', {}).get('url') if isinstance(data.get('repository'), dict) else data.get('repository')
            metadata['author'] = data.get('author')
            metadata['license'] = data.get('license')
            metadata['manifest_type'] = 'package.json'
            return metadata
        except (json.JSONDecodeError, KeyError):
            pass
    
    # Try pyproject.toml (Python)
    pyproject = project_dir / 'pyproject.toml'
    if pyproject.exists():
        try:
            # Simple TOML parsing for basic fields
            with open(pyproject, 'r') as f:
                content = f.read()
            
            # Extract basic info (simplified, not a full TOML parser)
            for line in content.split('\n'):
                if line.strip().startswith('name ='):
                    metadata['name'] = line.split('=')[1].strip().strip('"\'')
                elif line.strip().startswith('version ='):
                    metadata['version'] = line.split('=')[1].strip().strip('"\'')
                elif line.strip().startswith('description ='):
                    metadata['description'] = line.split('=')[1].strip().strip('"\'')
            
            if metadata:
                metadata['manifest_type'] = 'pyproject.toml'
                return metadata
        except Exception:
            pass
    
    # Try Cargo.toml (Rust)
    cargo_toml = project_dir / 'Cargo.toml'
    if cargo_toml.exists():
        try:
            with open(cargo_toml, 'r') as f:
                content = f.read()
            
            # Extract basic info (simplified)
            for line in content.split('\n'):
                if line.strip().startswith('name ='):
                    metadata['name'] = line.split('=')[1].strip().strip('"\'')
                elif line.strip().startswith('version ='):
                    metadata['version'] = line.split('=')[1].strip().strip('"\'')
                elif line.strip().startswith('description ='):
                    metadata['description'] = line.split('=')[1].strip().strip('"\'')
            
            if metadata:
                metadata['manifest_type'] = 'Cargo.toml'
                return metadata
        except Exception:
            pass
    
    return None


def create_project_receipts(
    project_dir: Path,
    output_dir: Optional[Path] = None,
    sign_key: Optional[str] = None,
    public_key: Optional[str] = None,
    create_manifest: bool = True
) -> List[Path]:
    """
    Create receipts for all build artifacts in a project.
    
    This is the "repository mode" that auto-discovers artifacts.
    
    Args:
        project_dir: Root directory of the project
        output_dir: Where to save receipts (default: project_dir/receipts)
        sign_key: Optional signing key path
        public_key: Optional public key path
        create_manifest: Whether to create MANIFEST.receipt.json index
    
    Returns:
        List of paths to created receipt files
    """
    project_dir = Path(project_dir).resolve()
    output_dir = output_dir or (project_dir / 'receipts')
    output_dir.mkdir(parents=True, exist_ok=True)
    
    print(f"📂 Scanning project: {project_dir}")
    
    # Discover build artifacts
    artifacts = discover_build_outputs(project_dir)
    
    if not artifacts:
        print("⚠️  No build artifacts found. Have you run your build command?")
        print("   Looking in: dist/, target/, build/, bin/, pkg/, releases/, artifacts/")
        return []
    
    print(f"📦 Found {len(artifacts)} artifact(s):")
    for artifact in artifacts:
        rel_path = artifact.relative_to(project_dir)
        print(f"   • {rel_path}")
    
    # Read package manifest for metadata
    manifest_metadata = read_package_manifest(project_dir)
    if manifest_metadata:
        print(f"\n📋 Detected {manifest_metadata.get('manifest_type', 'manifest')}")
        if manifest_metadata.get('name'):
            print(f"   Name: {manifest_metadata['name']}")
        if manifest_metadata.get('version'):
            print(f"   Version: {manifest_metadata['version']}")
    
    # Create receipts for each artifact
    print(f"\n🔐 Creating receipts...")
    receipt_paths = []
    
    for artifact in artifacts:
        # Prepare metadata
        metadata = {}
        if manifest_metadata:
            metadata.update(manifest_metadata)
        
        metadata['artifact_path'] = str(artifact.relative_to(project_dir))
        metadata['project_dir'] = str(project_dir)
        
        # Create receipt
        receipt_name = f"{artifact.name}.receipt.json"
        receipt_path = output_dir / receipt_name
        
        try:
            receipt = create_receipt(
                [str(artifact)],
                output_path=str(receipt_path),
                include_steps=False,
                sign_key=sign_key,
                public_key=public_key,
                metadata=metadata
            )
            receipt_paths.append(receipt_path)
            
        except Exception as e:
            print(f"❌ Failed to create receipt for {artifact.name}: {e}")
    
    # Create manifest index
    if create_manifest and receipt_paths:
        manifest_path = output_dir / 'MANIFEST.receipt.json'
        manifest = {
            'version': '1.0',
            'project': manifest_metadata.get('name', 'unknown') if manifest_metadata else 'unknown',
            'generated': datetime.now().astimezone().isoformat(),
            'receipts': [
                {
                    'file': r.name,
                    'artifact': Path(r.name).stem.replace('.receipt', ''),
                    'path': str(r.relative_to(output_dir))
                }
                for r in receipt_paths
            ],
            'metadata': manifest_metadata or {}
        }
        
        with open(manifest_path, 'w') as f:
            json.dump(manifest, f, indent=2, ensure_ascii=False)
        
        print(f"\n📑 Created manifest index: {manifest_path}")
        print(f"   Lists all {len(receipt_paths)} receipt(s)")
    
    return receipt_paths


def create_receipt(files, output_path=None, include_steps=False, sign_key=None, public_key=None, metadata=None):
    """
    Create a Thiele receipt for one or more files.
    
    Args:
        files: List of file paths to include in receipt
        output_path: Where to save the receipt (default: auto-generated)
        include_steps: Whether to include detailed TRS-0 steps (default: False, uses TRS-1.0)
        sign_key: Path to Ed25519 private key for signing (optional)
        public_key: Path to Ed25519 public key (optional, will be included in receipt)
        metadata: Optional metadata dict to include in receipt
    
    Returns:
        dict: The created receipt
    """
    
    file_infos = []
    
    for filepath in files:
        path = Path(filepath)
        
        if not path.exists():
            print(f"Error: File not found: {filepath}", file=sys.stderr)
            sys.exit(1)
        
        # Read file content
        with open(path, 'rb') as f:
            content = f.read()
        
        # Compute hash
        content_hash = hashlib.sha256(content).hexdigest()
        
        file_infos.append({
            "path": path.name,
            "size": len(content),
            "sha256": content_hash
        })
        
        print(f"✓ Added: {path.name} ({len(content)} bytes, SHA256: {content_hash[:16]}...)")
    
    # Compute global digest per TRS-1.0 spec
    global_digest = compute_global_digest(file_infos)
    
    # Determine receipt version and structure
    if include_steps:
        # TRS-0 with detailed steps
        receipt = create_trs0_receipt(file_infos, global_digest)
    else:
        # TRS-1.0 simplified format
        receipt = {
            "version": "TRS-1.0",
            "files": file_infos,
            "global_digest": global_digest,
            "kernel_sha256": file_infos[0]["sha256"] if len(file_infos) == 1 else global_digest,
            "timestamp": datetime.now().astimezone().isoformat(),
            "sig_scheme": "none",
            "signature": ""
        }
        
        # Add metadata if provided
        if metadata:
            receipt["metadata"] = metadata
    
    # Sign if requested
    if sign_key:
        if not HAS_NACL:
            print("Error: PyNaCl not installed. Install with: pip install PyNaCl", file=sys.stderr)
            sys.exit(1)
        
        try:
            # Load private key
            with open(sign_key, 'rb') as f:
                key_data = f.read()
            
            # Try to parse as raw bytes (32 bytes) or hex
            if len(key_data) == 32:
                private_key = signing.SigningKey(key_data)
            elif len(key_data) == 64:
                # Hex encoded
                private_key = signing.SigningKey(bytes.fromhex(key_data.decode('ascii').strip()))
            else:
                print(f"Error: Invalid key format. Expected 32 bytes or 64 hex chars, got {len(key_data)} bytes", file=sys.stderr)
                sys.exit(1)
            
            # Sign the global digest
            message = global_digest.encode('utf-8')
            signature_bytes = private_key.sign(message).signature
            
            receipt["sig_scheme"] = "ed25519"
            receipt["signature"] = signature_bytes.hex()
            
            # Include public key if provided or derive from private key
            if public_key:
                with open(public_key, 'rb') as f:
                    pubkey_data = f.read()
                if len(pubkey_data) == 32:
                    receipt["public_key"] = pubkey_data.hex()
                elif len(pubkey_data) == 64:
                    receipt["public_key"] = pubkey_data.decode('ascii').strip()
                else:
                    print(f"Warning: Invalid public key format, using derived key", file=sys.stderr)
                    receipt["public_key"] = private_key.verify_key.encode().hex()
            else:
                receipt["public_key"] = private_key.verify_key.encode().hex()
            
            print(f"✓ Receipt signed with Ed25519")
            print(f"✓ Public key: {receipt['public_key'][:16]}...")
            
        except FileNotFoundError as e:
            print(f"Error: Key file not found: {e}", file=sys.stderr)
            sys.exit(1)
        except Exception as e:
            print(f"Error signing receipt: {e}", file=sys.stderr)
            sys.exit(1)
    
    # Determine output path
    if output_path is None:
        if len(files) == 1:
            output_path = f"{Path(files[0]).stem}_receipt.json"
        else:
            output_path = "receipt.json"
    
    # Save receipt
    with open(output_path, 'w') as f:
        json.dump(receipt, f, indent=2, ensure_ascii=False)
    
    print(f"\n✓ Receipt created: {output_path}")
    print(f"✓ Global digest: {global_digest}")
    print(f"\nTo verify and materialize:")
    print(f"  python3 verifier/replay.py {output_path}")
    
    return receipt


def create_trs0_receipt(file_infos, global_digest):
    """Create a TRS-0 receipt with detailed steps."""
    
    # Empty state hash (SHA-256 of empty bytes)
    empty_state = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
    
    steps = []
    current_state = empty_state
    
    for idx, file_info in enumerate(file_infos):
        # Read file for hex encoding
        with open(file_info["path"], 'rb') as f:
            content = f.read()
        
        # Create EMIT_BYTES step
        step = {
            "step": idx * 2,
            "pre_state_sha256": current_state,
            "opcode": "EMIT_BYTES",
            "args": {
                "path": file_info["path"],
                "offset": 0,
                "bytes_hex": content.hex()
            },
            "axioms": ["initial_emit" if idx == 0 else "emit_next_file"],
            "oracle_reply": {
                "status": "sat",
                "witness": None
            },
            "mu_bits": len(content) * 8.0,  # 8 bits per byte
            "post_state_sha256": "computed_by_verifier"
        }
        steps.append(step)
        
        # Create ASSERT_SHA256 step
        assert_step = {
            "step": idx * 2 + 1,
            "pre_state_sha256": "computed_by_verifier",
            "opcode": "ASSERT_SHA256",
            "args": {
                "path": file_info["path"],
                "sha256": file_info["sha256"]
            },
            "axioms": ["hash_integrity"],
            "oracle_reply": {
                "status": "sat",
                "witness": {"verified_hash": file_info["sha256"]}
            },
            "mu_bits": 256.0,  # Cost of SHA-256 verification
            "post_state_sha256": "computed_by_verifier"
        }
        steps.append(assert_step)
        
        current_state = "computed_by_verifier"
    
    return {
        "version": "TRS-0",
        "steps": steps,
        "global_digest": global_digest,
        "sig_scheme": "none",
        "signature": ""
    }


def main():
    parser = argparse.ArgumentParser(
        description="Create Thiele receipts for cryptographically verifiable software distribution",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Create receipt for a single file
  %(prog)s script.py
  
  # Create receipt for multiple files
  %(prog)s main.py utils.py config.json
  
  # Repository mode: auto-discover and create receipts for all build artifacts
  %(prog)s --project .
  %(prog)s --project /path/to/myproject
  
  # Directory mode: scan and create receipts for all files in directory
  %(prog)s --directory ./src --include "*.py" "*.js"
  
  # Archive mode: fetch and create receipts from a URL
  %(prog)s --archive https://github.com/user/repo/archive/refs/tags/v1.0.0.tar.gz
  
  # Specify output path
  %(prog)s script.py --output my_receipt.json
  
  # Create TRS-0 receipt with detailed steps
  %(prog)s script.py --steps

After creating a receipt, verify it with:
  python3 verifier/replay.py <receipt.json>

Learn more: docs/RECEIPT_GUIDE.md
"""
    )
    
    parser.add_argument(
        'files',
        nargs='*',  # Changed from '+' to '*' to allow --project/--directory/--archive mode
        help='Files to include in the receipt (or use --project/--directory/--archive for auto-discovery)'
    )
    
    parser.add_argument(
        '--project',
        metavar='DIR',
        help='Repository mode: auto-discover build artifacts in project directory'
    )
    
    parser.add_argument(
        '--directory',
        metavar='DIR',
        help='Directory mode: scan directory recursively and create receipt for all files'
    )
    
    parser.add_argument(
        '--archive',
        metavar='URL',
        help='Archive mode: fetch archive from URL and create receipt (supports .zip, .tar.gz)'
    )
    
    parser.add_argument(
        '--include',
        nargs='+',
        metavar='PATTERN',
        help='Glob patterns to include (only with --directory mode, e.g., "*.py" "*.js")'
    )
    
    parser.add_argument(
        '--exclude',
        nargs='+',
        metavar='PATTERN',
        help='Glob patterns to exclude (only with --directory mode, e.g., "*.pyc" "test_*")'
    )
    
    parser.add_argument(
        '-o', '--output',
        help='Output path for the receipt (default: auto-generated)'
    )
    
    parser.add_argument(
        '--steps',
        action='store_true',
        help='Create TRS-0 receipt with detailed steps (default: TRS-1.0 simplified)'
    )
    
    parser.add_argument(
        '--sign',
        metavar='KEY_FILE',
        help='Sign receipt with Ed25519 private key (32 bytes or 64 hex chars)'
    )
    
    parser.add_argument(
        '--public-key',
        metavar='PUBKEY_FILE',
        help='Public key file to include in receipt (optional, derived from private if not provided)'
    )
    
    parser.add_argument(
        '--metadata',
        metavar='JSON',
        help='JSON metadata to include in receipt (e.g., \'{"author":"Name","version":"1.0"}\')'
    )
    
    parser.add_argument(
        '--verify',
        action='store_true',
        help='Verify the receipt after creation (requires verifier/replay.py)'
    )
    
    args = parser.parse_args()
    
    # Validate arguments
    mode_count = sum([bool(args.project), bool(args.directory), bool(args.archive), bool(args.files)])
    if mode_count > 1:
        print("Error: Can only use one of: files, --project, --directory, or --archive", file=sys.stderr)
        sys.exit(1)
    
    if mode_count == 0:
        print("Error: Must specify files, --project, --directory, or --archive", file=sys.stderr)
        parser.print_help()
        sys.exit(1)
    
    # Parse metadata if provided
    metadata = None
    if args.metadata:
        try:
            metadata = json.loads(args.metadata)
        except json.JSONDecodeError as e:
            print(f"Error: Invalid JSON metadata: {e}", file=sys.stderr)
            sys.exit(1)
    
    # Archive mode
    if args.archive:
        print(f"🌐 Archive mode: fetching from {args.archive}\n")
        
        # Create temp directory for extraction
        with tempfile.TemporaryDirectory() as temp_dir:
            temp_path = Path(temp_dir)
            
            try:
                # Fetch and extract archive
                extracted_path = fetch_archive(args.archive, temp_path)
                
                # Scan the extracted directory
                files = scan_directory(
                    extracted_path,
                    include_patterns=args.include,
                    exclude_patterns=args.exclude
                )
                
                if not files:
                    print("⚠️  No files found in archive", file=sys.stderr)
                    sys.exit(1)
                
                # Add archive URL to metadata
                archive_metadata = metadata or {}
                archive_metadata['archive_url'] = args.archive
                archive_metadata['archive_timestamp'] = datetime.now().astimezone().isoformat()
                
                # Detect package manifest
                manifest_meta = read_package_manifest(extracted_path)
                if manifest_meta:
                    archive_metadata.update(manifest_meta)
                
                # Create receipt
                receipt = create_receipt(
                    [str(f) for f in files],
                    output_path=args.output,
                    include_steps=args.steps,
                    sign_key=args.sign,
                    public_key=args.public_key,
                    metadata=archive_metadata
                )
                
            except Exception as e:
                print(f"❌ Archive processing failed: {e}", file=sys.stderr)
                sys.exit(1)
        
        return
    
    # Directory mode
    if args.directory:
        print(f"📁 Directory mode: scanning {args.directory}\n")
        
        directory = Path(args.directory)
        if not directory.exists() or not directory.is_dir():
            print(f"Error: Directory not found: {args.directory}", file=sys.stderr)
            sys.exit(1)
        
        # Scan directory
        files = scan_directory(
            directory,
            include_patterns=args.include,
            exclude_patterns=args.exclude
        )
        
        if not files:
            print("⚠️  No files found in directory", file=sys.stderr)
            sys.exit(1)
        
        # Add directory info to metadata
        dir_metadata = metadata or {}
        dir_metadata['scanned_directory'] = str(directory.resolve())
        dir_metadata['scan_timestamp'] = datetime.now().astimezone().isoformat()
        dir_metadata['file_count'] = len(files)
        
        # Detect package manifest
        manifest_meta = read_package_manifest(directory)
        if manifest_meta:
            dir_metadata.update(manifest_meta)
        
        # Create receipt
        receipt = create_receipt(
            [str(f) for f in files],
            output_path=args.output,
            include_steps=args.steps,
            sign_key=args.sign,
            public_key=args.public_key,
            metadata=dir_metadata
        )
        
        return
    
    # Repository mode
    if args.project:
        print(f"🚀 Repository mode: scanning {args.project}\n")
        
        output_dir = Path(args.output) if args.output else None
        
        receipt_paths = create_project_receipts(
            project_dir=Path(args.project),
            output_dir=output_dir,
            sign_key=args.sign,
            public_key=args.public_key,
            create_manifest=True
        )
        
        if receipt_paths:
            print(f"\n✅ Created {len(receipt_paths)} receipt(s)")
            print(f"   Output directory: {receipt_paths[0].parent}")
        else:
            print("\n⚠️  No receipts created")
            sys.exit(1)
        
        return
    
    # Single/multi-file mode
    print(f"Creating Thiele receipt for {len(args.files)} file(s)...\n")
    receipt = create_receipt(
        args.files,
        output_path=args.output,
        include_steps=args.steps,
        sign_key=args.sign,
        public_key=args.public_key,
        metadata=metadata
    )
    
    # Optionally verify
    if args.verify:
        import subprocess
        output_path = args.output or (
            f"{Path(args.files[0]).stem}_receipt.json" if len(args.files) == 1 else "receipt.json"
        )
        print(f"\nVerifying receipt...")
        try:
            subprocess.run(
                ["python3", "verifier/replay.py", output_path],
                check=True
            )
            print("✓ Verification successful!")
        except subprocess.CalledProcessError:
            print("✗ Verification failed!", file=sys.stderr)
            sys.exit(1)
        except FileNotFoundError:
            print("Warning: verifier/replay.py not found, skipping verification", file=sys.stderr)


if __name__ == "__main__":
    main()
