#!/usr/bin/env python3
"""
Build Evidence Dossier for Thiele Machine Experiments

Creates a comprehensive ZIP archive of experimental results, plots, reports,
and SHA256 manifests for reproducibility and verification.
"""

import argparse
import hashlib
import json
import zipfile
from pathlib import Path
from typing import Dict, List

EXPERIMENTS_DIR = Path("experiments")

def compute_sha256(file_path: Path) -> str:
    """Compute SHA256 hash of a file."""
    with open(file_path, 'rb') as f:
        return hashlib.sha256(f.read()).hexdigest()

def collect_files(patterns: List[str]) -> List[Path]:
    """Collect files matching patterns."""
    files = []
    for pattern in patterns:
        files.extend(EXPERIMENTS_DIR.glob(pattern))
    return sorted(files)

def create_manifest(files: List[Path]) -> Dict[str, str]:
    """Create SHA256 manifest for files."""
    manifest = {}
    for file_path in files:
        if file_path.is_file():
            manifest[str(file_path.relative_to(EXPERIMENTS_DIR))] = compute_sha256(file_path)
    return manifest

def build_dossier(output_zip: Path):
    """Build the evidence dossier ZIP."""
    # Collect all relevant files
    patterns = [
        "*.json",  # Results and reports
        "*.png",   # Plots
        "*.yaml",  # Hypotheses
        "*.md",    # README
        "*.csv"    # Any CSVs
    ]
    files = collect_files(patterns)
    
    # Create manifest
    manifest = create_manifest(files)
    manifest_path = EXPERIMENTS_DIR / "SHA256SUMS"
    with open(manifest_path, 'w') as f:
        for path, hash_val in manifest.items():
            f.write(f"{hash_val}  {path}\n")
    
    # Create ZIP
    with zipfile.ZipFile(output_zip, 'w', zipfile.ZIP_DEFLATED) as zf:
        for file_path in files:
            zf.write(file_path, file_path.relative_to(EXPERIMENTS_DIR))
        zf.write(manifest_path, manifest_path.relative_to(EXPERIMENTS_DIR))
    
    # Compute dossier hash
    dossier_hash = compute_sha256(output_zip)
    
    print(f"Dossier created: {output_zip}")
    print(f"Dossier SHA256: {dossier_hash}")
    print(f"Manifest: {manifest_path}")
    
    return dossier_hash

def main():
    parser = argparse.ArgumentParser(description="Build Thiele Machine evidence dossier")
    parser.add_argument('--output', type=Path, default=Path("thiele_dossier.zip"), help='Output ZIP file')
    
    args = parser.parse_args()
    
    if not EXPERIMENTS_DIR.exists():
        print(f"Experiments directory {EXPERIMENTS_DIR} not found")
        return
    
    build_dossier(args.output)

if __name__ == '__main__':
    main()