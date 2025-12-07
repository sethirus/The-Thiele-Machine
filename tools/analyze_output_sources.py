#!/usr/bin/env python3
"""
Analyze Output Sources - Comprehensive Directory Audit Tool
Maps every output directory to its source code and suggests fixes
"""

import subprocess
import json
from pathlib import Path
from collections import defaultdict
import re

REPO_ROOT = Path(__file__).resolve().parents[1]

def run_cmd(cmd):
    """Run shell command and return output"""
    result = subprocess.run(cmd, shell=True, capture_output=True, text=True, cwd=REPO_ROOT)
    return result.stdout

def find_directory_references(dirname):
    """Find all references to a directory name in Python/shell files"""
    cmd = f"grep -r '{dirname}' --include='*.py' --include='*.sh' 2>/dev/null | grep -v '.venv\\|__pycache__\\|.egg-info'"
    output = run_cmd(cmd)
    
    references = []
    for line in output.split('\n'):
        if line.strip():
            parts = line.split(':', 2)
            if len(parts) >= 3:
                references.append({
                    'file': parts[0],
                    'line_num': parts[1] if parts[1].isdigit() else 'N/A',
                    'content': parts[2] if len(parts) > 2 else parts[1]
                })
    return references

def get_directory_info(dirpath):
    """Get metadata about a directory"""
    if not dirpath.exists():
        return None
    
    # Count files
    files = list(dirpath.rglob('*'))
    file_count = len([f for f in files if f.is_file()])
    dir_count = len([f for f in files if f.is_dir()])
    
    # Get total size
    total_size = sum(f.stat().st_size for f in files if f.is_file())
    
    # Get creation date from git
    git_cmd = f"git log --diff-filter=A --follow --format=%ai -- {dirpath} 2>/dev/null | tail -1"
    creation_date = run_cmd(git_cmd).strip() or "Unknown"
    
    # Get last modification
    git_cmd = f"git log -1 --format=%ai -- {dirpath} 2>/dev/null"
    last_modified = run_cmd(git_cmd).strip() or "Unknown"
    
    return {
        'file_count': file_count,
        'dir_count': dir_count,
        'total_size_mb': round(total_size / 1024 / 1024, 2),
        'created': creation_date,
        'last_modified': last_modified
    }

def analyze_all_directories():
    """Analyze all directories in the repository"""
    
    # Get all directories (excluding hidden, venv, caches)
    all_dirs = []
    for item in REPO_ROOT.iterdir():
        if item.is_dir() and not item.name.startswith('.') and item.name not in ['__pycache__', 'build']:
            all_dirs.append(item)
    
    results = {}
    
    for dirpath in sorted(all_dirs):
        dirname = dirpath.name
        print(f"Analyzing: {dirname}...")
        
        info = get_directory_info(dirpath)
        if not info:
            continue
        
        # Find source code references
        references = find_directory_references(dirname)
        
        # Categorize directory
        category = categorize_directory(dirname, dirpath, references)
        
        results[dirname] = {
            'path': str(dirpath),
            'info': info,
            'category': category,
            'references': references[:10],  # Limit to first 10
            'reference_count': len(references)
        }
    
    return results

def categorize_directory(dirname, dirpath, references):
    """Categorize a directory based on name and references"""
    
    # Core directories
    if dirname in ['thielecpu', 'coq', 'demos', 'tests', 'scripts', 'tools', 'docs', 'web']:
        return 'CORE'
    
    # Build artifacts
    if dirname in ['build', 'dist', '__pycache__', '.pytest_cache', '.mypy_cache']:
        return 'BUILD_ARTIFACT'
    
    # Output directories (likely experiment results)
    output_patterns = [
        'output', 'results', 'demo', '_out', '_work', 'test_',
        'random_', 'shor_', 'graph_', 'stress_', 'thesis_'
    ]
    if any(pattern in dirname.lower() for pattern in output_patterns):
        if not references or len(references) < 3:
            return 'OLD_OUTPUT'
        return 'ACTIVE_OUTPUT'
    
    # Archive
    if 'archive' in dirname.lower() or 'backup' in dirname.lower():
        return 'ARCHIVE'
    
    # Config/Data
    if dirname in ['configs', 'data', 'artifacts', 'receipts', 'checksums']:
        return 'DATA'
    
    # Unknown but has references
    if references and len(references) > 5:
        return 'ACTIVE_UNKNOWN'
    
    # Unknown with few/no references
    return 'INACTIVE_UNKNOWN'

def generate_report(results):
    """Generate human-readable report"""
    
    categories = defaultdict(list)
    for dirname, data in results.items():
        categories[data['category']].append((dirname, data))
    
    report = []
    report.append("=" * 80)
    report.append("DIRECTORY AUDIT REPORT")
    report.append("=" * 80)
    report.append("")
    
    for category in ['CORE', 'ACTIVE_OUTPUT', 'OLD_OUTPUT', 'DATA', 'ARCHIVE', 
                     'ACTIVE_UNKNOWN', 'INACTIVE_UNKNOWN', 'BUILD_ARTIFACT']:
        if category not in categories:
            continue
        
        report.append(f"\n{'='*80}")
        report.append(f"CATEGORY: {category}")
        report.append('='*80)
        
        for dirname, data in sorted(categories[category]):
            info = data['info']
            report.append(f"\n📁 {dirname}/")
            report.append(f"   Files: {info['file_count']}, Size: {info['total_size_mb']} MB")
            report.append(f"   Created: {info['created'][:10] if info['created'] != 'Unknown' else 'Unknown'}")
            report.append(f"   Modified: {info['last_modified'][:10] if info['last_modified'] != 'Unknown' else 'Unknown'}")
            report.append(f"   References in code: {data['reference_count']}")
            
            if data['references']:
                report.append(f"   Source files:")
                for ref in data['references'][:3]:
                    report.append(f"     - {ref['file']}")
            
            # Recommendation
            if category == 'OLD_OUTPUT':
                report.append(f"   ⚠️  RECOMMENDATION: Archive to results/archive/")
            elif category == 'BUILD_ARTIFACT':
                report.append(f"   🗑️  RECOMMENDATION: Delete (add to .gitignore)")
            elif category == 'INACTIVE_UNKNOWN':
                report.append(f"   ❓ RECOMMENDATION: Investigate purpose or delete")
            elif category == 'ACTIVE_OUTPUT':
                report.append(f"   🔧 RECOMMENDATION: Fix source to use results/ subdirectory")
    
    report.append("\n" + "=" * 80)
    report.append("END REPORT")
    report.append("=" * 80)
    
    return '\n'.join(report)

def save_json_report(results, output_file):
    """Save detailed JSON report"""
    with open(output_file, 'w') as f:
        json.dump(results, f, indent=2)
    print(f"\n✓ JSON report saved to: {output_file}")

def main():
    print("Starting comprehensive directory audit...")
    print(f"Repository root: {REPO_ROOT}")
    print()
    
    results = analyze_all_directories()
    
    # Generate reports
    text_report = generate_report(results)
    print(text_report)
    
    # Save reports
    report_dir = REPO_ROOT / "audit_logs"
    report_dir.mkdir(exist_ok=True)
    
    text_file = report_dir / "directory_audit_report.txt"
    json_file = report_dir / "directory_audit_report.json"
    
    with open(text_file, 'w') as f:
        f.write(text_report)
    print(f"\n✓ Text report saved to: {text_file}")
    
    save_json_report(results, json_file)
    
    print("\n" + "=" * 80)
    print("NEXT STEPS:")
    print("=" * 80)
    print("1. Review the audit reports in audit_logs/")
    print("2. Update DIRECTORY_AUDIT.md with findings")
    print("3. Fix source code for ACTIVE_OUTPUT directories")
    print("4. Archive OLD_OUTPUT directories")
    print("5. Delete BUILD_ARTIFACT directories")
    print("6. Investigate INACTIVE_UNKNOWN directories")
    print()

if __name__ == '__main__':
    main()
