#!/usr/bin/env python3
"""Analyze admits and axioms in Coq files."""

import os
import re
from pathlib import Path
from collections import defaultdict

def find_admits_and_axioms(root_dir):
    """Find all admits and axioms in .v files."""
    results = defaultdict(list)

    for path in Path(root_dir).rglob("*.v"):
        with open(path, 'r', encoding='utf-8', errors='ignore') as f:
            lines = f.readlines()

        for i, line in enumerate(lines, 1):
            # Find admits (not in comments)
            if re.match(r'^\s*admit\.\s*$', line) or re.match(r'^\s*Admitted\.\s*$', line):
                # Get context (previous 3 lines)
                context_start = max(0, i-4)
                context = ''.join(lines[context_start:i])
                results[str(path)].append({
                    'type': 'admit',
                    'line': i,
                    'context': context.strip()
                })

            # Find axioms (not in comments)
            if re.match(r'^\s*Axiom\s+\w+', line):
                results[str(path)].append({
                    'type': 'axiom',
                    'line': i,
                    'context': line.strip()
                })

    return results

def main():
    root = "/home/user/The-Thiele-Machine/coq"
    results = find_admits_and_axioms(root)

    # Print summary
    total_admits = sum(1 for items in results.values() for item in items if item['type'] == 'admit')
    total_axioms = sum(1 for items in results.values() for item in items if item['type'] == 'axiom')

    print(f"=== SUMMARY ===")
    print(f"Total admits: {total_admits}")
    print(f"Total axioms: {total_axioms}")
    print(f"Files with admits/axioms: {len(results)}")
    print()

    # Print admits by file
    print("=== ADMITS BY FILE ===")
    for filepath in sorted(results.keys()):
        admits = [item for item in results[filepath] if item['type'] == 'admit']
        if admits:
            filename = os.path.basename(filepath)
            print(f"\n{filename} ({len(admits)} admits):")
            for admit in admits:
                print(f"  Line {admit['line']}")
                # Print last line of context
                context_lines = admit['context'].split('\n')
                if len(context_lines) > 1:
                    print(f"    Context: {context_lines[-2][:80]}")

    # Print axioms by file
    print("\n\n=== AXIOMS BY FILE ===")
    for filepath in sorted(results.keys()):
        axioms = [item for item in results[filepath] if item['type'] == 'axiom']
        if axioms:
            filename = os.path.basename(filepath)
            print(f"\n{filename} ({len(axioms)} axioms):")
            for axiom in axioms:
                print(f"  Line {axiom['line']}: {axiom['context'][:80]}")

if __name__ == '__main__':
    main()
