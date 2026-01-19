#!/usr/bin/env python3
"""
Convert Variable declarations to Axiom in Coq kernel files.

Variable is for section-local assumptions.
Axiom is for top-level global assumptions.

This script converts Variable → Axiom for documented external mathematical results.
"""

import re
import sys
from pathlib import Path

def convert_file(filepath):
    """Convert Variable to Axiom in a Coq file."""
    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()

    # Track if we're inside a Section
    lines = content.split('\n')
    new_lines = []
    in_section = False
    changes_made = 0

    for line in lines:
        # Track Section blocks
        if re.match(r'^\s*Section\s+', line):
            in_section = True
        elif re.match(r'^\s*End\s+', line):
            in_section = False

        # Convert Variable to Axiom only if NOT in a Section
        if not in_section and re.match(r'^Variable\s+', line):
            new_line = re.sub(r'^Variable\s+', 'Axiom ', line)
            if new_line != line:
                changes_made += 1
                print(f"  Line {len(new_lines)+1}: Variable → Axiom")
            new_lines.append(new_line)
        else:
            new_lines.append(line)

    if changes_made > 0:
        new_content = '\n'.join(new_lines)
        with open(filepath, 'w', encoding='utf-8') as f:
            f.write(new_content)
        return changes_made
    return 0

def main():
    kernel_dir = Path(__file__).parent.parent / 'coq' / 'kernel'

    # Files to convert
    files_to_convert = [
        'TsirelsonBoundProof.v',
        'QuantumBoundComplete.v',
        'SemidefiniteProgramming.v',
        'NPAMomentMatrix.v',
        'MinorConstraints.v',
        'MuLedgerConservation.v',
        'TsirelsonUniqueness.v',
        'BoxCHSH.v',
        'ModularObservation.v',
        'FiniteInformation.v',
        'QuantumBound.v',
    ]

    total_changes = 0
    for filename in files_to_convert:
        filepath = kernel_dir / filename
        if filepath.exists():
            print(f"\nProcessing {filename}...")
            changes = convert_file(filepath)
            if changes > 0:
                print(f"  ✓ Converted {changes} Variable → Axiom")
                total_changes += changes
            else:
                print(f"  ✓ No changes needed")
        else:
            print(f"\n⚠ Skipping {filename} (not found)")

    print(f"\n{'='*60}")
    print(f"Total conversions: {total_changes}")
    print(f"{'='*60}")

if __name__ == '__main__':
    main()
