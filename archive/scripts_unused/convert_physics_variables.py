#!/usr/bin/env python3
"""
Convert Variable declarations to Axiom in physics_exploration files.
"""

import re
from pathlib import Path

def convert_file(filepath):
    """Convert Variable to Axiom in a Coq file."""
    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()

    lines = content.split('\n')
    new_lines = []
    in_section = False
    changes_made = 0

    for line in lines:
        if re.match(r'^\s*Section\s+', line):
            in_section = True
        elif re.match(r'^\s*End\s+', line):
            in_section = False

        if not in_section and re.match(r'^Variable\s+', line):
            new_line = re.sub(r'^Variable\s+', 'Axiom ', line)
            if new_line != line:
                changes_made += 1
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
    physics_dir = Path(__file__).parent.parent / 'coq' / 'physics_exploration'

    total_changes = 0
    for filepath in sorted(physics_dir.glob('*.v')):
        changes = convert_file(filepath)
        if changes > 0:
            print(f"{filepath.name}: {changes} conversions")
            total_changes += changes

    print(f"\nTotal: {total_changes} conversions")

if __name__ == '__main__':
    main()
