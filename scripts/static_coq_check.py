#!/usr/bin/env python3
"""Static Coq file analyzer - checks for common issues without compilation."""

import re
import sys
from pathlib import Path
from collections import defaultdict

def check_balanced_delimiters(content, filepath):
    """Check for balanced parentheses, brackets, braces."""
    issues = []
    stack = []
    pairs = {'(': ')', '[': ']', '{': '}'}
    reverse_pairs = {v: k for k, v in pairs.items()}

    for i, char in enumerate(content):
        if char in pairs:
            stack.append((char, i))
        elif char in reverse_pairs:
            if not stack:
                issues.append(f"Unmatched closing '{char}' at position {i}")
            else:
                open_char, _ = stack.pop()
                if pairs[open_char] != char:
                    issues.append(f"Mismatched delimiter: '{open_char}' closed by '{char}' at position {i}")

    for char, pos in stack:
        issues.append(f"Unclosed '{char}' at position {pos}")

    return issues

def check_proof_structure(content, filepath):
    """Check for incomplete proofs, admits, axioms."""
    issues = []

    # Check for Admitted
    if re.search(r'\bAdmitted\s*\.', content):
        matches = re.finditer(r'\bAdmitted\s*\.', content)
        for match in matches:
            line_num = content[:match.start()].count('\n') + 1
            issues.append(f"Line {line_num}: ADMITTED found (incomplete proof)")

    # Check for admit tactic
    if re.search(r'\badmit\s*\.', content):
        matches = re.finditer(r'\badmit\s*\.', content)
        for match in matches:
            line_num = content[:match.start()].count('\n') + 1
            issues.append(f"Line {line_num}: admit tactic found")

    # Check for Axioms (report but don't fail - some are expected)
    axiom_matches = re.finditer(r'^\s*(Axiom|Parameter)\s+(\w+)', content, re.MULTILINE)
    axioms = []
    for match in axiom_matches:
        line_num = content[:match.start()].count('\n') + 1
        axioms.append(f"Line {line_num}: Axiom/Parameter '{match.group(2)}'")

    # Check for proofs without Qed/Defined/Admitted
    proof_starts = list(re.finditer(r'\bProof\s*\.', content))
    for start_match in proof_starts:
        start_pos = start_match.end()
        # Look for corresponding Qed/Defined/Admitted
        end_match = re.search(r'\b(Qed|Defined|Admitted)\s*\.', content[start_pos:])
        if not end_match:
            line_num = content[:start_match.start()].count('\n') + 1
            issues.append(f"Line {line_num}: Proof without Qed/Defined/Admitted")

    return issues, axioms

def check_imports(content, filepath):
    """Check for potentially problematic imports."""
    issues = []

    # Check for Classical axioms
    if re.search(r'Require\s+Import\s+Classical', content):
        matches = re.finditer(r'Require\s+Import\s+Classical', content)
        for match in matches:
            line_num = content[:match.start()].count('\n') + 1
            issues.append(f"Line {line_num}: Classical logic imported (uses LEM)")

    return issues

def check_syntax_patterns(content, filepath):
    """Check for common syntax issues."""
    issues = []

    # Check for common typos
    if re.search(r'\bLemam\b', content):
        issues.append("Typo: 'Lemam' should be 'Lemma'")

    if re.search(r'\bTheorm\b', content):
        issues.append("Typo: 'Theorm' should be 'Theorem'")

    # Check for unbalanced comments
    open_comments = len(re.findall(r'\(\*', content))
    close_comments = len(re.findall(r'\*\)', content))
    if open_comments != close_comments:
        issues.append(f"Unbalanced comments: {open_comments} open, {close_comments} closed")

    return issues

def analyze_file(filepath):
    """Analyze a single Coq file."""
    try:
        with open(filepath, 'r', encoding='utf-8', errors='ignore') as f:
            content = f.read()
    except Exception as e:
        return None, None, [f"Error reading file: {e}"]

    all_issues = []
    axioms = []

    # Run all checks
    all_issues.extend(check_balanced_delimiters(content, filepath))
    proof_issues, file_axioms = check_proof_structure(content, filepath)
    all_issues.extend(proof_issues)
    axioms.extend(file_axioms)
    all_issues.extend(check_imports(content, filepath))
    all_issues.extend(check_syntax_patterns(content, filepath))

    return content, axioms, all_issues

def main():
    repo_root = Path(__file__).parent.parent
    coq_root = repo_root / "coq"

    if not coq_root.exists():
        print(f"ERROR: Coq directory not found at {coq_root}")
        return 1

    print("=" * 70)
    print("STATIC COQ FILE ANALYSIS")
    print("=" * 70)
    print(f"Scanning: {coq_root}")
    print()

    # Find all .v files
    coq_files = sorted(coq_root.rglob("*.v"))
    print(f"Found {len(coq_files)} Coq files")
    print()

    critical_files = []
    files_with_issues = []
    all_axioms = defaultdict(list)
    total_admits = 0

    for filepath in coq_files:
        content, axioms, issues = analyze_file(filepath)
        if content is None:
            continue

        rel_path = filepath.relative_to(repo_root)

        # Check for admits
        if re.search(r'\b(Admitted|admit)\b', content):
            total_admits += len(re.findall(r'\b(Admitted|admit)\b', content))
            if 'kernel/' in str(rel_path):
                critical_files.append(str(rel_path))

        # Collect axioms
        for axiom in axioms:
            all_axioms[str(rel_path)].append(axiom)

        # Report issues
        if issues:
            files_with_issues.append((rel_path, issues))

    # Print results
    print("=" * 70)
    print("CRITICAL CHECKS")
    print("=" * 70)

    if critical_files:
        print(f"❌ KERNEL FILES WITH ADMITS: {len(critical_files)}")
        for f in critical_files[:10]:
            print(f"   - {f}")
        if len(critical_files) > 10:
            print(f"   ... and {len(critical_files) - 10} more")
    else:
        print("✅ ZERO admits in kernel/ files")

    print()
    print(f"Total admits across all files: {total_admits}")
    print()

    # Print files with issues
    if files_with_issues:
        print("=" * 70)
        print(f"FILES WITH ISSUES: {len(files_with_issues)}")
        print("=" * 70)
        for filepath, issues in files_with_issues[:20]:
            print(f"\n{filepath}")
            for issue in issues[:5]:
                print(f"   - {issue}")
            if len(issues) > 5:
                print(f"   ... and {len(issues) - 5} more issues")

        if len(files_with_issues) > 20:
            print(f"\n... and {len(files_with_issues) - 20} more files with issues")
    else:
        print("✅ No structural issues found")

    print()
    print("=" * 70)
    print("AXIOMS SUMMARY")
    print("=" * 70)
    print(f"Files with axioms: {len(all_axioms)}")

    # Count unique axioms
    unique_axioms = set()
    for axiom_list in all_axioms.values():
        for axiom in axiom_list:
            # Extract axiom name from "Line X: Axiom/Parameter 'name'"
            match = re.search(r"'(\w+)'", axiom)
            if match:
                unique_axioms.add(match.group(1))

    print(f"Unique axiom names: {len(unique_axioms)}")
    print()

    print("=" * 70)
    print("ANALYSIS COMPLETE")
    print("=" * 70)
    print()
    print("Note: This is a static analysis. Full compilation with coqc required")
    print("      to verify type correctness and tactic validity.")
    print()

    # Return 0 if no critical issues
    if critical_files:
        return 1
    return 0

if __name__ == "__main__":
    sys.exit(main())
