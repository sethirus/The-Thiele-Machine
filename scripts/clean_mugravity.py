"""
Surgical deletion of false axioms and invalid theorems from MuGravity.v

This script:
1. Reads MuGravity.v
2. Deletes the three false axioms
3. Deletes all theorems that depend on them
4. Keeps all valid definitions and theorems
5. Writes cleaned file
"""

# Theorems/definitions to DELETE (use false axioms)
DELETE_ITEMS = [
    "geometric_calibration_axiom",
    "source_normalization_axiom",
    "horizon_cycle_axiom",
    "geometric_calibration_semantics_from_kernel",
    "source_normalization_semantics_from_kernel",
    "source_normalization_certificate_from_equation",
    "angle_defect_equals_laplacian",
    "curvature_stress_balance",
    "einstein_equation",
    "horizon_cycle_certificate_from_components",
    "horizon_cycle_semantics_from_kernel",
    "bekenstein_hawking_from_angle_defect",
    "geometric_calibration_certificate_from_residual_zero",
    "zero_residual_implies_calibrated",
    "calibration_residual_zero_iff",
]

# Also delete these Notations (they define the false equalities)
DELETE_NOTATIONS = [
    "geometric_calibration_semantics",
    "source_normalization_semantics",
    "geometric_calibration_certificate",
    "source_normalization_certificate",
    "horizon_cycle_semantics",
    "horizon_cycle_certificate",
]

def find_item_range(lines, item_name):
    """
    Find the line range of a theorem/lemma/axiom declaration and its proof.
    Returns (start_line, end_line) or None if not found.
    """
    # Find the declaration
    decl_line = None
    for i, line in enumerate(lines):
        # Match "Theorem name", "Lemma name", "Axiom name", "Notation name"
        if any(line.strip().startswith(f"{kw} {item_name} ") or
               line.strip().startswith(f"{kw} {item_name}:")
               for kw in ["Theorem", "Lemma", "Axiom", "Definition", "Notation"]):
            decl_line = i
            break

    if decl_line is None:
        return None

    # Find the end (either Qed, Defined, or just the notation line)
    if lines[decl_line].strip().startswith("Notation"):
        # Notations are single lines (or a few lines)
        # Find the next line that ends with period
        end_line = decl_line
        while end_line < len(lines) - 1:
            if lines[end_line].rstrip().endswith('.'):
                break
            end_line += 1
        return (decl_line, end_line + 1)

    # For Theorem/Lemma/Axiom, find Qed/Defined/Admitted or just the axiom declaration
    end_line = decl_line
    for i in range(decl_line + 1, len(lines)):
        stripped = lines[i].strip()
        if stripped in ["Qed.", "Defined.", "Admitted."]:
            end_line = i
            break
        # For axioms without proof, the declaration itself might span multiple lines
        # and end with a period
        if lines[decl_line].strip().startswith("Axiom"):
            if stripped.endswith('.') and not stripped.startswith('(*'):
                end_line = i
                break

    return (decl_line, end_line + 1)

def delete_comments_before(lines, start_line, max_lookback=50):
    """
    Delete comment blocks immediately before a declaration.
    Returns the new start line.
    """
    # Look backwards for comment blocks
    i = start_line - 1
    while i >= max(0, start_line - max_lookback):
        stripped = lines[i].strip()
        # If we hit a non-comment, non-blank line, stop
        if stripped and not stripped.startswith('(*') and not stripped.startswith('*') and not stripped.endswith('*)'):
            break
        # If it's a comment start, this is our new start
        if '(*' in stripped:
            return i
        i -= 1

    return start_line

def main():
    input_file = "/workspaces/The-Thiele-Machine/coq/kernel/MuGravity.v"
    output_file = "/workspaces/The-Thiele-Machine/coq/kernel/MuGravity_cleaned.v"

    with open(input_file, 'r') as f:
        lines = f.readlines()

    # Collect all ranges to delete
    delete_ranges = []

    # Find each item to delete
    for item in DELETE_ITEMS + DELETE_NOTATIONS:
        item_range = find_item_range(lines, item)
        if item_range:
            start, end = item_range
            # Also delete comments before
            start_with_comments = delete_comments_before(lines, start)
            delete_ranges.append((start_with_comments, end))
            print(f"Will delete {item}: lines {start_with_comments+1}-{end}")
        else:
            print(f"NOT FOUND: {item}")

    # Sort ranges
    delete_ranges.sort()

    # Merge overlapping ranges
    merged = []
    for start, end in delete_ranges:
        if merged and start <= merged[-1][1]:
            # Overlapping - extend previous range
            merged[-1] = (merged[-1][0], max(end, merged[-1][1]))
        else:
            merged.append((start, end))

    print(f"\nMerged into {len(merged)} deletion ranges")

    # Build output
    output_lines = []
    current_pos = 0

    for start, end in merged:
        # Add lines before this deletion
        output_lines.extend(lines[current_pos:start])
        current_pos = end

    # Add remaining lines
    output_lines.extend(lines[current_pos:])

    # Write output
    with open(output_file, 'w') as f:
        f.writelines(output_lines)

    original_count = len(lines)
    output_count = len(output_lines)
    deleted_count = original_count - output_count

    print(f"\nOriginal: {original_count} lines")
    print(f"Output: {output_count} lines")
    print(f"Deleted: {deleted_count} lines ({100*deleted_count/original_count:.1f}%)")
    print(f"\nCleaned file written to: {output_file}")

if __name__ == "__main__":
    main()
