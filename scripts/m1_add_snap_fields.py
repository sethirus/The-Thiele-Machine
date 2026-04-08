#!/usr/bin/env python3
"""M1: Add 6 new fields to KamiSnapshot and propagate them through all constructions.

New fields: snap_csr_cert_addr, snap_csr_status, snap_csr_err, snap_csr_heap_base,
            snap_logic_acc, snap_mstatus.
"""

import re
import sys

def transform(text: str) -> str:
    # === 1. Add 6 fields to KamiSnapshot record definition ===
    # Insert after snap_rich_state line in the record
    old_rich_field = "  snap_rich_state    : RichSnapshotState\n}."
    new_rich_field = (
        "  snap_rich_state    : RichSnapshotState ;\n"
        "  (* --- M1 unification fields: CSR / logic_acc / mstatus --- *)\n"
        "  snap_csr_cert_addr : nat ;   (* mirrors CSRState.csr_cert_addr *)\n"
        "  snap_csr_status    : nat ;   (* mirrors CSRState.csr_status *)\n"
        "  snap_csr_err       : nat ;   (* mirrors CSRState.csr_err *)\n"
        "  snap_csr_heap_base : nat ;   (* mirrors CSRState.csr_heap_base *)\n"
        "  snap_logic_acc     : nat ;   (* mirrors VMState.vm_logic_acc *)\n"
        "  snap_mstatus       : nat     (* mirrors VMState.vm_mstatus *)\n"
        "}."
    )
    if old_rich_field not in text:
        print("ERROR: Could not find KamiSnapshot record closing field", file=sys.stderr)
        sys.exit(1)
    text = text.replace(old_rich_field, new_rich_field, 1)

    # === 2. Update abs_phase1 to use new fields ===
    text = text.replace(
        "     vm_csrs      := default_csrs ;",
        "     vm_csrs      := {| csr_cert_addr := snap_csr_cert_addr s;\n"
        "                        csr_status    := snap_csr_status s;\n"
        "                        csr_err       := snap_csr_err s;\n"
        "                        csr_heap_base := snap_csr_heap_base s |} ;",
        1
    )
    text = text.replace(
        "     vm_logic_acc := 0 ;",
        "     vm_logic_acc := snap_logic_acc s ;",
        1
    )
    text = text.replace(
        "     vm_mstatus   := 0 ;",
        "     vm_mstatus   := snap_mstatus s ;",
        1
    )

    # === 3. Add 6 new field assignments to every KamiSnapshot record construction ===
    # Pattern: "snap_rich_state := EXPR |}" at end of record construction
    # We need to add 6 new fields between the rich_state line and the closing "|}"
    #
    # But we need to figure out the source snapshot name. In nearly all cases it's "hs".
    # The one exception is abs_phase1 which builds a VMState, not KamiSnapshot.

    # We handle two patterns:
    # A) "snap_rich_state := snap_rich_state hs |}" -> propagate from hs
    # B) "snap_rich_state := rs' |}" -> propagate from hs (the KamiSnapshot param)
    # C) "snap_rich_state := snap_rich_state hs |} in" -> propagate from hs (local let)

    # Generic regex: match "snap_rich_state := EXPR |}" or "snap_rich_state := EXPR |} in"
    # and inject new fields before the closing

    new_fields_hs = (
        "{indent}snap_csr_cert_addr := snap_csr_cert_addr hs;\n"
        "{indent}snap_csr_status    := snap_csr_status hs;\n"
        "{indent}snap_csr_err       := snap_csr_err hs;\n"
        "{indent}snap_csr_heap_base := snap_csr_heap_base hs;\n"
        "{indent}snap_logic_acc     := snap_logic_acc hs;\n"
        "{indent}snap_mstatus       := snap_mstatus hs"
    )

    # Find all occurrences of "snap_rich_state := EXPR |}" patterns
    # We use a line-by-line approach for precision

    lines = text.split('\n')
    new_lines = []
    i = 0
    while i < len(lines):
        line = lines[i]
        # Check if this line contains "snap_rich_state :=" and ends the record
        stripped = line.strip()

        # Pattern: "snap_rich_state := SOMETHING |}" or "snap_rich_state := SOMETHING |} in"
        m = re.match(r'^(\s+)snap_rich_state\s*:=\s*(.+?)\s*(\|}\s*(?:in)?)(.*)$', line)
        if m:
            indent = m.group(1)
            expr = m.group(2)
            closing = m.group(3)
            rest = m.group(4)
            # Remove the closing from the original line and add fields + closing
            new_line = f"{indent}snap_rich_state    := {expr};"
            new_lines.append(new_line)
            for fname, fval in [
                ("snap_csr_cert_addr", "snap_csr_cert_addr hs"),
                ("snap_csr_status   ", "snap_csr_status hs"),
                ("snap_csr_err      ", "snap_csr_err hs"),
                ("snap_csr_heap_base", "snap_csr_heap_base hs"),
                ("snap_logic_acc    ", "snap_logic_acc hs"),
                ("snap_mstatus      ", "snap_mstatus hs"),
            ]:
                new_lines.append(f"{indent}{fname} := {fval};")
            # Fix last line: remove trailing ; and add closing
            new_lines[-1] = new_lines[-1].rstrip(';') + " " + closing.strip() + rest
            i += 1
            continue

        # Also handle multi-line pattern where |} is on next line
        m2 = re.match(r'^(\s+)snap_rich_state\s*:=\s*(.+?)$', line)
        if m2 and not line.strip().endswith('|}') and not line.strip().endswith('|} in'):
            # Check if next line is just "|}" or "|} in"
            if i + 1 < len(lines):
                next_stripped = lines[i+1].strip()
                if next_stripped.startswith('|}'):
                    indent = m2.group(1)
                    expr = m2.group(2).rstrip().rstrip(';')
                    new_line = f"{indent}snap_rich_state    := {expr};"
                    new_lines.append(new_line)
                    for fname, fval in [
                        ("snap_csr_cert_addr", "snap_csr_cert_addr hs"),
                        ("snap_csr_status   ", "snap_csr_status hs"),
                        ("snap_csr_err      ", "snap_csr_err hs"),
                        ("snap_csr_heap_base", "snap_csr_heap_base hs"),
                        ("snap_logic_acc    ", "snap_logic_acc hs"),
                        ("snap_mstatus      ", "snap_mstatus hs"),
                    ]:
                        new_lines.append(f"{indent}{fname} := {fval};")
                    new_lines[-1] = new_lines[-1].rstrip(';') + " " + next_stripped
                    i += 2
                    continue

        new_lines.append(line)
        i += 1

    text = '\n'.join(new_lines)

    # === 4. Verify we got all constructions ===
    # Count remaining "|}" after "snap_rich_state" that DON'T have the new fields
    count_old = text.count('snap_rich_state')
    count_new = text.count('snap_csr_cert_addr')
    print(f"snap_rich_state occurrences: {count_old}", file=sys.stderr)
    print(f"snap_csr_cert_addr occurrences: {count_new}", file=sys.stderr)

    return text

if __name__ == '__main__':
    path = sys.argv[1] if len(sys.argv) > 1 else '/workspaces/The-Thiele-Machine/coq/kami_hw/Abstraction.v'
    with open(path, 'r') as f:
        original = f.read()
    result = transform(original)
    with open(path, 'w') as f:
        f.write(result)
    print(f"Done. File updated: {path}", file=sys.stderr)
