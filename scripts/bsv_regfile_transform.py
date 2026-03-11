#!/usr/bin/env python3
"""Transform extracted BSV to use RegFile for large Vector registers.

The Kami extraction pipeline generates BSV like:
  Reg#(Vector#(4096, Bit#(32))) mem <- mkReg(unpack(0));
which BSC cannot elaborate (stack overflow on Vector#(4096,...) default value).

This script replaces such registers with RegFile#(...) and rewrites all
read/write patterns, enabling BSC to compile the design.

This is a legitimate part of the extraction pipeline:
  Coq -> OCaml -> BSV -> **this transform** -> BSC -> Verilog

The logic (instruction decode, register update computation, error handling)
is UNCHANGED -- only the memory storage primitive is swapped.
"""

import re
import sys


# Threshold: vectors with >= this many elements get converted to RegFile
REGFILE_THRESHOLD = 256


def transform_bsv(bsv: str) -> str:
    """Main transformation: replace large Reg#(Vector#(...)) with RegFile#."""

    # Step 1: Find large vector register declarations
    decl_pat = re.compile(
        r'Reg#\(Vector#\((\d+),\s*(Bit#\(\d+\))\)\)\s+(\w+)\s+<-\s+mkReg\(unpack\(0\)\);'
    )
    regfile_regs = {}  # name -> {n_elems, elem_type, addr_bits}
    for m in decl_pat.finditer(bsv):
        n_elems = int(m.group(1))
        elem_type = m.group(2)
        name = m.group(3)
        if n_elems >= REGFILE_THRESHOLD:
            addr_bits = (n_elems - 1).bit_length()
            regfile_regs[name] = {
                'n_elems': n_elems,
                'elem_type': elem_type,
                'addr_bits': addr_bits,
                'full_match': m.group(0),
            }
            print(f"  RegFile transform: {name} Vector#({n_elems}, {elem_type}) -> "
                  f"RegFile#(Bit#({addr_bits}), {elem_type})", file=sys.stderr)

    if not regfile_regs:
        print("  No large vector registers found (threshold=%d)." % REGFILE_THRESHOLD,
              file=sys.stderr)
        return bsv

    # Step 2: Replace declarations
    for name, info in regfile_regs.items():
        old_decl = info['full_match']
        new_decl = (f"RegFile#(Bit#({info['addr_bits']}), {info['elem_type']}) "
                    f"{name} <- mkRegFileFullZero();")
        bsv = bsv.replace(old_decl, new_decl)

    # Step 3: Split into scopes (rule/method bodies) and process each independently
    # This prevents alias collisions across methods (e.g., x_1 = imem in one method
    # vs x_1 = mu_tensor in another)
    bsv = _transform_scoped(bsv, regfile_regs)

    return bsv


def _transform_scoped(bsv: str, regfile_regs: dict) -> str:
    """Process each rule/method body independently to avoid cross-scope alias collisions."""

    # Split BSV into segments: alternating between "outside scope" and "inside scope"
    # Scopes start with "rule <name>;" or "method ... ;" and end with "endrule" or "endmethod"
    scope_start_pat = re.compile(r'^(\s*(?:rule\s+\w+|method\s+.+?);)\s*$', re.MULTILINE)
    scope_end_pat = re.compile(r'^\s*(endrule|endmethod)\s*$', re.MULTILINE)

    result = []
    pos = 0

    while pos < len(bsv):
        # Find the next scope start
        start_m = scope_start_pat.search(bsv, pos)
        if not start_m:
            result.append(bsv[pos:])
            break

        # Add everything before this scope
        result.append(bsv[pos:start_m.start()])

        # Find the matching end
        end_m = scope_end_pat.search(bsv, start_m.end())
        if not end_m:
            result.append(bsv[start_m.start():])
            break

        # Extract the scope header, body, and footer
        header = start_m.group(0)
        body = bsv[start_m.end():end_m.start()]
        footer = end_m.group(0)

        # Transform the body
        transformed_body = _transform_scope_body(body, regfile_regs)

        result.append(header)
        result.append(transformed_body)
        result.append(footer)

        pos = end_m.end()

    return ''.join(result)


def _transform_scope_body(body: str, regfile_regs: dict) -> str:
    """Transform a single rule/method body."""

    # Step 1: Find aliases within this scope
    alias_pat = re.compile(r'let\s+(x_\d+)\s*=\s*\((\w+)\);')
    alias_map = {}  # alias_var -> reg_name (only for regfile regs)
    for m in alias_pat.finditer(body):
        var = m.group(1)
        reg = m.group(2)
        if reg in regfile_regs:
            alias_map[var] = reg

    # Step 2: Remove alias lines for RegFile registers
    for alias, reg in alias_map.items():
        alias_line_pat = re.compile(
            rf'^\s*let\s+{re.escape(alias)}\s*=\s*\({re.escape(reg)}\);\s*$',
            re.MULTILINE
        )
        body = alias_line_pat.sub('', body)

    # Step 3: Replace index reads: (alias)[expr] -> reg.sub(expr)
    for alias, reg in alias_map.items():
        read_pat = re.compile(rf'\({re.escape(alias)}\)\[([^\]]+)\]')
        body = read_pat.sub(rf'{reg}.sub(\1)', body)

    # Step 4: Transform writes
    for name, info in regfile_regs.items():
        alias = None
        for a, r in alias_map.items():
            if r == name:
                alias = a
                break
        if not alias:
            continue

        body = _transform_writes(body, name, alias, info)

    return body


def _transform_writes(body: str, reg_name: str, alias: str, info: dict) -> str:
    """Transform write patterns for a RegFile register within a scope body."""

    # Pattern 1: Simple direct write
    # reg <= update(alias, addr, val);
    simple_pat = re.compile(
        rf'(\s*){re.escape(reg_name)}\s*<=\s*update\s*\({re.escape(alias)},\s*'
        rf'([^,]+),\s*([^)]+)\);\s*$',
        re.MULTILINE
    )
    body = simple_pat.sub(
        rf'\1{reg_name}.upd(\2, \3);',
        body
    )

    # Pattern 2: Conditional with vector result variable
    # Vector#(N, T) x_result = (complex_ternary_with_update);
    # ...
    # reg <= x_result;
    write_back_pat = re.compile(
        rf'(\s*){re.escape(reg_name)}\s*<=\s*(x_\d+);\s*$', re.MULTILINE
    )
    for wm in write_back_pat.finditer(body):
        result_var = wm.group(2)
        indent = wm.group(1)

        # Find the assignment to result_var
        assign_pat = re.compile(
            rf'(\s*)Vector#\({info["n_elems"]},\s*{re.escape(info["elem_type"])}\)\s+'
            rf'{re.escape(result_var)}\s*=\s*\((.+?)\);\s*$',
            re.MULTILINE | re.DOTALL
        )
        am = assign_pat.search(body)
        if not am:
            continue

        assign_full = am.group(0)
        assign_expr = am.group(2)
        assign_indent = am.group(1) or '        '

        # Parse the expression and generate .upd() calls
        upd_code = _generate_upd_calls(
            reg_name, alias, assign_expr, assign_indent.strip() or '        '
        )

        if upd_code:
            # Remove the Vector assignment (replace with newline to avoid line concatenation)
            body = body.replace(assign_full, '\n')
            # Replace the reg <= x_result with upd calls (ensure newline before)
            old_write = wm.group(0)
            body = body.replace(old_write, '\n' + upd_code)

    return body


def _generate_upd_calls(reg_name: str, alias: str, expr: str, indent: str) -> str:
    """Generate RegFile .upd() calls from a conditional update expression.

    Generates individual if statements. Only one opcode matches per cycle,
    so individual ifs are semantically equivalent to else-if.
    """
    indent = '        '

    # Extract the guard and the update branches
    guard = _extract_guard(expr, alias)
    updates = _extract_updates_simple(expr, alias)

    if not updates:
        return None

    # Normalize guard: collapse whitespace/newlines to single line
    if guard:
        guard = ' '.join(guard.split())

    lines = []
    for cond, addr, val in updates:
        cond = ' '.join(cond.split())
        if guard:
            full_cond = f'(!({guard})) && ({cond})'
        else:
            full_cond = cond
        lines.append(f'{indent}if ({full_cond}) {reg_name}.upd({addr}, {val});')

    return '\n'.join(lines) + '\n'


def _extract_guard(expr: str, alias: str) -> str:
    """Extract the top-level guard: the condition where the register is NOT written.

    Pattern: (big_guard ? (alias) : (write_tree))
    Returns the guard string, or None.
    """
    # Find the first ` ? (alias) :` or ` ? alias :`
    markers = [f'? ({alias}) :', f'? {alias} :']
    idx = -1
    for marker in markers:
        idx = expr.find(marker)
        if idx != -1:
            break
    if idx == -1:
        return None

    guard = expr[:idx].strip()

    # The guard may include extra opening parens from the ternary expression wrapper.
    # Ensure the result is paren-balanced by stripping leading unmatched '('.
    depth = 0
    for c in guard:
        if c == '(':
            depth += 1
        elif c == ')':
            depth -= 1

    while depth > 0 and guard.startswith('('):
        guard = guard[1:].strip()
        depth -= 1

    return guard


def _strip_balanced_parens(s: str) -> str:
    """Remove outermost balanced parentheses."""
    while len(s) >= 2 and s[0] == '(' and s[-1] == ')':
        depth = 0
        balanced = True
        for i, c in enumerate(s[1:-1], 1):
            if c == '(':
                depth += 1
            elif c == ')':
                depth -= 1
                if depth < 0:
                    balanced = False
                    break
        if balanced and depth == 0:
            s = s[1:-1].strip()
        else:
            break
    return s


def _extract_updates_simple(expr: str, alias: str) -> list:
    """Extract (condition, addr, val) tuples from conditional update expressions.

    Handles the specific pattern emitted by Kami extraction:
    (guard ? alias : ((cond1 ? update(alias, a1, v1) : ((cond2 ? update(alias, a2, v2) : alias)))))
    """
    results = []

    # Find all `update (alias, addr, val)` in the expression
    update_prefix = f'update ({alias},'
    pos = 0
    while True:
        idx = expr.find(update_prefix, pos)
        if idx == -1:
            break

        # Find the opening paren of update(
        paren_start = expr.index('(', idx)
        paren_end = _find_matching_paren(expr, paren_start)
        if paren_end == -1:
            pos = idx + 1
            continue

        # Extract args
        args_str = expr[paren_start + 1:paren_end]
        parts = _split_at_depth0(args_str, ',')
        if len(parts) != 3:
            pos = idx + 1
            continue

        addr = parts[1].strip()
        val = parts[2].strip()

        # Find the condition: look backwards for the nearest `? (`
        # The pattern is: cond ? (update(...)) : (...)
        cond = _find_condition_backward(expr, idx)
        if cond:
            results.append((cond, addr, val))

        pos = paren_end + 1

    return results


def _find_condition_backward(expr: str, update_pos: int) -> str:
    """Find the ternary condition before an update() call.

    Look backward from update_pos for the `cond ? (update...` pattern.
    """
    before = expr[:update_pos]

    # Find the last `? (` before the update, skipping whitespace
    # The `(` right before "update" is what we matched through
    last_q = before.rfind('?')
    if last_q == -1:
        return None

    # Everything between the previous `:` or paren group and `?` is the condition
    # Walk backward from `?` to find where the condition starts
    # Look for `:` or `(` at depth 0
    cond_end = last_q
    depth = 0
    cond_start = 0
    for i in range(last_q - 1, -1, -1):
        c = before[i]
        if c == ')':
            depth += 1
        elif c == '(':
            depth -= 1
            if depth < 0:
                cond_start = i + 1
                break
        elif c == ':' and depth == 0:
            cond_start = i + 1
            break

    cond = before[cond_start:cond_end].strip()
    cond = _strip_balanced_parens(cond)
    return cond


def _find_matching_paren(s: str, start: int) -> int:
    """Find the matching close paren for the open paren at position start."""
    depth = 0
    for i in range(start, len(s)):
        if s[i] == '(':
            depth += 1
        elif s[i] == ')':
            depth -= 1
            if depth == 0:
                return i
    return -1


def _split_at_depth0(s: str, delim: str) -> list:
    """Split string by delimiter at paren depth 0."""
    parts = []
    depth = 0
    current = []
    for c in s:
        if c == '(':
            depth += 1
        elif c == ')':
            depth -= 1
        if c == delim and depth == 0:
            parts.append(''.join(current))
            current = []
        else:
            current.append(c)
    parts.append(''.join(current))
    return parts


if __name__ == '__main__':
    if len(sys.argv) < 2:
        print("Usage: bsv_regfile_transform.py <input.bsv> [output.bsv]", file=sys.stderr)
        sys.exit(1)

    infile = sys.argv[1]
    outfile = sys.argv[2] if len(sys.argv) > 2 else infile

    with open(infile) as f:
        bsv = f.read()

    result = transform_bsv(bsv)

    with open(outfile, 'w') as f:
        f.write(result)

    print(f"Transformed {infile} -> {outfile}", file=sys.stderr)
