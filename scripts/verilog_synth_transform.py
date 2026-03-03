#!/usr/bin/env python3
"""Transform BSC-generated Verilog into synthesizable Verilog.

The Kami→BSC→Verilog pipeline (kami_extract.sh) produces simulation-correct RTL
where arrays are flattened into individual scalar registers or wide bit-vectors.
This script transforms that output into synthesis-friendly Verilog while
preserving ALL logic exactly.

Transformations:
  1. reg [8191:0] imem         → reg [31:0] imem_arr [0:255]
  2. reg [511:0] mu_tensor     → reg [31:0] mt_arr [0:15]
  3. reg [31:0] mem0..mem255   → reg [31:0] dm [0:255]
  4. reg [31:0] reg0..reg31    → reg [31:0] rf [0:31]
  5. reg [31:0] pt0..pt15      → reg [31:0] pt [0:15]
  6. All read/write references updated accordingly
  7. imem$D_IN concatenation replaced with indexed write
  8. Sequential block updated for array syntax
  9. Reset block updated for array initialization

The proof chain is: Coq → OCaml → BSV → BSC → Verilog → THIS SCRIPT → Synth Verilog
All logic is preserved; only storage representation changes.

Usage:
    python3 scripts/verilog_synth_transform.py [input.v] [output.v]
    python3 scripts/verilog_synth_transform.py  # uses default paths
"""

import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
DEFAULT_IN = REPO / "thielecpu" / "hardware" / "rtl" / "thiele_cpu_kami.v"
DEFAULT_OUT = REPO / "thielecpu" / "hardware" / "rtl" / "thiele_cpu_kami_synth_generated.v"


# ---------------------------------------------------------------------------
# Pass 1: Replace flat imem [8191:0] with imem_arr [0:255]
# ---------------------------------------------------------------------------

def transform_imem(text: str) -> str:
    """Replace the flat 8192-bit imem register with a 256-entry array."""

    # 1a. Declaration: reg [8191:0] imem; → reg [31:0] imem_arr [0:255];
    text = re.sub(
        r'reg\s+\[8191\s*:\s*0\]\s+imem\s*;',
        '(* ram_style = "block" *) reg [31:0] imem_arr [0:255];  // was: reg [8191:0] imem',
        text
    )

    # 1b. Wire declarations: remove D_IN (replaced by indexed write),
    #     keep EN but rename to imem_EN for clarity
    text = re.sub(
        r'wire\s+\[8191\s*:\s*0\]\s+imem\$D_IN\s*;',
        '// imem$D_IN removed (indexed write replaces concatenation)',
        text
    )
    text = re.sub(
        r'wire\s+imem\$EN\s*;',
        'wire imem_EN;  // was: imem$EN',
        text
    )
    # Rename all imem$EN references to imem_EN
    text = text.replace('imem$EN', 'imem_EN')

    # 1c. Replace imem bit-slices imem[H:L] where H-L+1 == 32 and L%32 == 0
    #     Pattern: imem[N*32+31 : N*32] → imem_arr[N]
    def imem_slice_repl(m):
        hi = int(m.group(1))
        lo = int(m.group(2))
        if (hi - lo + 1) == 32 and lo % 32 == 0:
            idx = lo // 32
            return f'imem_arr[{idx}]'
        # Non-standard slice, leave as-is (shouldn't happen)
        return m.group(0)

    text = re.sub(r'imem\[(\d+)\s*:\s*(\d+)\]', imem_slice_repl, text)

    # 1d. Remove the 769-line assign imem$D_IN = { ... };
    #     Pattern: starts with "assign imem$D_IN =" and ends with matching ";"
    #     at top indent level. This is a single continuous assign.
    text = _remove_assign_block(text, 'imem$D_IN')

    # 1e. Remove the sequential update: if (imem$EN/imem_EN) imem <= ...
    text = re.sub(
        r'if\s*\(imem_EN\)\s+imem\s*<=\s*`BSV_ASSIGNMENT_DELAY\s+imem\$D_IN\s*;',
        '// imem update moved to loadInstr indexed write (see below)',
        text
    )
    # Also catch the un-renamed variant
    text = re.sub(
        r'if\s*\(imem\$EN\)\s+imem\s*<=\s*`BSV_ASSIGNMENT_DELAY\s+imem\$D_IN\s*;',
        '// imem update moved to loadInstr indexed write (see below)',
        text
    )

    # 1f. Fix sensitivity lists: always@(pc or imem) → always@(*)
    text = re.sub(
        r'always@\(pc\s+or\s+imem\)',
        'always@(*)',
        text
    )

    # 1g. Fix reset: imem <= 8192'd0 → loop over imem_arr
    text = re.sub(
        r'imem\s*<=\s*`BSV_ASSIGNMENT_DELAY\s+8192\'d0\s*;',
        'begin : rst_imem_arr\n'
        '\t  integer _j;\n'
        '\t  for (_j = 0; _j < 256; _j = _j + 1)\n'
        '\t    imem_arr[_j] <= `BSV_ASSIGNMENT_DELAY 32\'d0;\n'
        '\tend',
        text
    )

    # 1f. Replace the 256-case always block for imem fetch
    #     The BSC generates: always@(pc or imem) begin case(pc[7:0]) ... endcase end
    #     where each case maps pc to imem[H:L]. After 1c above, these become
    #     imem_arr[N] references. We can replace the whole block with a wire.
    #     But it's safer to let the renamed references stand — Yosys optimizes them.

    return text


def _remove_assign_block(text: str, wire_name: str) -> str:
    """Remove a multi-line assign statement for a specific wire."""
    pattern = re.compile(
        r'^\s*assign\s+' + re.escape(wire_name) + r'\s*=',
        re.MULTILINE
    )
    m = pattern.search(text)
    if not m:
        return text

    start = m.start()
    # Find the matching semicolon. Count braces to handle nested {}.
    depth = 0
    i = m.end()
    while i < len(text):
        ch = text[i]
        if ch == '{':
            depth += 1
        elif ch == '}':
            depth -= 1
        elif ch == ';' and depth <= 0:
            end = i + 1
            # Replace with a comment
            replacement = f'  // assign {wire_name} removed by synth transform (indexed write used instead)\n'
            text = text[:start] + replacement + text[end:]
            return text
        i += 1
    return text


# ---------------------------------------------------------------------------
# Pass 2: Replace flat mu_tensor [511:0] with mt_arr [0:15]
# ---------------------------------------------------------------------------

def transform_mu_tensor(text: str) -> str:
    """Replace the flat 512-bit mu_tensor register with a 16-entry array."""

    # 2a. Declaration
    text = re.sub(
        r'reg\s+\[511\s*:\s*0\]\s+mu_tensor\s*;',
        'reg [31:0] mt_arr [0:15];  // was: reg [511:0] mu_tensor',
        text
    )

    # 2b. Wire declarations: rename mu_tensor$D_IN to mu_tensor_D_IN_flat
    text = re.sub(
        r'wire\s+\[511\s*:\s*0\]\s+mu_tensor\$D_IN\s*;',
        'wire [511:0] mu_tensor_D_IN_flat;  // kept for compatibility',
        text
    )

    # Also rename the assign target and all references to mu_tensor$D_IN
    text = text.replace('mu_tensor$D_IN', 'mu_tensor_D_IN_flat')

    # 2c. Replace mu_tensor bit-slices mu_tensor[H:L] where H-L+1 == 32
    def mt_slice_repl(m):
        hi = int(m.group(1))
        lo = int(m.group(2))
        if (hi - lo + 1) == 32 and lo % 32 == 0:
            idx = lo // 32
            return f'mt_arr[{idx}]'
        return m.group(0)

    text = re.sub(r'mu_tensor\[(\d+)\s*:\s*(\d+)\]', mt_slice_repl, text)

    # 2d. Rename mu_tensor$EN wire
    text = re.sub(
        r'wire\s+mu_tensor\$EN\s*;',
        'wire mu_tensor_EN;  // was: mu_tensor$EN',
        text
    )
    text = text.replace('mu_tensor$EN', 'mu_tensor_EN')

    # 2e. Replace standalone mu_tensor (the 512-bit register value) in expressions
    #     with mt_arr_flat (the reconstruction wire). Must not match:
    #     mu_tensor_D_IN_flat, mu_tensor_EN, mu_tensor_BITS, mt_arr, mt_arr_flat
    #     Pattern: mu_tensor preceded/followed by non-identifier chars,
    #     not already part of a longer name.
    text = re.sub(
        r'(?<![a-zA-Z_])mu_tensor(?!_[A-Za-z])',
        'mt_arr_flat',
        text
    )

    # 2f. Fix reset: mu_tensor <= 512'd0 → loop over mt_arr
    text = re.sub(
        r'mt_arr_flat\s*<=\s*`BSV_ASSIGNMENT_DELAY\s+512\'d0\s*;',
        'begin : rst_mt_arr\n'
        '\t  integer _j;\n'
        '\t  for (_j = 0; _j < 16; _j = _j + 1)\n'
        '\t    mt_arr[_j] <= `BSV_ASSIGNMENT_DELAY 32\'d0;\n'
        '\tend',
        text
    )

    # 2g. Fix sensitivity lists that reference mu_tensor (now mt_arr_flat)
    #     Replace entire always@(...mt_arr_flat...) with always@(*)
    text = re.sub(
        r'always@\([^)]*mt_arr_flat[^)]*\)',
        'always@(*)',
        text
    )

    return text


# ---------------------------------------------------------------------------
# Pass 3: Replace individual mem0..mem255 with dm[0..255]
# ---------------------------------------------------------------------------

def transform_data_mem(text: str) -> str:
    """Replace 256 individual data memory registers with an array."""

    # 3a. Remove individual register declarations
    #     Pattern: reg [31:0] memN;
    text = re.sub(
        r'^\s*//\s*register\s+mem(\d+)\s*\n\s*reg\s+\[31\s*:\s*0\]\s+mem\d+\s*;',
        '',
        text,
        flags=re.MULTILINE
    )

    # 3b. Replace register references: mem(\d+) but NOT mem(\d+)$D_IN/EN
    text = re.sub(
        r'(?<![a-zA-Z_$])mem(\d+)(?!\$)(?![a-zA-Z_\d])',
        lambda m: f'dm[{m.group(1)}]',
        text
    )

    return text


# ---------------------------------------------------------------------------
# Pass 4: Replace individual reg0..reg31 with rf[0..31]
# ---------------------------------------------------------------------------

def transform_regfile(text: str) -> str:
    """Replace 32 individual register file entries with an array."""

    # 4a. Remove individual register declarations
    text = re.sub(
        r'^\s*//\s*register\s+reg(\d+)\s*\n\s*reg\s+\[31\s*:\s*0\]\s+reg\d+\s*;',
        '',
        text,
        flags=re.MULTILINE
    )

    # 4b. Replace register references: reg(\d+) but NOT reg(\d+)$
    text = re.sub(
        r'(?<![a-zA-Z_$])reg(\d+)(?!\$)(?![a-zA-Z_\d])',
        lambda m: f'rf[{m.group(1)}]',
        text
    )

    return text


# ---------------------------------------------------------------------------
# Pass 5: Replace individual pt0..pt15 with pt_tbl[0..15]
# ---------------------------------------------------------------------------

def transform_partition_table(text: str) -> str:
    """Replace 16 individual partition table registers with an array."""

    # 5a. Remove individual register declarations
    text = re.sub(
        r'^\s*//\s*register\s+pt(\d+)\s*\n\s*reg\s+\[31\s*:\s*0\]\s+pt\d+\s*;',
        '',
        text,
        flags=re.MULTILINE
    )

    # 5b. Replace register references
    text = re.sub(
        r'(?<![a-zA-Z_$])pt(\d+)(?!\$)(?![a-zA-Z_\d])',
        lambda m: f'pt_tbl[{m.group(1)}]',
        text
    )

    return text


# ---------------------------------------------------------------------------
# Pass 5b: Insert array declarations in one place
# ---------------------------------------------------------------------------

def insert_array_declarations(text: str) -> str:
    """Insert dm, rf, pt_tbl array declarations after imem_arr declaration.

    This runs AFTER all renames, so anchors use the already-transformed text.
    """
    anchor = 'imem_arr [0:255];  // was: reg [8191:0] imem'
    if anchor in text:
        additions = (
            '\n'
            '  (* ram_style = "block" *) reg [31:0] dm [0:255];      // was: mem0..mem255\n'
            '  reg [31:0] rf [0:31];       // was: reg0..reg31\n'
            '  reg [31:0] pt_tbl [0:15];   // was: pt0..pt15'
        )
        text = text.replace(anchor, anchor + additions)
    return text


# ---------------------------------------------------------------------------
# Pass 6: Remove individual D_IN/EN wire declarations for arrays
# ---------------------------------------------------------------------------

def remove_array_wire_decls(text: str) -> str:
    """Keep D_IN/EN wire declarations — they are still used by assigns.

    Previously this removed them, causing 'implicitly declared' warnings.
    The wire names (mem0$D_IN, reg0$D_IN, etc.) stay as-is since the
    assigns that compute them and the sequential block that consumes them
    still reference the original BSC wire names.
    """
    # Intentionally a no-op now. Wire declarations are valid and needed.
    return text


# ---------------------------------------------------------------------------
# Pass 7: Fix the reset block — replace individual register inits with loops
# ---------------------------------------------------------------------------

def transform_reset_block(text: str) -> str:
    """Replace individual register reset assignments with array loops."""

    # The BSC reset block has patterns like:
    #   mem0 <= `BSV_ASSIGNMENT_DELAY 32'd0;
    #   mem1 <= `BSV_ASSIGNMENT_DELAY 32'd0;
    #   ... (256 times)
    # After pass 3, these became dm[0] <= ...; dm[1] <= ...; etc.
    # We want to replace them with a for loop.

    # Find consecutive dm[N] reset assignments and replace with loop
    # Pattern: multiple lines of "dm[N] <= `BSV_ASSIGNMENT_DELAY 32'd0;"
    dm_reset_pattern = re.compile(
        r'((?:\s*dm\[\d+\]\s*<=\s*`BSV_ASSIGNMENT_DELAY\s+32\'d0\s*;\s*\n){10,})',
        re.MULTILINE
    )
    text = dm_reset_pattern.sub(
        '\tbegin : rst_dm\n'
        '\t  integer _i;\n'
        '\t  for (_i = 0; _i < 256; _i = _i + 1)\n'
        '\t    dm[_i] <= `BSV_ASSIGNMENT_DELAY 32\'d0;\n'
        '\tend\n',
        text
    )

    # Same for rf[N]
    rf_reset_pattern = re.compile(
        r'((?:\s*rf\[\d+\]\s*<=\s*`BSV_ASSIGNMENT_DELAY\s+32\'d0\s*;\s*\n){10,})',
        re.MULTILINE
    )
    text = rf_reset_pattern.sub(
        '\tbegin : rst_rf\n'
        '\t  integer _i;\n'
        '\t  for (_i = 0; _i < 32; _i = _i + 1)\n'
        '\t    rf[_i] <= `BSV_ASSIGNMENT_DELAY 32\'d0;\n'
        '\tend\n',
        text
    )

    # Same for pt_tbl[N]
    pt_reset_pattern = re.compile(
        r'((?:\s*pt_tbl\[\d+\]\s*<=\s*`BSV_ASSIGNMENT_DELAY\s+32\'d0\s*;\s*\n){10,})',
        re.MULTILINE
    )
    text = pt_reset_pattern.sub(
        '\tbegin : rst_pt\n'
        '\t  integer _i;\n'
        '\t  for (_i = 0; _i < 16; _i = _i + 1)\n'
        '\t    pt_tbl[_i] <= `BSV_ASSIGNMENT_DELAY 32\'d0;\n'
        '\tend\n',
        text
    )

    return text


# ---------------------------------------------------------------------------
# Pass 8: Fix the initial block — replace individual inits with loops
# ---------------------------------------------------------------------------

def transform_initial_block(text: str) -> str:
    """Replace individual register initializations with array loops."""

    # Replace consecutive dm[N] = hex_literal; with loop
    dm_init_pattern = re.compile(
        r'((?:\s*dm\[\d+\]\s*=\s*32\'h[0-9a-fA-F]+\s*;\s*\n){10,})',
        re.MULTILINE
    )
    text = dm_init_pattern.sub(
        '\tbegin : init_dm\n'
        '\t  integer _i;\n'
        '\t  for (_i = 0; _i < 256; _i = _i + 1)\n'
        '\t    dm[_i] = 32\'hAAAAAAAA;\n'
        '\tend\n',
        text
    )

    # Same for rf[N]
    rf_init_pattern = re.compile(
        r'((?:\s*rf\[\d+\]\s*=\s*32\'h[0-9a-fA-F]+\s*;\s*\n){10,})',
        re.MULTILINE
    )
    text = rf_init_pattern.sub(
        '\tbegin : init_rf\n'
        '\t  integer _i;\n'
        '\t  for (_i = 0; _i < 32; _i = _i + 1)\n'
        '\t    rf[_i] = 32\'hAAAAAAAA;\n'
        '\tend\n',
        text
    )

    # Same for pt_tbl[N]
    pt_init_pattern = re.compile(
        r'((?:\s*pt_tbl\[\d+\]\s*=\s*32\'h[0-9a-fA-F]+\s*;\s*\n){10,})',
        re.MULTILINE
    )
    text = pt_init_pattern.sub(
        '\tbegin : init_pt\n'
        '\t  integer _i;\n'
        '\t  for (_i = 0; _i < 16; _i = _i + 1)\n'
        '\t    pt_tbl[_i] = 32\'hAAAAAAAA;\n'
        '\tend\n',
        text
    )

    # imem: replace the massive 8192-bit hex literal initialization
    # Pattern: imem = 8192'hAAAA...;
    text = re.sub(
        r'imem\s*=\s*8192\'h[0-9a-fA-F]+\s*;',
        'begin : init_imem\n'
        '\t  integer _i;\n'
        '\t  for (_i = 0; _i < 256; _i = _i + 1)\n'
        '\t    imem_arr[_i] = 32\'hAAAAAAAA;\n'
        '\tend',
        text
    )

    # mu_tensor: replace 512-bit hex literal (already renamed to mt_arr_flat)
    text = re.sub(
        r'mt_arr_flat\s*=\s*512\'h[0-9a-fA-F]+\s*;',
        'begin : init_mt\n'
        '\t  integer _i;\n'
        '\t  for (_i = 0; _i < 16; _i = _i + 1)\n'
        '\t    mt_arr[_i] = 32\'hAAAAAAAA;\n'
        '\tend',
        text
    )

    return text


# ---------------------------------------------------------------------------
# Pass 9: Add indexed imem write in sequential block
# ---------------------------------------------------------------------------

def add_imem_indexed_write(text: str) -> str:
    """Add an indexed write for imem_arr in the sequential always block.

    The BSC original had: if (imem$EN) imem <= imem$D_IN;
    which was a write to the entire 8192-bit register.
    We replace with: if (EN_loadInstr) imem_arr[loadInstr_x_0[39:32]] <= loadInstr_x_0[31:0];
    """
    # Find where the imem update comment was placed and add the indexed write
    text = text.replace(
        '// imem update moved to loadInstr indexed write (see below)',
        'if (EN_loadInstr)\n'
        '\t  imem_arr[loadInstr_x_0[39:32]] <= `BSV_ASSIGNMENT_DELAY loadInstr_x_0[31:0];'
    )
    return text


# ---------------------------------------------------------------------------
# Pass 10: Handle mu_tensor sequential updates
# ---------------------------------------------------------------------------

def transform_mu_tensor_seq(text: str) -> str:
    """Fix mu_tensor sequential updates to use array syntax.

    By this point, mu_tensor has been renamed to mt_arr_flat and
    mu_tensor$EN to mu_tensor_EN. Replace the flat write with per-element writes.
    """
    # Match the already-renamed pattern
    text = re.sub(
        r'if\s*\(mu_tensor_EN\)\s+mt_arr_flat\s*<=\s*`BSV_ASSIGNMENT_DELAY\s+mu_tensor_D_IN_flat\s*;',
        'if (mu_tensor_EN) begin\n'
        '\t    mt_arr[0]  <= `BSV_ASSIGNMENT_DELAY mu_tensor_D_IN_flat[31:0];\n'
        '\t    mt_arr[1]  <= `BSV_ASSIGNMENT_DELAY mu_tensor_D_IN_flat[63:32];\n'
        '\t    mt_arr[2]  <= `BSV_ASSIGNMENT_DELAY mu_tensor_D_IN_flat[95:64];\n'
        '\t    mt_arr[3]  <= `BSV_ASSIGNMENT_DELAY mu_tensor_D_IN_flat[127:96];\n'
        '\t    mt_arr[4]  <= `BSV_ASSIGNMENT_DELAY mu_tensor_D_IN_flat[159:128];\n'
        '\t    mt_arr[5]  <= `BSV_ASSIGNMENT_DELAY mu_tensor_D_IN_flat[191:160];\n'
        '\t    mt_arr[6]  <= `BSV_ASSIGNMENT_DELAY mu_tensor_D_IN_flat[223:192];\n'
        '\t    mt_arr[7]  <= `BSV_ASSIGNMENT_DELAY mu_tensor_D_IN_flat[255:224];\n'
        '\t    mt_arr[8]  <= `BSV_ASSIGNMENT_DELAY mu_tensor_D_IN_flat[287:256];\n'
        '\t    mt_arr[9]  <= `BSV_ASSIGNMENT_DELAY mu_tensor_D_IN_flat[319:288];\n'
        '\t    mt_arr[10] <= `BSV_ASSIGNMENT_DELAY mu_tensor_D_IN_flat[351:320];\n'
        '\t    mt_arr[11] <= `BSV_ASSIGNMENT_DELAY mu_tensor_D_IN_flat[383:352];\n'
        '\t    mt_arr[12] <= `BSV_ASSIGNMENT_DELAY mu_tensor_D_IN_flat[415:384];\n'
        '\t    mt_arr[13] <= `BSV_ASSIGNMENT_DELAY mu_tensor_D_IN_flat[447:416];\n'
        '\t    mt_arr[14] <= `BSV_ASSIGNMENT_DELAY mu_tensor_D_IN_flat[479:448];\n'
        '\t    mt_arr[15] <= `BSV_ASSIGNMENT_DELAY mu_tensor_D_IN_flat[511:480];\n'
        '\t  end',
        text
    )
    return text


# ---------------------------------------------------------------------------
# Pass 11: Fix standalone mu_tensor references (not bit-sliced)
# ---------------------------------------------------------------------------

def fix_standalone_mu_tensor(text: str) -> str:
    """Add mt_arr_flat reconstruction wire.

    After the mu_tensor → mt_arr_flat rename, the D_IN computation references
    mt_arr_flat as a 512-bit value. We need a wire that reconstructs this
    from the 16-element array.
    """
    if 'mt_arr_flat' in text and 'wire [511:0] mt_arr_flat' not in text:
        # Find the mt_arr declaration and add the reconstruction wire after it
        text = re.sub(
            r'(reg \[31:0\] mt_arr \[0:15\];[^\n]*\n)',
            r'\1'
            '  wire [511:0] mt_arr_flat = {\n'
            '    mt_arr[15], mt_arr[14], mt_arr[13], mt_arr[12],\n'
            '    mt_arr[11], mt_arr[10], mt_arr[9],  mt_arr[8],\n'
            '    mt_arr[7],  mt_arr[6],  mt_arr[5],  mt_arr[4],\n'
            '    mt_arr[3],  mt_arr[2],  mt_arr[1],  mt_arr[0]\n'
            '  };\n',
            text,
            count=1
        )

    return text


# ---------------------------------------------------------------------------
# Pass 12: Add header comment
# ---------------------------------------------------------------------------

def add_header(text: str) -> str:
    header = """\
// ============================================================================
// Thiele CPU — Synthesis-Transformed Verilog
// ============================================================================
// Generated by: scripts/verilog_synth_transform.py
// Source: BSC output from Kami-proven specification (thiele_cpu_kami.v)
//
// This file preserves ALL logic from the BSC-generated simulation model.
// Only storage representations are changed for FPGA synthesis:
//   - imem: reg [8191:0] → reg [31:0] imem_arr [0:255]
//   - mu_tensor: reg [511:0] → reg [31:0] mt_arr [0:15]
//   - data memory: mem0..mem255 → reg [31:0] dm [0:255]
//   - register file: reg0..reg31 → reg [31:0] rf [0:31]
//   - partition table: pt0..pt15 → reg [31:0] pt_tbl [0:15]
//
// Proof chain: Coq → OCaml → Bluespec → BSC → verilog_synth_transform.py
// ============================================================================

"""
    return header + text


# ---------------------------------------------------------------------------
# Main pipeline
# ---------------------------------------------------------------------------

def transform(text: str) -> str:
    """Apply all transformation passes in order."""
    original_lines = text.count('\n')

    text = transform_imem(text)          # Pass 1: imem flat → array
    text = transform_mu_tensor(text)      # Pass 2: mu_tensor flat → array
    text = transform_data_mem(text)       # Pass 3: mem0-255 → dm[0-255]
    text = transform_regfile(text)        # Pass 4: reg0-31 → rf[0-31]
    text = transform_partition_table(text) # Pass 5: pt0-15 → pt_tbl[0-15]
    text = insert_array_declarations(text) # Pass 5b: insert array decl block
    text = remove_array_wire_decls(text)   # Pass 6: remove individual wire decls
    text = transform_reset_block(text)     # Pass 7: reset loops
    text = transform_initial_block(text)   # Pass 8: initial loops
    text = add_imem_indexed_write(text)    # Pass 9: imem indexed write
    text = transform_mu_tensor_seq(text)   # Pass 10: mu_tensor seq update
    text = fix_standalone_mu_tensor(text)  # Pass 11: mt_arr_flat reconstruction
    text = add_header(text)                # Pass 12: header comment

    final_lines = text.count('\n')
    print(f"  Lines: {original_lines} → {final_lines} ({original_lines - final_lines} removed)")

    return text


def main():
    if len(sys.argv) >= 3:
        in_path = Path(sys.argv[1])
        out_path = Path(sys.argv[2])
    elif len(sys.argv) == 2:
        in_path = Path(sys.argv[1])
        out_path = DEFAULT_OUT
    else:
        in_path = DEFAULT_IN
        out_path = DEFAULT_OUT

    if not in_path.exists():
        print(f"ERROR: Input file not found: {in_path}", file=sys.stderr)
        sys.exit(1)

    print(f"Reading: {in_path}")
    text = in_path.read_text()

    print("Transforming...")
    result = transform(text)

    print(f"Writing: {out_path}")
    out_path.write_text(result)
    print("Done.")


if __name__ == '__main__':
    main()
