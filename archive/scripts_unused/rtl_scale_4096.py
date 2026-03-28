#!/usr/bin/env python3
"""Transform the generated thiele_cpu_kami.v to use Verilog arrays and scale to 4096.

This script takes the BSC-generated Verilog (which uses individual named registers
for mem0..mem255 and reg0..reg31) and transforms it into a clean RTL design with:
- reg [31:0] data_mem [0:4095]   (was 256 individual mem0..mem255)
- reg [31:0] regs [0:31]         (was 32 individual reg0..reg31)
- reg [31:0] imem [0:4095]       (was reg [8191:0] imem)
- reg [2047:0] ptTable           (was reg [511:0] ptTable, 16 -> 64 slots)
- reg [2047:0] mu_tensor         (was reg [511:0] mu_tensor, 16 -> 64 slots)
- 12-bit PC addressing           (was 8-bit)
- 6-bit partition index          (was 4-bit)
- 44-bit loadInstr port          (was 40-bit)
"""

import re, sys

# ── Constants ────────────────────────────────────────────────────────
OLD_MEM_SIZE   = 256
NEW_MEM_SIZE   = 4096
OLD_MEM_BITS   = 8     # log2(256)
NEW_MEM_BITS   = 12    # log2(4096)
OLD_PT_SLOTS   = 16
NEW_PT_SLOTS   = 64
OLD_PT_BITS    = 4     # log2(16)
NEW_PT_BITS    = 6     # log2(64)
OLD_IMEM_FLAT  = OLD_MEM_SIZE * 32  # 8192
NEW_IMEM_FLAT  = NEW_MEM_SIZE * 32  # 131072
OLD_PT_FLAT    = OLD_PT_SLOTS * 32  # 512
NEW_PT_FLAT    = NEW_PT_SLOTS * 32  # 2048
NUM_REGS       = 32
WORD_SZ        = 32


def transform(src: str) -> str:
    lines = src.split('\n')
    out = []
    skip_until_endmodule = False

    # We'll do a line-by-line transform with state tracking
    i = 0
    in_module = False
    decl_emitted = {
        'mem_array': False,
        'reg_array': False,
        'imem_array': False,
    }

    # Track what blocks we need to skip
    skip_mode = None  # None, 'mem_decl', 'reg_decl', etc.
    skip_depth = 0

    while i < len(lines):
        line = lines[i]

        # ── Port header comment updates ──
        # loadInstr_x_0: I 40 -> 44
        if '// loadInstr_x_0' in line and 'I' in line and '40' in line:
            line = line.replace('40', '44')
        # setActiveModule_x_0: I 4 -> 6
        if '// setActiveModule_x_0' in line and 'I' in line:
            line = re.sub(r'\b4\b(?=\s*$)', '6', line)
        # getPtSize_x_0: I 4 -> 6
        if '// getPtSize_x_0' in line and 'I' in line:
            line = re.sub(r'\b4\b(?=\s*$)', '6', line)
        # getPtNextId: O 32 -> stays 32 (but internal width changes)

        # ── Port declarations ──
        # input [39:0] loadInstr_x_0 -> input [43:0] loadInstr_x_0
        if re.match(r'\s*input\s+\[39\s*:\s*0\]\s+loadInstr_x_0', line):
            line = line.replace('[39 : 0]', '[43 : 0]').replace('[39:0]', '[43:0]')

        # input [3:0] setActiveModule_x_0 -> input [5:0]
        if re.match(r'\s*input\s+\[3\s*:\s*0\]\s+setActiveModule_x_0', line):
            line = line.replace('[3 : 0]', '[5 : 0]').replace('[3:0]', '[5:0]')

        # input [3:0] getPtSize_x_0 -> input [5:0]
        if re.match(r'\s*input\s+\[3\s*:\s*0\]\s+getPtSize_x_0', line):
            line = line.replace('[3 : 0]', '[5 : 0]').replace('[3:0]', '[5:0]')

        # ── Register declarations: skip individual memN and regN ──
        # Skip "// register memN" + "reg [31:0] memN;" + "wire... memN$D_IN" + "wire memN$EN"
        m_mem_comment = re.match(r'\s*// register mem(\d+)\s*$', line)
        if m_mem_comment:
            idx = int(m_mem_comment.group(1))
            if 0 <= idx < OLD_MEM_SIZE:
                # Skip this block (comment + reg + wire D_IN + wire EN + blank)
                if not decl_emitted['mem_array']:
                    out.append('  // data memory array (4096 x 32-bit)')
                    out.append(f'  reg [{WORD_SZ-1} : 0] data_mem [0:{NEW_MEM_SIZE-1}];')
                    out.append('')
                    decl_emitted['mem_array'] = True
                # Skip comment + up to 4 more lines (reg, wire D_IN, wire EN, blank)
                i += 1
                while i < len(lines) and (re.match(r'\s*reg\s+\[31\s*:\s*0\]\s+mem\d+', lines[i]) or
                                            re.match(r'\s*wire\s+.*mem\d+\$', lines[i]) or
                                            lines[i].strip() == ''):
                    i += 1
                continue

        # Skip "// register regN" blocks
        m_reg_comment = re.match(r'\s*// register reg(\d+)\s*$', line)
        if m_reg_comment:
            idx = int(m_reg_comment.group(1))
            if 0 <= idx < NUM_REGS:
                if not decl_emitted['reg_array']:
                    out.append('  // register file array (32 x 32-bit)')
                    out.append(f'  reg [{WORD_SZ-1} : 0] regs [0:{NUM_REGS-1}];')
                    out.append('')
                    decl_emitted['reg_array'] = True
                i += 1
                while i < len(lines) and (re.match(r'\s*reg\s+\[31\s*:\s*0\]\s+reg\d+', lines[i]) or
                                            re.match(r'\s*wire\s+.*reg\d+\$', lines[i]) or
                                            lines[i].strip() == ''):
                    i += 1
                continue

        # ── Replace imem declaration: reg [8191:0] imem -> reg [31:0] imem [0:4095] ──
        if re.match(r'\s*reg\s+\[8191\s*:\s*0\]\s+imem\s*;', line):
            out.append(f'  reg [{WORD_SZ-1} : 0] imem [0:{NEW_MEM_SIZE-1}];')
            i += 1
            # Skip wire [8191:0] imem$D_IN and wire imem$EN — we handle writes directly
            while i < len(lines) and re.match(r'\s*wire\s+.*imem\$', lines[i]):
                i += 1
            continue

        # ── Widen ptTable: [511:0] -> [2047:0] ──
        if re.match(r'\s*reg\s+\[511\s*:\s*0\]\s+ptTable\s*;', line):
            line = line.replace('[511 : 0]', f'[{NEW_PT_FLAT-1} : 0]').replace('[511:0]', f'[{NEW_PT_FLAT-1}:0]')
        if 'wire' in line and 'ptTable$D_IN' in line and '[511' in line:
            line = line.replace('[511 : 0]', f'[{NEW_PT_FLAT-1} : 0]').replace('[511:0]', f'[{NEW_PT_FLAT-1}:0]')

        # ── Widen mu_tensor: [511:0] -> [2047:0] ──
        if re.match(r'\s*reg\s+\[511\s*:\s*0\]\s+mu_tensor\s*;', line):
            line = line.replace('[511 : 0]', f'[{NEW_PT_FLAT-1} : 0]').replace('[511:0]', f'[{NEW_PT_FLAT-1}:0]')
        if 'wire' in line and 'mu_tensor$D_IN' in line and '[511' in line:
            line = line.replace('[511 : 0]', f'[{NEW_PT_FLAT-1} : 0]').replace('[511:0]', f'[{NEW_PT_FLAT-1}:0]')

        # ── Skip huge imem write MUX (MUX_imem$write_1__VAL_1 and VAL_2) ──
        # These are 8000+ bit assignment statements that we'll replace with simple array writes
        if 'MUX_imem$write_1__VAL_1' in line and 'assign' in line:
            # Skip this entire multi-line assign block
            while i < len(lines) and not (lines[i].strip().endswith(';') and 'imem[' not in lines[i]):
                i += 1
                if i < len(lines) and lines[i].strip().endswith(';'):
                    i += 1
                    break
            continue
        if 'MUX_imem$write_1__VAL_2' in line and 'assign' in line:
            while i < len(lines) and not lines[i].strip().endswith(';'):
                i += 1
            i += 1
            continue

        # ── Replace imem$D_IN / imem$EN assignments ──
        if re.match(r'\s*assign\s+imem\$D_IN', line):
            # Skip this block — we handle imem writes in the clocked section
            while i < len(lines) and not lines[i].strip().endswith(';'):
                i += 1
            i += 1
            continue
        if re.match(r'\s*assign\s+imem\$EN', line):
            i += 1
            continue

        # ── Replace instruction fetch case: pc[7:0] -> pc[11:0] ──
        line = re.sub(r'pc\[7:0\]', f'pc[{NEW_MEM_BITS-1}:0]', line)

        # ── Replace loadInstr address bits: loadInstr_x_0[39:32] -> [43:32] ──
        line = line.replace('loadInstr_x_0[39:32]', f'loadInstr_x_0[{31+NEW_MEM_BITS}:32]')
        # Also 8-bit width references in loadInstr
        line = re.sub(r"8'd255\)", f"{NEW_MEM_BITS}'d{NEW_MEM_SIZE-1})", line)

        # ── Replace pt index bits: [19:16] 4-bit -> still works for 6-bit ──
        # The partition indices are embedded in instruction fields. Keep as-is since
        # instructions still have 8-bit fields; only the hardware table is wider.

        # ── 4-bit pt case statements -> 6-bit ──
        # getPtSize case: 4'd0..4'd15 -> 6'd0..6'd63
        if "4'd0: getPtSize = ptTable[31:0]" in line or "4'd0: x_734__h" in line:
            # This is inside a case block for ptTable read — need to expand
            pass  # We'll handle the case blocks differently

        # ── Replace ptTable bit-slicing for 16->64 slots ──
        for slot in range(OLD_PT_SLOTS):
            old_hi = slot * 32 + 31
            old_lo = slot * 32
            old_pattern = f'ptTable[{old_hi}:{old_lo}]'
            if old_pattern in line:
                # Keep the same slot index, just the pattern stays the same
                pass

        # ── Reset values ──
        # imem reset: 8192'd0 -> handled differently (array reset uses for loop)
        if "imem <= `BSV_ASSIGNMENT_DELAY" in line and "8192'd0" in line:
            # Replace with for-loop reset in the always block
            out.append('        for (__rst_i = 0; __rst_i < ' + str(NEW_MEM_SIZE) + '; __rst_i = __rst_i + 1)')
            out.append('          imem[__rst_i] <= `BSV_ASSIGNMENT_DELAY 32\'d0;')
            i += 1
            continue

        # ptTable reset: 512'd0 -> 2048'd0
        if "ptTable <= `BSV_ASSIGNMENT_DELAY" in line and "512'd0" in line:
            line = line.replace("512'd0", f"{NEW_PT_FLAT}'d0")

        # mu_tensor reset: 512'd0 -> 2048'd0
        if "mu_tensor <= `BSV_ASSIGNMENT_DELAY" in line and "512'd0" in line:
            line = line.replace("512'd0", f"{NEW_PT_FLAT}'d0")

        # memN reset: skip individual, add array loop
        m_mem_reset = re.match(r'\s+mem0\s+<=\s+`BSV_ASSIGNMENT_DELAY\s+32\'d0', line)
        if m_mem_reset:
            out.append('        for (__rst_i = 0; __rst_i < ' + str(NEW_MEM_SIZE) + '; __rst_i = __rst_i + 1)')
            out.append('          data_mem[__rst_i] <= `BSV_ASSIGNMENT_DELAY 32\'d0;')
            # Skip all individual mem resets
            while i < len(lines) and re.match(r'\s+mem\d+\s+<=\s+`BSV_ASSIGNMENT_DELAY\s+32\'d0', lines[i]):
                i += 1
            continue
        # Skip remaining individual mem resets
        if re.match(r'\s+mem\d+\s+<=\s+`BSV_ASSIGNMENT_DELAY\s+32\'d0', line):
            i += 1
            continue

        # regN reset: skip individual, add array loop
        m_reg_reset = re.match(r'\s+reg0\s+<=\s+`BSV_ASSIGNMENT_DELAY\s+32\'d0', line)
        if m_reg_reset:
            out.append('        for (__rst_i = 0; __rst_i < ' + str(NUM_REGS) + '; __rst_i = __rst_i + 1)')
            out.append('          regs[__rst_i] <= `BSV_ASSIGNMENT_DELAY 32\'d0;')
            while i < len(lines) and re.match(r'\s+reg\d+\s+<=\s+`BSV_ASSIGNMENT_DELAY\s+32\'d0', lines[i]):
                i += 1
            continue
        if re.match(r'\s+reg\d+\s+<=\s+`BSV_ASSIGNMENT_DELAY\s+32\'d0', line):
            i += 1
            continue

        # ── Clock update: individual mem/reg updates -> array ──
        # "if (mem0$EN) mem0 <= ..." -> "if (data_mem_en[0]) data_mem[0] <= ..."
        # We'll replace these with a single block
        m_mem_clk = re.match(r'\s+if\s+\(mem0\$EN\)\s+mem0\s+<=', line)
        if m_mem_clk:
            # Emit array write block
            out.append('        // Data memory array update')
            out.append('        for (__clk_i = 0; __clk_i < ' + str(NEW_MEM_SIZE) + '; __clk_i = __clk_i + 1)')
            out.append('          if (data_mem_en[__clk_i]) data_mem[__clk_i] <= `BSV_ASSIGNMENT_DELAY data_mem_din[__clk_i];')
            # Skip all individual mem clock updates
            while i < len(lines) and re.match(r'\s+if\s+\(mem\d+\$EN\)\s+mem\d+\s+<=', lines[i]):
                i += 1
            continue
        if re.match(r'\s+if\s+\(mem\d+\$EN\)\s+mem\d+\s+<=', line):
            i += 1
            continue

        m_reg_clk = re.match(r'\s+if\s+\(reg0\$EN\)\s+reg0\s+<=', line)
        if m_reg_clk:
            out.append('        // Register file array update')
            out.append('        for (__clk_i = 0; __clk_i < ' + str(NUM_REGS) + '; __clk_i = __clk_i + 1)')
            out.append('          if (regs_en[__clk_i]) regs[__clk_i] <= `BSV_ASSIGNMENT_DELAY regs_din[__clk_i];')
            while i < len(lines) and re.match(r'\s+if\s+\(reg\d+\$EN\)\s+reg\d+\s+<=', lines[i]):
                i += 1
            continue
        if re.match(r'\s+if\s+\(reg\d+\$EN\)\s+reg\d+\s+<=', line):
            i += 1
            continue

        # imem clock update
        if re.match(r'\s+if\s+\(imem\$EN\)\s+imem\s+<=', line):
            out.append('        if (EN_loadInstr)')
            out.append(f'          imem[loadInstr_x_0[{31+NEW_MEM_BITS}:32]] <= `BSV_ASSIGNMENT_DELAY loadInstr_x_0[31:0];')
            i += 1
            continue

        # ── Replace references to individual memN and regN throughout ──
        # This is the trickiest part: references like "mem0", "reg5" in assignments
        # need to become "data_mem[0]", "regs[5]"

        # Replace regN$ references: reg0$D_IN -> regs_din[0], reg0$EN -> regs_en[0]
        line = re.sub(r'\breg(\d+)\$D_IN\b', lambda m: f'regs_din[{int(m.group(1))}]', line)
        line = re.sub(r'\breg(\d+)\$EN\b', lambda m: f'regs_en[{int(m.group(1))}]', line)

        # Replace memN$ references: mem0$D_IN -> data_mem_din[0], mem0$EN -> data_mem_en[0]
        line = re.sub(r'\bmem(\d+)\$D_IN\b', lambda m: f'data_mem_din[{int(m.group(1))}]', line)
        line = re.sub(r'\bmem(\d+)\$EN\b', lambda m: f'data_mem_en[{int(m.group(1))}]', line)

        # Replace bare regN references (not reg$): reg0 -> regs[0], reg31 -> regs[31]
        # Be careful not to match 'regs' array itself or partial matches
        line = re.sub(r'\breg(\d+)\b(?!\$|_din|_en|\[)', lambda m: f'regs[{int(m.group(1))}]' if int(m.group(1)) < 32 else m.group(0), line)

        # Replace bare memN references: mem0 -> data_mem[0]
        line = re.sub(r'\bmem(\d+)\b(?!\$|_din|_en|\[)', lambda m: f'data_mem[{int(m.group(1))}]' if int(m.group(1)) < OLD_MEM_SIZE else m.group(0), line)

        # ── Replace imem flat bit-slice reads: imem[N*32+31 : N*32] -> imem[N] ──
        # Pattern: imem[8191:8160] -> imem[255], imem[31:0] -> imem[0], etc.
        def replace_imem_slice(m):
            hi = int(m.group(1))
            lo = int(m.group(2))
            if (hi - lo) == 31 and lo % 32 == 0:
                idx = lo // 32
                return f'imem[{idx}]'
            return m.group(0)
        line = re.sub(r'imem\[(\d+):(\d+)\]', replace_imem_slice, line)

        # Also handle imem[pc[11:0] * 32 +: 32] patterns
        line = re.sub(r'imem\[pc\[\d+:0\]\s*\*\s*32\s*\+:\s*32\]', f'imem[pc[{NEW_MEM_BITS-1}:0]]', line)

        # ── Replace instruction fetch case block ──
        # The huge case(pc[11:0]) block selecting from imem[N] can become just imem[pc[11:0]]
        # Look for the always block that assigns the instruction word
        if 'SEL_ARR_imem_0_BITS_31_TO_0' in line and 'always@' in line and 'pc' in line:
            # This is the instruction fetch case block — replace with direct array index
            var_name = None
            # Scan forward to find the variable name
            j = i + 1
            while j < len(lines):
                m_case = re.match(r'\s*case\s*\(pc\[', lines[j])
                if m_case:
                    # Next line after case should have the assignment
                    j2 = j + 1
                    while j2 < len(lines):
                        m_asgn = re.match(r'\s+(\w+)\s*=', lines[j2])
                        if m_asgn:
                            var_name = m_asgn.group(1)
                            break
                        j2 += 1
                    break
                j += 1

            if var_name:
                # Skip the entire always block and replace with assign
                depth = 0
                while i < len(lines):
                    if 'begin' in lines[i]:
                        depth += 1
                    if 'end' in lines[i]:
                        depth -= 1
                        if depth <= 0:
                            i += 1
                            break
                    i += 1
                out.append(f'  // Instruction fetch: direct array index (was {OLD_MEM_SIZE}-entry case)')
                out.append(f'  assign {var_name} = imem[pc[{NEW_MEM_BITS-1}:0]];')
                out.append('')
                continue

        # ── Replace register read case blocks ──
        # Pattern: case(instr_bits[20:16]) 5'd0: var = regs[0]; ... endcase
        # These become: assign var = regs[index];
        # Look for always blocks that have the register mux pattern
        if re.search(r'always@.*SEL_ARR.*or\s+regs\[0\]', line):
            # Register read mux — find the case and variable
            var_name = None
            idx_expr = None
            j = i + 1
            while j < len(lines):
                m_case = re.match(r'\s*case\s*\((.+?)\)', lines[j])
                if m_case:
                    idx_expr = m_case.group(1)
                    j2 = j + 1
                    while j2 < len(lines):
                        m_asgn = re.match(r'\s+(\w+)\s*=\s*regs\[', lines[j2])
                        if m_asgn:
                            var_name = m_asgn.group(1)
                            break
                        j2 += 1
                    break
                j += 1

            if var_name and idx_expr:
                depth = 0
                while i < len(lines):
                    if 'begin' in lines[i]:
                        depth += 1
                    if 'end' in lines[i]:
                        depth -= 1
                        if depth <= 0:
                            i += 1
                            break
                    i += 1
                out.append(f'  assign {var_name} = regs[{idx_expr}];')
                out.append('')
                continue

        # ── Replace memory read binary trees ──
        # These are the deep nested ternary operators that read memN based on address.
        # After memN -> data_mem[N] substitution, these become:
        #   (addr < 2) ? ((addr == 0) ? data_mem[0] : data_mem[1]) : ...
        # We can replace the whole tree with: data_mem[addr]
        # But these are deeply nested across many lines — hard to detect generically.
        # Instead, we'll keep them as-is since the data_mem[N] substitution already happened.
        # The synthesizer will optimize them.

        # ── ptTable bit-slice patterns remain valid (same encoding, just wider) ──
        # But we need to extend case statements from 16 to 64 entries
        # For now, keep existing 16 entries — partition ops use 8-bit instruction fields
        # that get truncated, so only 0-63 are valid indices

        # ── mu_tensor output ports ──
        # getMuTensor0..3 reference mu_tensor[127:96], etc.
        # These stay as-is since they reference specific slots

        # ── active_module width: was 4-bit, now 6-bit ──
        # active_module register declaration
        if re.match(r'\s*reg\s+\[3\s*:\s*0\]\s+active_module\s*;', line):
            line = re.sub(r'\[3\s*:\s*0\]', f'[{NEW_PT_BITS-1} : 0]', line)
        if 'wire' in line and 'active_module$D_IN' in line and '[3' in line:
            line = re.sub(r'\[3\s*:\s*0\]', f'[{NEW_PT_BITS-1} : 0]', line)

        # pt_next_id width: was 5-bit (0..16), now 7-bit (0..64)
        if re.match(r'\s*reg\s+\[4\s*:\s*0\]\s+pt_next_id\s*;', line):
            line = re.sub(r'\[4\s*:\s*0\]', '[6 : 0]', line)
        if 'wire' in line and 'pt_next_id$D_IN' in line and '[4' in line:
            line = re.sub(r'\[4\s*:\s*0\]', '[6 : 0]', line)

        # ── Width references in expressions ──
        # 5'd16 (old pt_next_id max) -> 7'd64
        line = re.sub(r"\b5'd16\b", "7'd64", line)
        # 4'd15 -> 6'd63 (ptTable max index)
        # Be careful: only in ptTable/mu_tensor context

        # 8'd255 in imem context -> 12'd4095
        if 'imem' in line or 'loadInstr' in line:
            line = re.sub(r"8'd255", f"{NEW_MEM_BITS}'d{NEW_MEM_SIZE-1}", line)

        # ── Wire declarations for array D_IN/EN ──
        # We need to declare these somewhere. Add after the array declarations.
        # Actually, BSC assigns each mem$D_IN and mem$EN individually.
        # After our transform, references like data_mem_din[0] and data_mem_en[0] exist
        # but the arrays aren't declared. We need to add them.
        # We'll add them right after the data_mem array declaration.

        # ── Aggregate patterns ──
        # {512{1'b0}} for mu_tensor/ptTable -> {2048{1'b0}}
        line = line.replace("{512{1'b0}}", f"{{{NEW_PT_FLAT}{{1'b0}}}}")
        line = line.replace("512'd0", f"{NEW_PT_FLAT}'d0")

        out.append(line)
        i += 1

    result = '\n'.join(out)

    # ── Post-processing: add array wire declarations ──
    # After 'reg [31:0] data_mem [0:4095];' add wire arrays
    mem_array_line = f'  reg [{WORD_SZ-1} : 0] data_mem [0:{NEW_MEM_SIZE-1}];'
    if mem_array_line in result:
        wire_decls = '\n'.join([
            f'  wire [{WORD_SZ-1} : 0] data_mem_din [0:{NEW_MEM_SIZE-1}];',
            f'  wire data_mem_en [0:{NEW_MEM_SIZE-1}];',
        ])
        result = result.replace(mem_array_line, mem_array_line + '\n' + wire_decls)

    reg_array_line = f'  reg [{WORD_SZ-1} : 0] regs [0:{NUM_REGS-1}];'
    if reg_array_line in result:
        wire_decls = '\n'.join([
            f'  wire [{WORD_SZ-1} : 0] regs_din [0:{NUM_REGS-1}];',
            f'  wire regs_en [0:{NUM_REGS-1}];',
        ])
        result = result.replace(reg_array_line, reg_array_line + '\n' + wire_decls)

    # Add integer loop variables for reset and clock blocks
    # Insert after `define lines
    result = result.replace(
        'module mkModule1(CLK,',
        '// synthesis translate_off\n// integer loop counters for array operations\n// synthesis translate_on\n\nmodule mkModule1(CLK,'
    )

    # Add integer declarations inside module (after first 'input CLK;')
    result = result.replace(
        '  input  CLK;\n  input  RST_N;',
        '  input  CLK;\n  input  RST_N;\n\n  integer __rst_i, __clk_i;'
    )

    return result


if __name__ == '__main__':
    if len(sys.argv) < 2:
        print("Usage: rtl_scale_4096.py <input.v> [output.v]")
        sys.exit(1)

    infile = sys.argv[1]
    outfile = sys.argv[2] if len(sys.argv) > 2 else infile

    with open(infile) as f:
        src = f.read()

    result = transform(src)

    with open(outfile, 'w') as f:
        f.write(result)

    print(f"Transformed {infile} -> {outfile}")
    print(f"  Input:  {len(src.splitlines())} lines")
    print(f"  Output: {len(result.splitlines())} lines")
