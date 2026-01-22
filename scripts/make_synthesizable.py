#!/usr/bin/env python3
import sys
import re
from pathlib import Path

def main():
    root = Path(__file__).parent.parent
    input_file = root / "thielecpu/hardware/rtl/thiele_cpu.v"
    output_file = root / "thielecpu/hardware/rtl/thiele_cpu_synth.v"
    
    if not input_file.exists():
        print(f"Error: {input_file} not found")
        sys.exit(1)
        
    content = input_file.read_text()
    
    # Remove $display and $finish
    content = re.sub(r'^\s*\$display\(.*?\);\s*$', '', content, flags=re.MULTILINE)
    content = re.sub(r'^\s*\$finish\b.*?;', '', content, flags=re.MULTILINE)
    
    # Ensure generated_opcodes.vh is included
    if '`include "generated_opcodes.vh"' not in content:
        # Fallback if somehow missing
        content = content.replace("module thiele_cpu", "`include \"generated_opcodes.vh\"\nmodule thiele_cpu")

    # Add synthesizable header if not present
    if "SYNTHESIZABLE VERSION" not in content:
        header = """// ============================================================================
// SYNTHESIZABLE VERSION
// ============================================================================
// This file is auto-generated from thiele_cpu.v with non-synthesizable
// constructs removed for FPGA/ASIC synthesis.
"""
        content = header + content

    output_file.write_text(content)
    print(f"Generated {output_file}")

if __name__ == "__main__":
    main()
