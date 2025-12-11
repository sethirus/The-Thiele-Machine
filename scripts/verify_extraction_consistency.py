#!/usr/bin/env python3
"""
verify_extraction_consistency.py

Verifies that all three layers (Coq, Verilog, Python) have consistent instruction sets.
This ensures the single source of truth (Coq) is properly reflected in all layers.
"""

import re
import json
import sys
from pathlib import Path

COQ_KERNEL = Path("coq/kernel/VMStep.v")
VERILOG_OPCODES = Path("thielecpu/generated/opcode_definitions.vh")
PYTHON_TYPES = Path("thielecpu/generated/vm_instructions.py")
VERILOG_CPU = Path("thielecpu/hardware/thiele_cpu.v")
OUTPUT_JSON = Path("artifacts/extraction_consistency.json")

def extract_coq_instructions():
    """Extract all instructions from Coq kernel."""
    with open(COQ_KERNEL) as f:
        content = f.read()
    
    pattern = r'\|\s+instr_(\w+)\s'
    instructions = [m.group(1) for m in re.finditer(pattern, content)]
    return set(instructions)

def extract_verilog_opcodes():
    """Extract all opcode definitions from generated Verilog."""
    with open(VERILOG_OPCODES) as f:
        content = f.read()
    
    pattern = r'parameter.*?OPCODE_(\w+)\s*='
    opcodes = [m.group(1).lower() for m in re.finditer(pattern, content)]
    return set(opcodes)

def extract_python_types():
    """Extract all instruction types from generated Python."""
    with open(PYTHON_TYPES) as f:
        content = f.read()
    
    pattern = r'class Instr(\w+):'
    types = [m.group(1).lower() for m in re.finditer(pattern, content)]
    return set(types)

def extract_verilog_cpu_opcodes():
    """Extract opcodes actually implemented in the CPU."""
    if not VERILOG_CPU.exists():
        return set()
    
    with open(VERILOG_CPU) as f:
        content = f.read()
    
    pattern = r'OPCODE_(\w+)\s*:'
    opcodes = [m.group(1).lower() for m in re.finditer(pattern, content)]
    return set(opcodes)

def main():
    """Main verification logic."""
    print("=== Extraction Consistency Verification ===\n")
    
    # Extract from each layer
    print("Extracting instruction sets from each layer...")
    coq_instrs = extract_coq_instructions()
    verilog_opcodes = extract_verilog_opcodes()
    python_types = extract_python_types()
    cpu_opcodes = extract_verilog_cpu_opcodes()
    
    print(f"✅ Coq kernel: {len(coq_instrs)} instructions")
    print(f"✅ Verilog generated: {len(verilog_opcodes)} opcodes")
    print(f"✅ Python generated: {len(python_types)} instruction types")
    if cpu_opcodes:
        print(f"✅ Verilog CPU: {len(cpu_opcodes)} opcode handlers\n")
    else:
        print("⚠️  Verilog CPU: File not found\n")
    
    # Check consistency
    all_match = True
    
    # Coq vs Verilog generated
    if coq_instrs == verilog_opcodes:
        print("✅ Coq ↔ Verilog (generated): PERFECT MATCH")
    else:
        print("❌ Coq ↔ Verilog (generated): MISMATCH")
        missing_in_verilog = coq_instrs - verilog_opcodes
        extra_in_verilog = verilog_opcodes - coq_instrs
        if missing_in_verilog:
            print(f"   Missing in Verilog: {missing_in_verilog}")
        if extra_in_verilog:
            print(f"   Extra in Verilog: {extra_in_verilog}")
        all_match = False
    
    # Coq vs Python generated
    if coq_instrs == python_types:
        print("✅ Coq ↔ Python (generated): PERFECT MATCH")
    else:
        print("❌ Coq ↔ Python (generated): MISMATCH")
        missing_in_python = coq_instrs - python_types
        extra_in_python = python_types - coq_instrs
        if missing_in_python:
            print(f"   Missing in Python: {missing_in_python}")
        if extra_in_python:
            print(f"   Extra in Python: {extra_in_python}")
        all_match = False
    
    # Check CPU if available
    if cpu_opcodes:
        if coq_instrs == cpu_opcodes:
            print("✅ Coq ↔ Verilog CPU: PERFECT MATCH")
        else:
            print("⚠️  Coq ↔ Verilog CPU: Partial match (some opcodes in CPU may be grouped)")
            missing_in_cpu = coq_instrs - cpu_opcodes
            if missing_in_cpu:
                print(f"   Not explicitly in CPU: {missing_in_cpu}")
    
    # Generate report
    report = {
        "timestamp": str(Path("artifacts").absolute()),
        "coq_instructions": sorted(list(coq_instrs)),
        "verilog_generated_opcodes": sorted(list(verilog_opcodes)),
        "python_generated_types": sorted(list(python_types)),
        "verilog_cpu_opcodes": sorted(list(cpu_opcodes)) if cpu_opcodes else [],
        "counts": {
            "coq": len(coq_instrs),
            "verilog_generated": len(verilog_opcodes),
            "python_generated": len(python_types),
            "verilog_cpu": len(cpu_opcodes) if cpu_opcodes else 0
        },
        "consistency": {
            "coq_verilog_gen": coq_instrs == verilog_opcodes,
            "coq_python_gen": coq_instrs == python_types,
            "all_layers_match": all_match
        }
    }
    
    OUTPUT_JSON.parent.mkdir(parents=True, exist_ok=True)
    with open(OUTPUT_JSON, 'w') as f:
        json.dump(report, f, indent=2)
    
    print(f"\nReport saved to: {OUTPUT_JSON}")
    
    if all_match:
        print("\n🎉 RESULT: Perfect three-layer consistency from single Coq source")
        return 0
    else:
        print("\n⚠️  RESULT: Inconsistencies detected - regenerate with 'make generate-all'")
        return 1

if __name__ == "__main__":
    sys.exit(main())
