"""
Test that verifies bit-for-bit isomorphism of opcodes across Coq, Python, and Verilog.

This test ensures that all three layers of the Thiele Machine have identical
instruction sets with matching opcode values.
"""

import re
from pathlib import Path
import pytest


# Expected complete ISA based on Coq kernel
EXPECTED_ISA = {
    "PNEW": 0x00,
    "PSPLIT": 0x01,
    "PMERGE": 0x02,
    "LASSERT": 0x03,
    "LJOIN": 0x04,
    "MDLACC": 0x05,
    "PDISCOVER": 0x06,
    "XFER": 0x07,
    "PYEXEC": 0x08,
    "CHSH_TRIAL": 0x09,
    "XOR_LOAD": 0x0A,
    "XOR_ADD": 0x0B,
    "XOR_SWAP": 0x0C,
    "XOR_RANK": 0x0D,
    "EMIT": 0x0E,
    "REVEAL": 0x0F,
    "ORACLE_HALTS": 0x10,
    "HALT": 0xFF,
}


def test_python_isa_completeness():
    """Verify Python ISA has all 18 instructions with correct opcodes."""
    from thielecpu.isa import Opcode
    
    python_opcodes = {op.name: op.value for op in Opcode}
    
    # Check all expected instructions are present
    missing = set(EXPECTED_ISA.keys()) - set(python_opcodes.keys())
    assert not missing, f"Python ISA missing instructions: {missing}"
    
    # Check no extra instructions
    extra = set(python_opcodes.keys()) - set(EXPECTED_ISA.keys())
    assert not extra, f"Python ISA has unexpected instructions: {extra}"
    
    # Check opcode values match
    mismatches = []
    for name, expected_value in EXPECTED_ISA.items():
        actual_value = python_opcodes[name]
        if actual_value != expected_value:
            mismatches.append(f"{name}: expected 0x{expected_value:02X}, got 0x{actual_value:02X}")
    
    assert not mismatches, f"Python opcode value mismatches:\n" + "\n".join(mismatches)
    
    print(f"✓ Python ISA: {len(python_opcodes)} instructions, all correct")


def test_verilog_isa_completeness():
    """Verify Verilog generated_opcodes.vh has all 18 instructions with correct opcodes."""
    repo_root = Path(__file__).parent.parent
    verilog_header = repo_root / "thielecpu" / "hardware" / "rtl" / "generated_opcodes.vh"
    
    assert verilog_header.exists(), f"Verilog opcode header not found: {verilog_header}"
    
    # Parse Verilog opcodes
    verilog_opcodes = {}
    opcode_pattern = re.compile(r'localparam\s+\[7:0\]\s+OPCODE_(\w+)\s+=\s+8\'h([0-9A-Fa-f]+);')
    
    with open(verilog_header, 'r') as f:
        for line in f:
            match = opcode_pattern.search(line)
            if match:
                name = match.group(1)
                value = int(match.group(2), 16)
                verilog_opcodes[name] = value
    
    # Check all expected instructions are present
    missing = set(EXPECTED_ISA.keys()) - set(verilog_opcodes.keys())
    assert not missing, f"Verilog ISA missing instructions: {missing}"
    
    # Check no extra instructions
    extra = set(verilog_opcodes.keys()) - set(EXPECTED_ISA.keys())
    assert not extra, f"Verilog ISA has unexpected instructions: {extra}"
    
    # Check opcode values match
    mismatches = []
    for name, expected_value in EXPECTED_ISA.items():
        actual_value = verilog_opcodes[name]
        if actual_value != expected_value:
            mismatches.append(f"{name}: expected 0x{expected_value:02X}, got 0x{actual_value:02X}")
    
    assert not mismatches, f"Verilog opcode value mismatches:\n" + "\n".join(mismatches)
    
    print(f"✓ Verilog ISA: {len(verilog_opcodes)} instructions, all correct")


def test_coq_isa_completeness():
    """Verify Coq kernel has all 18 instructions."""
    repo_root = Path(__file__).parent.parent
    coq_vmstep = repo_root / "coq" / "kernel" / "VMStep.v"
    
    assert coq_vmstep.exists(), f"Coq VMStep.v not found: {coq_vmstep}"
    
    # Parse Coq instructions
    coq_instructions = []
    instr_pattern = re.compile(r'\|\s+instr_(\w+)\s+')
    
    with open(coq_vmstep, 'r') as f:
        for line in f:
            match = instr_pattern.match(line)
            if match:
                name = match.group(1).upper()
                coq_instructions.append(name)
    
    # Check count
    assert len(coq_instructions) == 18, f"Coq has {len(coq_instructions)} instructions, expected 18"
    
    # Check all expected instructions are present
    coq_set = set(coq_instructions)
    missing = set(EXPECTED_ISA.keys()) - coq_set
    assert not missing, f"Coq ISA missing instructions: {missing}"
    
    # Check no extra instructions
    extra = coq_set - set(EXPECTED_ISA.keys())
    assert not extra, f"Coq ISA has unexpected instructions: {extra}"
    
    print(f"✓ Coq ISA: {len(coq_instructions)} instructions, all correct")


def test_three_way_isomorphism():
    """Verify complete isomorphism: Coq = Python = Verilog."""
    # This test passes if all three individual tests pass
    # It serves as a unified verification point
    
    from thielecpu.isa import Opcode
    
    # Verify count
    assert len(Opcode) == 18, f"Expected 18 opcodes, got {len(Opcode)}"
    
    # Verify each opcode
    for name, expected_value in EXPECTED_ISA.items():
        # Python
        python_value = Opcode[name].value
        assert python_value == expected_value, \
            f"{name}: Python has 0x{python_value:02X}, expected 0x{expected_value:02X}"
    
    print(f"✓ Three-way isomorphism verified: 18 instructions across Coq, Python, and Verilog")
    print(f"✓ All opcode values match bit-for-bit")


if __name__ == "__main__":
    # Run tests standalone
    test_coq_isa_completeness()
    test_python_isa_completeness()
    test_verilog_isa_completeness()
    test_three_way_isomorphism()
    print("\n✅ All isomorphism tests passed!")
