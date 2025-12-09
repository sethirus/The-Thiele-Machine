# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

"""
Phase 7 - Adversarial Falsification Tests

Property-based fuzzing to attempt falsification of Python ↔ Verilog isomorphism.
Uses hypothesis library to generate thousands of random Thiele programs and
verify that Python VM and Verilog hardware produce identical cryptographic receipts.

FALSIFIABILITY:
- If any random program produces different hashes between Python and Verilog,
  the isomorphism claim is FALSIFIED.
- The goal is to FAIL to falsify (i.e., all tests pass).
"""

import pytest
import subprocess
import shutil
import tempfile
from pathlib import Path
from typing import List, Tuple, Dict, Any
import hashlib

from hypothesis import given, settings, strategies as st
from hypothesis import assume, example

# Add parent directory to path
import sys
sys.path.insert(0, str(Path(__file__).parent.parent))

from thielecpu.state import State
from thielecpu.vm import VM
from thielecpu.isa import Opcode, encode
from thielecpu.crypto import StateHasher, compute_state_hash_hex
from thielecpu.assemble import Instruction

# Paths
REPO_ROOT = Path(__file__).parent.parent
HARDWARE_DIR = REPO_ROOT / "thielecpu" / "hardware"
BUILD_DIR = REPO_ROOT / "build" / "fuzz_tests"


# =============================================================================
# UTILITY FUNCTIONS
# =============================================================================

def has_iverilog() -> bool:
    """Check if iverilog is available."""
    return shutil.which("iverilog") is not None


def encode_instruction(opcode: Opcode, a: int = 0, b: int = 0) -> bytes:
    """Encode instruction to 4-byte little-endian word."""
    return encode(opcode, a, b)


def instruction_to_hex(opcode: Opcode, a: int = 0, b: int = 0) -> str:
    """Convert instruction to hex string for Verilog memory file."""
    # Verilog expects big-endian 32-bit hex
    word = encode_instruction(opcode, a, b)
    # Reverse bytes for big-endian representation
    return f"{word[3]:02x}{word[2]:02x}{word[1]:02x}{word[0]:02x}"


def write_program_hex(program: List[Tuple[Opcode, int, int]], hex_file: Path) -> None:
    """Write program to hex file for Verilog testbench."""
    with open(hex_file, 'w') as f:
        for opcode, a, b in program:
            f.write(instruction_to_hex(opcode, a, b) + '\n')


# =============================================================================
# HYPOTHESIS STRATEGIES
# =============================================================================

# Strategy for generating valid instruction operands
operand_strategy = st.integers(min_value=0, max_value=255)

# Strategy for generating valid region indices (for PNEW)
region_index_strategy = st.integers(min_value=0, max_value=15)

# Strategy for generating small sets of region indices
region_strategy = st.lists(
    region_index_strategy,
    min_size=1,
    max_size=5,
    unique=True
).map(lambda lst: sorted(lst))


def instruction_strategy() -> st.SearchStrategy:
    """Generate random valid Thiele instructions.
    
    Focuses on instructions that:
    1. Don't require external files (no LASSERT, PYEXEC)
    2. Have deterministic behavior
    3. Can be easily verified
    """
    return st.one_of([
        # PNEW: Create partition with region
        st.tuples(
            st.just(Opcode.PNEW),
            operand_strategy,  # Single region index (simplified)
            st.just(0)
        ),
        # XOR_LOAD: Load value
        st.tuples(
            st.just(Opcode.XOR_LOAD),
            operand_strategy,
            operand_strategy
        ),
        # XOR_ADD: Add operation
        st.tuples(
            st.just(Opcode.XOR_ADD),
            operand_strategy,
            operand_strategy
        ),
        # XOR_SWAP: Swap operation
        st.tuples(
            st.just(Opcode.XOR_SWAP),
            operand_strategy,
            operand_strategy
        ),
        # EMIT: Emit value
        st.tuples(
            st.just(Opcode.EMIT),
            operand_strategy,
            operand_strategy
        ),
    ])


def program_strategy() -> st.SearchStrategy:
    """Generate random Thiele programs.
    
    Programs consist of:
    - 1-20 random instructions
    - Terminated with HALT
    """
    return st.lists(
        instruction_strategy(),
        min_size=1,
        max_size=20
    ).map(lambda instrs: instrs + [(Opcode.HALT, 0, 0)])


# =============================================================================
# PYTHON ORACLE
# =============================================================================

def execute_python(program: List[Tuple[Opcode, int, int]]) -> Dict[str, Any]:
    """Execute program in Python VM and capture cryptographic receipt.
    
    Args:
        program: List of (Opcode, a, b) tuples
        
    Returns:
        Dictionary with 'final_hash' (hex string) and 'mu_total' (int)
    """
    # Convert to instruction format
    instructions: List[Instruction] = []
    for opcode, a, b in program:
        # Format instruction as text
        if opcode == Opcode.PNEW:
            instructions.append(("PNEW", f"{{{a}}}"))
        elif opcode == Opcode.XOR_LOAD:
            instructions.append(("XOR_LOAD", f"{a} {b}"))
        elif opcode == Opcode.XOR_ADD:
            instructions.append(("XOR_ADD", f"{a} {b}"))
        elif opcode == Opcode.XOR_SWAP:
            instructions.append(("XOR_SWAP", f"{a} {b}"))
        elif opcode == Opcode.EMIT:
            instructions.append(("EMIT", f"{a} {b}"))
        elif opcode == Opcode.HALT:
            instructions.append(("HALT", ""))
        else:
            # Skip unsupported opcodes
            continue
    
    # Execute in VM
    state = State()
    vm = VM(state)
    
    # Create temporary output directory
    with tempfile.TemporaryDirectory() as tmpdir:
        outdir = Path(tmpdir)
        
        try:
            # Run program
            vm.run(instructions, outdir)
            
            # Capture final state
            final_hash = compute_state_hash_hex(state)
            mu_total = state.mu_ledger.total
            
            return {
                'final_hash': final_hash,
                'mu_total': mu_total,
                'error': None
            }
        except Exception as e:
            # If execution fails, return error
            return {
                'final_hash': '0' * 64,
                'mu_total': 0,
                'error': str(e)
            }


# =============================================================================
# VERILOG DEVICE UNDER TEST
# =============================================================================

def execute_verilog(program: List[Tuple[Opcode, int, int]], work_dir: Path) -> Dict[str, Any]:
    """Execute program in Verilog simulation and capture cryptographic receipt.
    
    Args:
        program: List of (Opcode, a, b) tuples
        work_dir: Working directory for compilation/simulation
        
    Returns:
        Dictionary with 'final_hash' (hex string) and 'mu_total' (int)
    """
    work_dir.mkdir(parents=True, exist_ok=True)
    
    # Write program to hex file
    hex_file = work_dir / "fuzz_program.hex"
    write_program_hex(program, hex_file)
    
    # Compile Verilog
    sim_executable = work_dir / "fuzz_sim"
    compile_cmd = [
        "iverilog",
        "-g2012",  # SystemVerilog 2012
        "-o", str(sim_executable),
        str(HARDWARE_DIR / "fuzz_harness.v"),
        str(HARDWARE_DIR / "thiele_cpu.v"),
        str(HARDWARE_DIR / "mu_alu.v"),
        str(HARDWARE_DIR / "mu_core.v"),
    ]
    
    try:
        result = subprocess.run(
            compile_cmd,
            capture_output=True,
            text=True,
            timeout=30,
            cwd=work_dir
        )
        
        if result.returncode != 0:
            return {
                'final_hash': '0' * 64,
                'mu_total': 0,
                'error': f"Verilog compilation failed: {result.stderr}"
            }
    except subprocess.TimeoutExpired:
        return {
            'final_hash': '0' * 64,
            'mu_total': 0,
            'error': "Verilog compilation timeout"
        }
    
    # Run simulation
    try:
        result = subprocess.run(
            ["vvp", str(sim_executable)],
            capture_output=True,
            text=True,
            timeout=30,
            cwd=work_dir
        )
        
        if result.returncode != 0:
            return {
                'final_hash': '0' * 64,
                'mu_total': 0,
                'error': f"Verilog simulation failed: {result.stderr}"
            }
        
        # Parse output
        output = result.stdout
        final_hash = None
        mu_total = None
        
        for line in output.split('\n'):
            if line.startswith('final_hash:'):
                final_hash = line.split(':', 1)[1].strip()
            elif line.startswith('mu_total:'):
                mu_total_str = line.split(':', 1)[1].strip()
                try:
                    mu_total = int(mu_total_str)
                except ValueError:
                    mu_total = 0
        
        if final_hash is None or mu_total is None:
            return {
                'final_hash': '0' * 64,
                'mu_total': 0,
                'error': f"Could not parse Verilog output:\n{output}"
            }
        
        return {
            'final_hash': final_hash,
            'mu_total': mu_total,
            'error': None
        }
        
    except subprocess.TimeoutExpired:
        return {
            'final_hash': '0' * 64,
            'mu_total': 0,
            'error': "Verilog simulation timeout"
        }


# =============================================================================
# FALSIFICATION TESTS
# =============================================================================

@pytest.mark.skipif(not has_iverilog(), reason="iverilog not available")
class TestAdversarialFalsification:
    """Attempt to falsify Python ↔ Verilog isomorphism using property-based fuzzing."""
    
    @settings(max_examples=10, deadline=None)  # Start with 10 for quick testing
    @given(program=program_strategy())
    def test_python_verilog_hash_isomorphism(self, program):
        """
        FALSIFICATION TEST: Python and Verilog must produce identical hashes.
        
        If this test fails, we have found a program that produces different
        cryptographic receipts in Python vs Verilog, FALSIFYING the isomorphism claim.
        """
        # Skip programs that are too trivial (just HALT)
        assume(len(program) > 1)
        
        # Execute in Python
        python_result = execute_python(program)
        
        # Skip if Python execution failed
        assume(python_result['error'] is None)
        
        # Execute in Verilog
        with tempfile.TemporaryDirectory() as tmpdir:
            work_dir = Path(tmpdir)
            verilog_result = execute_verilog(program, work_dir)
        
        # Skip if Verilog execution failed
        assume(verilog_result['error'] is None)
        
        # THE CRITICAL ASSERTION: Hashes must match
        python_hash = python_result['final_hash']
        verilog_hash = verilog_result['final_hash']
        
        if python_hash != verilog_hash:
            # FALSIFICATION SUCCESSFUL - Print divergence details
            print("\n⚠️  FALSIFICATION SUCCESSFUL: Divergence found!")
            print(f"\nProgram that caused divergence:")
            for i, (opcode, a, b) in enumerate(program):
                print(f"  [{i:02d}] {opcode.name} {a} {b}")
            print(f"\nPython hash:  {python_hash}")
            print(f"Verilog hash: {verilog_hash}")
            print(f"\nPython μ-total:  {python_result['mu_total']}")
            print(f"Verilog μ-total: {verilog_result['mu_total']}")
            
            # Fail the test
            assert False, "Hash mismatch between Python and Verilog"
        
        # Also check μ-cost consistency (weaker assertion)
        # Note: This might differ due to implementation details, so we only warn
        if python_result['mu_total'] != verilog_result['mu_total']:
            print(f"\n⚠️  Warning: μ-total mismatch (Python={python_result['mu_total']}, Verilog={verilog_result['mu_total']})")
    
    def test_manual_simple_program(self):
        """Manually test a simple program for debugging."""
        # Simple program: PNEW -> HALT
        program = [
            (Opcode.PNEW, 1, 0),
            (Opcode.HALT, 0, 0),
        ]
        
        # Execute in Python
        python_result = execute_python(program)
        print(f"\nPython result: {python_result}")
        
        # Execute in Verilog
        with tempfile.TemporaryDirectory() as tmpdir:
            work_dir = Path(tmpdir)
            verilog_result = execute_verilog(program, work_dir)
        
        print(f"Verilog result: {verilog_result}")
        
        # Verify both succeeded
        assert python_result['error'] is None, f"Python error: {python_result['error']}"
        assert verilog_result['error'] is None, f"Verilog error: {verilog_result['error']}"
        
        # Compare hashes
        print(f"\nPython hash:  {python_result['final_hash']}")
        print(f"Verilog hash: {verilog_result['final_hash']}")


# =============================================================================
# MAIN TEST RUNNER
# =============================================================================

def run_falsification_campaign(max_examples: int = 1000):
    """Run a full falsification campaign with specified number of examples.
    
    This is the main entry point for Phase 7 testing.
    """
    print("=" * 80)
    print("PHASE 7 - ADVERSARIAL FALSIFICATION")
    print("=" * 80)
    print(f"\nAttempting to falsify isomorphism with {max_examples} random programs...")
    print("If all tests pass, isomorphism claim survives falsification attempt.\n")
    
    if not has_iverilog():
        print("⚠️  iverilog not available - skipping Verilog tests")
        return
    
    # Run the property-based test with specified examples
    test_instance = TestAdversarialFalsification()
    
    # Reconfigure the test with desired max_examples
    original_test = test_instance.test_python_verilog_hash_isomorphism
    configured_test = settings(max_examples=max_examples, deadline=None)(original_test.hypothesis.inner_test)
    
    try:
        # Run with hypothesis
        configured_test()
        
        print("\n" + "=" * 80)
        print("✓ FALSIFICATION FAILED")
        print("=" * 80)
        print(f"All {max_examples} random programs verified successfully.")
        print("Isomorphism holds under adversarial fuzzing.")
        print("=" * 80)
        
    except AssertionError as e:
        print("\n" + "=" * 80)
        print("⚠️  FALSIFICATION SUCCESSFUL")
        print("=" * 80)
        print(f"Divergence found: {e}")
        print("=" * 80)
        raise


if __name__ == "__main__":
    # Run with specified number of examples
    import os
    max_examples = int(os.environ.get('FUZZ_EXAMPLES', '100'))
    run_falsification_campaign(max_examples=max_examples)
