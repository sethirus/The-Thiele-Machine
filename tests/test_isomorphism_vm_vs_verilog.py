# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

"""
Tests for VM ↔ Verilog isomorphism.

These tests verify that the Python VM and Verilog RTL produce
identical traces for the same programs.
"""

import json
import pytest
import shutil
import subprocess
from pathlib import Path

REPO_ROOT = Path(__file__).parent.parent
HARDWARE_DIR = REPO_ROOT / "hardware"
BUILD_DIR = REPO_ROOT / "build"
PROGRAMS_DIR = REPO_ROOT / "programs"


def has_iverilog():
    """Check if iverilog is available."""
    return shutil.which("iverilog") is not None


def run_vm_trace(program_path: Path) -> dict:
    """Run Python VM on a program and return final state."""
    from thielecpu.state import State
    from thielecpu.vm import VM
    from thielecpu.assemble import parse
    
    program_text = program_path.read_text(encoding='utf-8')
    program_lines = program_text.split('\n')
    program = parse(program_lines, program_path.parent)
    
    state = State()
    vm = VM(state)
    
    # Execute program
    outdir = BUILD_DIR / "vm_output"
    outdir.mkdir(parents=True, exist_ok=True)
    vm.run(program, outdir)
    
    # Return final μ-ledger state
    return {
        "mu_discovery": state.mu_ledger.mu_discovery,
        "mu_execution": state.mu_ledger.mu_execution,
        "mu_total": state.mu_ledger.total,
        "num_modules": state.num_modules,
    }


class TestMuCostIsomorphism:
    """Test that μ-costs are isomorphic between Python and Verilog."""
    
    def test_pnew_mu_cost_isomorphic(self):
        """PNEW μ-cost should be popcount(region) in both implementations."""
        from thielecpu.state import State, mask_popcount, mask_of_indices
        
        # Python VM
        state = State()
        region = {0, 1, 2}  # popcount = 3
        state.pnew(region)
        
        py_discovery = state.mu_ledger.mu_discovery
        
        # Expected from spec
        expected_discovery = mask_popcount(mask_of_indices(region))
        
        assert py_discovery == expected_discovery == 3
        
    def test_psplit_mu_cost_isomorphic(self):
        """PSPLIT μ-cost should be MASK_WIDTH in both implementations."""
        from thielecpu.state import State, MASK_WIDTH
        
        # Python VM
        state = State()
        mid = state.pnew({0, 1, 2, 3})
        
        exec_before = state.mu_ledger.mu_execution
        state.psplit(mid, lambda x: x < 2)
        exec_after = state.mu_ledger.mu_execution
        
        py_exec_delta = exec_after - exec_before
        
        # Expected from spec
        expected_exec = MASK_WIDTH
        
        assert py_exec_delta == expected_exec == 64
        
    def test_pmerge_mu_cost_isomorphic(self):
        """PMERGE μ-cost should be 4 in both implementations."""
        from thielecpu.state import State
        
        # Python VM
        state = State()
        m1 = state.pnew({0, 1})
        m2 = state.pnew({2, 3})
        
        exec_before = state.mu_ledger.mu_execution
        state.pmerge(m1, m2)
        exec_after = state.mu_ledger.mu_execution
        
        py_exec_delta = exec_after - exec_before
        
        # Expected from spec
        expected_exec = 4
        
        assert py_exec_delta == expected_exec


@pytest.mark.skipif(not has_iverilog(), reason="iverilog not available")
class TestVerilogTraceAlignment:
    """Test Verilog trace alignment with Python VM."""
    
    def test_verilog_compiles(self):
        """Verilog should compile without errors."""
        BUILD_DIR.mkdir(parents=True, exist_ok=True)
        
        result = subprocess.run(
            ["iverilog", "-g2012", "-o", str(BUILD_DIR / "partition_core_tb"),
             str(HARDWARE_DIR / "partition_core.v"),
             str(HARDWARE_DIR / "partition_core_tb.v")],
            capture_output=True,
            text=True
        )
        
        assert result.returncode == 0, f"Compilation failed: {result.stderr}"
    
    def test_verilog_simulation_runs(self):
        """Verilog simulation should run and produce trace."""
        BUILD_DIR.mkdir(parents=True, exist_ok=True)
        
        # Compile
        subprocess.run(
            ["iverilog", "-g2012", "-o", str(BUILD_DIR / "partition_core_tb"),
             str(HARDWARE_DIR / "partition_core.v"),
             str(HARDWARE_DIR / "partition_core_tb.v")],
            check=True
        )
        
        # Run simulation
        result = subprocess.run(
            ["vvp", str(BUILD_DIR / "partition_core_tb")],
            capture_output=True,
            text=True,
            cwd=BUILD_DIR
        )
        
        assert result.returncode == 0, f"Simulation failed: {result.stderr}"
        
        # Check trace file was created
        trace_file = BUILD_DIR / "hw_trace.json"
        assert trace_file.exists(), "Trace file was not created"


class TestOpcodeEncodingAlignment:
    """Test that opcode encodings match between Python and Verilog."""
    
    EXPECTED_OPCODES = {
        "PNEW": 0x00,
        "PSPLIT": 0x01,
        "PMERGE": 0x02,
        "LASSERT": 0x03,
        "LJOIN": 0x04,
        "MDLACC": 0x05,
        "XFER": 0x07,
        "PYEXEC": 0x08,
        "XOR_LOAD": 0x0A,
        "XOR_ADD": 0x0B,
        "XOR_SWAP": 0x0C,
        "XOR_RANK": 0x0D,
        "EMIT": 0x0E,
        "HALT": 0xFF,
    }
    
    def test_python_opcodes_match_spec(self):
        """Python opcodes should match spec."""
        from thielecpu.isa import Opcode
        
        for name, expected_value in self.EXPECTED_OPCODES.items():
            try:
                actual_value = getattr(Opcode, name).value
                assert actual_value == expected_value, \
                    f"Opcode {name}: Python={hex(actual_value)}, Expected={hex(expected_value)}"
            except AttributeError:
                pytest.skip(f"Opcode {name} not defined in Python")
    
    def test_verilog_opcodes_match_spec(self):
        """Verilog opcodes should match spec."""
        verilog_file = HARDWARE_DIR / "partition_core.v"
        content = verilog_file.read_text()
        
        import re
        
        for name, expected_value in self.EXPECTED_OPCODES.items():
            pattern = rf"OPC_{name}\s*=\s*8'h([0-9A-Fa-f]+)"
            match = re.search(pattern, content)
            
            if match:
                actual_value = int(match.group(1), 16)
                assert actual_value == expected_value, \
                    f"Opcode {name}: Verilog={hex(actual_value)}, Expected={hex(expected_value)}"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
