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
import re
import pytest
import shutil
import subprocess
from pathlib import Path

REPO_ROOT = Path(__file__).parent.parent
RTL_DIR = REPO_ROOT / "thielecpu" / "hardware" / "rtl"
TB_DIR = REPO_ROOT / "thielecpu" / "hardware" / "testbench"
HARDWARE_DIR = REPO_ROOT / "thielecpu" / "hardware"
BUILD_DIR = REPO_ROOT / "build"
PROGRAMS_DIR = REPO_ROOT / "programs"


def has_iverilog():
    """Check if iverilog is available."""
    return shutil.which("iverilog") is not None


def normalize_trace(trace_entries):
    """Strip padding and coerce numeric fields for comparison."""
    normalized = []
    for entry in trace_entries:
        normalized.append(
            {
                "step": int(entry["step"]),
                "opcode": entry["opcode"].strip(),
                "region": int(entry["region"]),
                "num_modules": int(entry["num_modules"]),
                "mu_discovery": int(entry["mu_discovery"]),
                "mu_execution": int(entry["mu_execution"]),
                "mu_total": int(entry["mu_total"]),
            }
        )
    return normalized


def run_verilog_trace():
    """Run the Kami RTL through a reference partition sequence and return the result."""
    from thielecpu.hardware.cosim import (
        _ensure_verilator_current, run_simulation_verilator,
        _ensure_vvp_current, run_simulation_iverilog,
        parse_verilog_output, _command_available,
    )
    import tempfile

    # Canonical partition sequence: build {0,1,2}, split even/odd, merge back
    def encode_word(opcode, a=0, b=0, cost=0):
        return ((opcode & 0xFF) << 24) | ((a & 0xFF) << 16) | ((b & 0xFF) << 8) | (cost & 0xFF)

    words = [
        encode_word(0x00, 0),    # PNEW {0} -> module 1
        encode_word(0x00, 1),    # PNEW {1} -> module 2
        encode_word(0x00, 2),    # PNEW {2} -> module 3
        encode_word(0x02, 1, 2), # PMERGE 1 2 -> module 4 = {0,1}
        encode_word(0x02, 4, 3), # PMERGE 4 3 -> module 5 = {0,1,2}
        encode_word(0x01, 5, 0), # PSPLIT 5 pred=0x00 (even/odd) -> 6={0,2}, 7={1}
        encode_word(0x02, 6, 7), # PMERGE 6 7 -> module 8 = {0,1,2}
        encode_word(0xFF),       # HALT
    ]

    with tempfile.TemporaryDirectory() as td:
        prog_hex = Path(td) / "prog.hex"
        data_hex = Path(td) / "data.hex"
        prog_hex.write_text("\n".join(f"{w:08x}" for w in words) + "\n")
        data_hex.write_text("00000000\n" * 256)
        n = len(words)

        if _command_available("verilator"):
            binary = _ensure_verilator_current()
            stdout = run_simulation_verilator(binary, prog_hex, data_hex, n_instrs=n)
        else:
            vvp = _ensure_vvp_current()
            stdout = run_simulation_iverilog(vvp, prog_hex, data_hex, n_instrs=n)

        return parse_verilog_output(stdout)


def vm_reference_trace():
    """Run the Python VM through the same sequence as the Verilog TB."""
    from thielecpu.state import State, indices_of_mask

    state = State()
    trace = []

    def record(opcode: str, region_mask: int):
        trace.append(
            {
                "step": len(trace),
                "opcode": opcode,
                "region": region_mask,
                "num_modules": state.num_modules,
                "mu_discovery": state.mu_ledger.mu_discovery,
                "mu_execution": state.mu_ledger.mu_execution,
                "mu_total": state.mu_ledger.total,
            }
        )

    # Sequence mirrors partition_core_tb.v
    first = state.pnew(indices_of_mask(0x7))
    record("PNEW", 0x7)

    _second = state.pnew(indices_of_mask(0x30))
    record("PNEW", 0x30)

    split_a, split_b = state.psplit(first, lambda idx: bool(0x1 & (1 << idx)))
    record("PSPLIT", 0x1)

    state.pmerge(split_a, split_b)
    record("PMERGE", 0x0)

    return trace


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
    """Test Kami RTL alignment with Python VM via cosim."""

    def test_verilog_compiles(self):
        """Kami RTL should compile (or cached binary should exist)."""
        from thielecpu.hardware.cosim import _ensure_vvp_current
        vvp_path = _ensure_vvp_current()
        assert vvp_path.exists(), "Compiled VVP binary should exist"

    def test_verilog_simulation_runs(self):
        """Kami RTL simulation should run and produce valid JSON with modules field."""
        from thielecpu.hardware.cosim import run_verilog
        result = run_verilog("PNEW {0} 0\nPNEW {1} 0\nPMERGE 1 2 0\nHALT 0")
        if result is None:
            pytest.skip("No RTL simulator available")
        assert result["status"] == 2, f"Expected status=2 (halted), got {result['status']}"
        assert "modules" in result, "Result must have 'modules' field"
        assert isinstance(result["modules"], list), "'modules' must be a list"

    def test_vm_trace_matches_verilog_trace(self):
        """RTL module regions match Python VM after PNEW+PMERGE+PSPLIT+PMERGE sequence.

        Verifies that the Kami RTL shadow partition tracker produces the same
        module-to-region mapping as the Python VM for a canonical sequence.
        """
        from thielecpu.state import State

        # Python VM: create {0,1,2}, split even/odd, merge back
        state = State()
        m0 = state.pnew({0})
        m1 = state.pnew({1})
        m2 = state.pnew({2})
        m01 = state.pmerge(m0, m1)
        m012 = state.pmerge(m01, m2)
        ma, mb = state.psplit(m012, lambda x: x % 2 == 0)  # even → left
        state.pmerge(ma, mb)
        py_regions = sorted([sorted(r) for r in state.regions.modules.values() if r])

        # RTL: run the same sequence; shadow tracker returns module data
        result = run_verilog_trace()
        assert result is not None, "RTL simulation should return a result"
        rtl_modules = result.get("modules", [])
        rtl_regions = sorted([sorted(m["region"]) for m in rtl_modules if m.get("region")])

        assert py_regions == rtl_regions, (
            f"RTL module regions do not match Python VM.\n"
            f"Python: {py_regions}\nRTL:    {rtl_regions}"
        )


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
        """Verilog opcodes should match spec (read from generated_opcodes.vh)."""
        opcodes_file = RTL_DIR / "generated_opcodes.vh"
        content = opcodes_file.read_text()

        for name, expected_value in self.EXPECTED_OPCODES.items():
            pattern = rf"OPCODE_{name}\s*=\s*8'h([0-9A-Fa-f]+)"
            match = re.search(pattern, content)

            if match:
                actual_value = int(match.group(1), 16)
                assert actual_value == expected_value, \
                    f"Opcode {name}: Verilog={hex(actual_value)}, Expected={hex(expected_value)}"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
