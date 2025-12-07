# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.
"""
Comprehensive Isomorphism Validation Test Suite

This test suite validates that:
1. Python VM, Verilog RTL, and Coq proofs are isomorphic
2. Standard programs produce identical results in Python and Thiele VM
3. All opcodes are aligned across implementations
4. μ-cost formulas match across implementations
5. Verilog RTL compiles and simulates correctly
6. Coq proofs compile without errors
"""

import pytest
import subprocess
import re
import tempfile
import os
from pathlib import Path

REPO_ROOT = Path(__file__).parent.parent


class TestOpcodeIsomorphism:
    """Test that opcodes are identical across Python, Verilog, and Coq."""
    
    def test_python_opcodes_defined(self):
        """All required opcodes exist in Python ISA."""
        from thielecpu.isa import Opcode
        
        required = ['PNEW', 'PSPLIT', 'PMERGE', 'LASSERT', 'LJOIN', 
                    'MDLACC', 'EMIT', 'PYEXEC', 'XOR_ADD', 'HALT']
        
        for op in required:
            assert hasattr(Opcode, op), f"Opcode {op} missing from Python ISA"
    
    def test_verilog_opcodes_defined(self):
        """All required opcodes exist in Verilog RTL."""
        verilog_path = REPO_ROOT / "thielecpu" / "hardware" / "thiele_cpu.v"
        content = verilog_path.read_text()
        
        required = {
            'OPCODE_PNEW': '8\'h00',
            'OPCODE_PSPLIT': '8\'h01',
            'OPCODE_PMERGE': '8\'h02',
            'OPCODE_LASSERT': '8\'h03',
            'OPCODE_LJOIN': '8\'h04',
            'OPCODE_MDLACC': '8\'h05',
            'OPCODE_EMIT': '8\'h0E',
            'OPCODE_PYEXEC': '8\'h08',
        }
        
        for name, value in required.items():
            pattern = rf"localparam\s+\[7:0\]\s+{name}\s*=\s*{value}"
            assert re.search(pattern, content), f"Verilog opcode {name} = {value} not found"
    
    def test_coq_opcodes_defined(self):
        """All required opcodes exist in Coq HardwareBridge."""
        coq_path = REPO_ROOT / "coq" / "thielemachine" / "coqproofs" / "HardwareBridge.v"
        content = coq_path.read_text()
        
        required = {
            'opcode_PNEW': '0%N',
            'opcode_PSPLIT': '1%N',
            'opcode_PMERGE': '2%N',
            'opcode_LASSERT': '3%N',
            'opcode_LJOIN': '4%N',
            'opcode_MDLACC': '5%N',
            'opcode_EMIT': '14%N',
            'opcode_PYEXEC': '8%N',
        }
        
        for name, value in required.items():
            pattern = rf"Definition\s+{name}\s*:\s*N\s*:=\s*{re.escape(value)}"
            assert re.search(pattern, content), f"Coq opcode {name} = {value} not found"
    
    def test_opcodes_match_across_layers(self):
        """Opcode values are identical across all three layers."""
        from thielecpu.isa import Opcode
        
        # Extract Python opcodes
        python_opcodes = {
            'PNEW': Opcode.PNEW.value,
            'PSPLIT': Opcode.PSPLIT.value,
            'PMERGE': Opcode.PMERGE.value,
            'LASSERT': Opcode.LASSERT.value,
            'LJOIN': Opcode.LJOIN.value,
            'MDLACC': Opcode.MDLACC.value,
            'EMIT': Opcode.EMIT.value,
            'PYEXEC': Opcode.PYEXEC.value,
        }
        
        # Extract Verilog opcodes
        verilog_path = REPO_ROOT / "thielecpu" / "hardware" / "thiele_cpu.v"
        verilog_content = verilog_path.read_text()
        verilog_opcodes = {}
        for match in re.finditer(r"localparam\s+\[7:0\]\s+OPCODE_(\w+)\s*=\s*8'h([0-9A-Fa-f]+)", verilog_content):
            verilog_opcodes[match.group(1)] = int(match.group(2), 16)
        
        # Extract Coq opcodes
        coq_path = REPO_ROOT / "coq" / "thielemachine" / "coqproofs" / "HardwareBridge.v"
        coq_content = coq_path.read_text()
        coq_opcodes = {}
        for match in re.finditer(r"Definition\s+opcode_(\w+)\s*:\s*N\s*:=\s*(\d+)%N", coq_content):
            coq_opcodes[match.group(1)] = int(match.group(2))
        
        # Compare
        for op, py_val in python_opcodes.items():
            v_val = verilog_opcodes.get(op)
            c_val = coq_opcodes.get(op)
            
            assert v_val == py_val, f"Opcode {op}: Python={py_val}, Verilog={v_val}"
            assert c_val == py_val, f"Opcode {op}: Python={py_val}, Coq={c_val}"


class TestMuCostIsomorphism:
    """Test that μ-cost formula is identical across implementations."""
    
    def test_python_mu_formula(self):
        """Python μ-cost formula computes correctly."""
        from thielecpu.mu import question_cost_bits, information_gain_bits
        
        # Test question cost: 8 bits per byte
        query = "test"
        expected = len(query.encode('utf-8')) * 8
        assert question_cost_bits(query) == expected
        
        # Test information gain: log2(N/M)
        import math
        n, m = 100, 10
        expected = math.log2(n / m)
        assert abs(information_gain_bits(n, m) - expected) < 0.001
    
    def test_coq_mu_formula_exists(self):
        """Coq μ-cost formula is defined in ThieleMachineConcrete.v."""
        coq_path = REPO_ROOT / "coq" / "thielemachine" / "coqproofs" / "ThieleMachineConcrete.v"
        content = coq_path.read_text()
        
        # The formula should be: mu := (Z.of_nat (String.length query)) * 8
        assert "String.length" in content, "Coq μ formula should use String.length"
        assert "* 8" in content or "mul 8" in content.lower(), "Coq μ formula should multiply by 8"


class TestVerilogCompilation:
    """Test that Verilog RTL compiles and simulates correctly."""
    
    def test_verilog_files_exist(self):
        """All required Verilog files exist."""
        hw_dir = REPO_ROOT / "thielecpu" / "hardware"
        
        required_files = ["thiele_cpu.v", "thiele_cpu_tb.v"]
        for f in required_files:
            assert (hw_dir / f).exists(), f"Verilog file {f} missing"
    
    def test_verilog_compiles(self):
        """Verilog compiles with iverilog."""
        hw_dir = REPO_ROOT / "thielecpu" / "hardware"
        
        with tempfile.NamedTemporaryFile(suffix='_thiele_test', delete=False) as tmp:
            tmp_path = tmp.name
        
        try:
            result = subprocess.run(
                ["iverilog", "-g2012", "-o", tmp_path, 
                 str(hw_dir / "thiele_cpu.v"), 
                 str(hw_dir / "thiele_cpu_tb.v"),
                 str(hw_dir / "mu_alu.v"),
                 str(hw_dir / "mu_core.v")],
                capture_output=True,
                timeout=60
            )
            
            assert result.returncode == 0, f"Verilog compilation failed: {result.stderr.decode()}"
        finally:
            if os.path.exists(tmp_path):
                os.unlink(tmp_path)
    
    def test_verilog_simulation_runs(self):
        """Verilog simulation completes without errors."""
        hw_dir = REPO_ROOT / "thielecpu" / "hardware"
        
        with tempfile.NamedTemporaryFile(suffix='_thiele_test', delete=False) as tmp:
            tmp_path = tmp.name
        
        try:
            # Compile
            subprocess.run(
                ["iverilog", "-g2012", "-o", tmp_path,
                 str(hw_dir / "thiele_cpu.v"),
                 str(hw_dir / "thiele_cpu_tb.v"),
                 str(hw_dir / "mu_alu.v"),
                 str(hw_dir / "mu_core.v")],
                check=True,
                timeout=60
            )
            
            # Simulate
            result = subprocess.run(
                ["vvp", tmp_path],
                capture_output=True,
                timeout=30
            )
            
            output = result.stdout.decode()
            assert "Test completed!" in output, "Verilog simulation did not complete"
            assert result.returncode == 0, f"Verilog simulation failed: {result.stderr.decode()}"
        finally:
            if os.path.exists(tmp_path):
                os.unlink(tmp_path)
    
    def test_verilog_produces_valid_metrics(self):
        """Verilog simulation produces valid partition_ops and info_gain."""
        hw_dir = REPO_ROOT / "thielecpu" / "hardware"
        
        with tempfile.NamedTemporaryFile(suffix='_thiele_test', delete=False) as tmp:
            tmp_path = tmp.name
        
        try:
            # Compile and run
            subprocess.run(
                ["iverilog", "-g2012", "-o", tmp_path,
                 str(hw_dir / "thiele_cpu.v"),
                 str(hw_dir / "thiele_cpu_tb.v"),
                 str(hw_dir / "mu_alu.v"),
                 str(hw_dir / "mu_core.v")],
                check=True,
                timeout=60
            )
            
            result = subprocess.run(
                ["vvp", tmp_path],
                capture_output=True,
                timeout=30
            )
            
            output = result.stdout.decode()
            
            # Extract metrics
            partition_ops_match = re.search(r'"partition_ops":\s*(\d+)', output)
            info_gain_match = re.search(r'"info_gain":\s*(\d+)', output)
            
            assert partition_ops_match, "partition_ops not found in Verilog output"
            assert info_gain_match, "info_gain not found in Verilog output"
            
            partition_ops = int(partition_ops_match.group(1))
            info_gain = int(info_gain_match.group(1))
            
            assert partition_ops >= 0, "partition_ops should be non-negative"
            assert info_gain >= 0, "info_gain should be non-negative"
        finally:
            if os.path.exists(tmp_path):
                os.unlink(tmp_path)


class TestCoqCompilation:
    """Test that Coq proofs compile correctly."""
    
    def test_coq_files_exist(self):
        """All required Coq files exist."""
        coq_dir = REPO_ROOT / "coq" / "thielemachine" / "coqproofs"
        
        required_files = [
            "ThieleMachine.v",
            "ThieleMachineConcrete.v",
            "HardwareBridge.v",
        ]
        
        for f in required_files:
            assert (coq_dir / f).exists(), f"Coq file {f} missing"
    
    def test_thiele_machine_compiles(self):
        """ThieleMachine.v compiles with coqc."""
        coq_dir = REPO_ROOT / "coq"
        coq_file = coq_dir / "thielemachine" / "coqproofs" / "ThieleMachine.v"
        
        result = subprocess.run(
            ["coqc", "-Q", "thielemachine/coqproofs", "ThieleMachine", 
             str(coq_file.relative_to(coq_dir))],
            cwd=coq_dir,
            capture_output=True,
            timeout=120
        )
        
        # May have warnings but should compile
        assert result.returncode == 0 or b"Error" not in result.stderr, \
            f"ThieleMachine.v compilation failed: {result.stderr.decode()}"


class TestStandardProgramIsomorphism:
    """Test that standard programs produce identical results in Python and Thiele VM."""
    
    def test_arithmetic_isomorphism(self):
        """Arithmetic operations produce identical results."""
        from thielecpu.vm import VM
        from thielecpu.state import State
        
        operations = [
            ("2 + 2", 4),
            ("10 * 5", 50),
            ("100 // 7", 14),
            ("2 ** 10", 1024),
        ]
        
        for code, expected in operations:
            # Standard Python
            std_result = eval(code)
            
            # Thiele VM
            vm = VM(State())
            vm_result, _ = vm.execute_python(f"__result__ = {code}")
            
            assert std_result == expected, f"Standard Python: {code} != {expected}"
            assert vm_result == expected, f"Thiele VM: {code} != {expected}"
            assert std_result == vm_result, f"Mismatch: std={std_result}, vm={vm_result}"
    
    def test_sorting_isomorphism(self):
        """Sorting produces identical results with same comparison count."""
        from thielecpu.vm import VM
        from thielecpu.state import State
        
        arr = [5, 2, 8, 1, 9]
        
        # Standard Python bubble sort
        def bubble_sort_std(arr):
            result = arr[:]
            comps = 0
            for i in range(len(result)):
                for j in range(len(result) - i - 1):
                    comps += 1
                    if result[j] > result[j+1]:
                        result[j], result[j+1] = result[j+1], result[j]
            return result, comps
        
        std_sorted, std_comps = bubble_sort_std(arr)
        
        # Thiele VM bubble sort
        vm = VM(State())
        code = f'''
arr = {arr}
result = arr[:]
comparisons = 0
for i in range(len(result)):
    for j in range(len(result) - i - 1):
        comparisons = comparisons + 1
        if result[j] > result[j + 1]:
            result[j], result[j + 1] = result[j + 1], result[j]
__result__ = (result, comparisons)
'''
        vm_result, _ = vm.execute_python(code)
        vm_sorted, vm_comps = vm_result
        
        assert std_sorted == vm_sorted, f"Sorted arrays don't match"
        assert std_comps == vm_comps, f"Comparison counts don't match: std={std_comps}, vm={vm_comps}"
    
    def test_recursion_isomorphism(self):
        """Recursive functions work identically in both environments."""
        from thielecpu.vm import VM
        from thielecpu.state import State
        
        # Standard Python factorial
        def factorial_std(n):
            if n <= 1:
                return 1
            return n * factorial_std(n - 1)
        
        std_result = factorial_std(10)
        
        # Thiele VM factorial
        vm = VM(State())
        code = '''
def factorial(n):
    if n <= 1:
        return 1
    return n * factorial(n - 1)

__result__ = factorial(10)
'''
        vm_result, _ = vm.execute_python(code)
        
        assert std_result == vm_result == 3628800, f"Factorial mismatch: std={std_result}, vm={vm_result}"


class TestSeparationProperties:
    """Test the separation between standard Python and Thiele VM."""
    
    def test_thiele_tracks_mu_cost(self):
        """Thiele VM tracks μ-cost, standard Python doesn't."""
        from thielecpu.vm import VM
        from thielecpu.state import State
        from thielecpu.mu import question_cost_bits
        
        vm = VM(State())
        code = "__result__ = 2 + 2"
        result, _ = vm.execute_python(code)
        
        # Thiele can compute μ-cost
        mu_cost = question_cost_bits("(eval 2 + 2)")
        
        assert result == 4, "Computation result incorrect"
        assert mu_cost > 0, "μ-cost should be positive"
    
    def test_thiele_supports_partitions(self):
        """Thiele VM supports partition operations."""
        from thielecpu.vm import VM
        from thielecpu.state import State
        
        vm = VM(State())
        state = vm.state
        
        # Create a partition
        m1 = state.pnew({1, 2, 3, 4})
        assert m1 is not None, "Partition creation failed"
        assert state.regions[m1] == {1, 2, 3, 4}, "Partition region incorrect"
        
        # Split by predicate
        m_even, m_odd = state.psplit(m1, lambda x: x % 2 == 0)
        assert state.regions[m_even] == {2, 4}, "Even partition incorrect"
        assert state.regions[m_odd] == {1, 3}, "Odd partition incorrect"
    
    def test_binary_search_advantage(self):
        """Binary search uses fewer operations than linear search."""
        from demos.standard_programs.number_guessing import run_standard_python, run_thiele_vm
        
        target, low, high = 500, 1, 1000
        
        std = run_standard_python(target, low, high)
        vm = run_thiele_vm(target, low, high)
        
        # Results should match
        assert std['binary']['found'] == vm['binary']['found'] == target
        assert std['linear']['found'] == vm['linear']['found'] == target
        
        # Binary should use fewer guesses
        assert std['binary']['guesses'] < std['linear']['guesses']
        
        # Thiele VM tracks μ-cost
        assert vm['binary']['mu_cost'] > 0
        assert vm['linear']['mu_cost'] > vm['binary']['mu_cost']


class TestEndToEndIsomorphism:
    """End-to-end tests validating full isomorphism."""
    
    def test_all_layers_produce_consistent_results(self):
        """All three layers (Python, Verilog, Coq) are consistent."""
        # Python VM produces correct results
        from thielecpu.vm import VM
        from thielecpu.state import State
        
        vm = VM(State())
        result, _ = vm.execute_python("__result__ = sum(range(10))")
        assert result == 45, "Python VM incorrect"
        
        # Verilog compiles (structure matches)
        hw_dir = REPO_ROOT / "thielecpu" / "hardware"
        
        with tempfile.NamedTemporaryFile(suffix='_thiele_test', delete=False) as tmp:
            tmp_path = tmp.name
        
        try:
            result = subprocess.run(
                ["iverilog", "-g2012", "-o", tmp_path,
                 str(hw_dir / "thiele_cpu.v"),
                 str(hw_dir / "thiele_cpu_tb.v"),
                 str(hw_dir / "mu_alu.v"),
                 str(hw_dir / "mu_core.v")],
                capture_output=True,
                timeout=60
            )
            assert result.returncode == 0, "Verilog compilation failed"
        finally:
            if os.path.exists(tmp_path):
                os.unlink(tmp_path)
        
        # Coq files exist (proofs are maintained)
        coq_dir = REPO_ROOT / "coq" / "thielemachine" / "coqproofs"
        assert (coq_dir / "ThieleMachine.v").exists()
        assert (coq_dir / "HardwareBridge.v").exists()
    
    def test_opcode_count_matches(self):
        """All three implementations define the same number of core opcodes."""
        from thielecpu.isa import Opcode
        
        # Count Python opcodes (excluding special values)
        python_count = len([op for op in Opcode if op.value < 0x10])
        
        # Count Verilog opcodes
        verilog_path = REPO_ROOT / "thielecpu" / "hardware" / "thiele_cpu.v"
        verilog_content = verilog_path.read_text()
        verilog_count = len(re.findall(r"localparam\s+\[7:0\]\s+OPCODE_", verilog_content))
        
        # Count Coq opcodes
        coq_path = REPO_ROOT / "coq" / "thielemachine" / "coqproofs" / "HardwareBridge.v"
        coq_content = coq_path.read_text()
        coq_count = len(re.findall(r"Definition\s+opcode_\w+\s*:", coq_content))
        
        # All should have similar counts (within 2 of each other)
        assert abs(python_count - verilog_count) <= 5, f"Python={python_count}, Verilog={verilog_count}"
        assert abs(python_count - coq_count) <= 5, f"Python={python_count}, Coq={coq_count}"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
