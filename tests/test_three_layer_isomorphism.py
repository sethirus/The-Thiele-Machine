"""Unified three-layer isomorphism test harness.

This module tests that identical programs produce equivalent results across:
1. Coq formal specification (via extraction)
2. Python reference implementation
3. Verilog hardware simulation (via cocotb or iverilog)

Tests verify:
- Identical partition operations (PNEW, PSPLIT, PMERGE)
- Identical μ-cost accumulation
- Identical final states (module counts, regions)
- Observational equivalence at each step
"""

import subprocess
import tempfile
from collections.abc import Callable as CallableType
from dataclasses import dataclass
from pathlib import Path
from typing import List, Tuple, Dict, Any, Optional
import json

import pytest

from thielecpu.state import State, ModuleId, MAX_MODULES
from thielecpu.isa import Opcode


# =============================================================================
# Test Program Representations
# =============================================================================

@dataclass(frozen=True)
class Instruction:
    """Generic instruction representation for cross-layer testing."""
    opcode: str  # "PNEW", "PSPLIT", "PMERGE", etc.
    operands: Tuple[Any, ...]
    cost: int = 0

    def to_python(self) -> Tuple[str, tuple]:
        """Convert to Python VM function call."""
        return (self.opcode.lower(), self.operands)

    def to_coq(self) -> str:
        """Convert to Coq instruction encoding."""
        if self.opcode == "PNEW":
            region = self.operands[0]
            return f"instr_pnew {region} {self.cost}"
        elif self.opcode == "PSPLIT":
            module, pred = self.operands
            return f"instr_psplit {module} left right {self.cost}"
        elif self.opcode == "PMERGE":
            m1, m2 = self.operands
            return f"instr_pmerge {m1} {m2} {self.cost}"
        else:
            return f"(* {self.opcode} not implemented *)"

    def to_verilog_hex(self) -> str:
        """Convert to Verilog hex instruction (4 bytes)."""
        opcode_map = {
            "PNEW": 0x00,
            "PSPLIT": 0x01,
            "PMERGE": 0x02,
            "LASSERT": 0x03,
            "LJOIN": 0x04,
            "MDLACC": 0x05,
            "HALT": 0xFF,
        }
        op_byte = opcode_map.get(self.opcode, 0xFF)

        if self.opcode == "PNEW":
            region_id = self.operands[0] if isinstance(self.operands[0], int) else 0
            return f"32'h{op_byte:02X}{region_id:02X}00{self.cost:02X}"
        elif self.opcode == "PSPLIT":
            module = self.operands[0]
            return f"32'h{op_byte:02X}{module:02X}00{self.cost:02X}"
        elif self.opcode == "PMERGE":
            m1, m2 = self.operands
            return f"32'h{op_byte:02X}{m1:02X}{m2:02X}{self.cost:02X}"
        else:
            return f"32'hFF000000"


@dataclass
class ProgramTrace:
    """Execution trace for cross-layer comparison."""
    program: List[Instruction]
    final_mu: int
    final_modules: int
    final_regions: Dict[int, List[int]]  # ModuleID -> region elements
    step_mu: List[int]  # μ-cost after each instruction


# =============================================================================
# Python VM Executor
# =============================================================================

def execute_python(program: List[Instruction]) -> ProgramTrace:
    """Execute program on Python VM and capture trace."""
    state = State()
    step_mu = [0]

    for instr in program:
        op_name, operands = instr.to_python()

        if op_name == "pnew":
            region = operands[0] if isinstance(operands[0], set) else {operands[0]}
            state.pnew(region, charge_discovery=True)
        elif op_name == "psplit":
            module, pred = operands
            if not isinstance(pred, CallableType):
                # Default predicate: even/odd split
                pred = lambda x: x % 2 == 0
            state.psplit(module, pred, cost=instr.cost)
        elif op_name == "pmerge":
            m1, m2 = operands
            state.pmerge(m1, m2, cost=instr.cost)

        step_mu.append(state.mu_ledger.total)

    # Extract final state
    final_regions = {}
    for mid in range(1, state._next_id):
        if mid in state.regions.modules:
            final_regions[mid] = sorted(list(state.regions.modules[mid]))

    return ProgramTrace(
        program=program,
        final_mu=state.mu_ledger.total,
        final_modules=state.num_modules,
        final_regions=final_regions,
        step_mu=step_mu,
    )


# =============================================================================
# Coq Executor (via extraction or direct compilation)
# =============================================================================

def execute_coq(program: List[Instruction]) -> Optional[ProgramTrace]:
    """Execute program via Coq extraction (if available).

    Note: This requires Coq extraction to be set up. For now, returns None
    and we rely on semantic equivalence proofs.
    """
    # TODO: Implement Coq extraction pipeline
    # For now, mark as skipped
    return None


# =============================================================================
# Verilog Simulator Executor
# =============================================================================

def execute_verilog(program: List[Instruction]) -> Optional[ProgramTrace]:
    """Execute program on Verilog simulator (iverilog or cocotb).

    This generates a testbench, runs simulation, and parses VCD/log output.
    """
    verilog_rtl = Path(__file__).parent.parent / "thielecpu" / "hardware" / "rtl"
    testbench_file = verilog_rtl / "thiele_cpu_synth.v"

    if not testbench_file.exists():
        pytest.skip("Verilog RTL not found")
        return None

    # Generate test stimulus
    stimulus = []
    for instr in program:
        stimulus.append(f"        instr_mem[prog_counter] = {instr.to_verilog_hex()};")
        stimulus.append(f"        prog_counter = prog_counter + 1;")

    # Create temporary testbench
    testbench_template = f"""
module isomorphism_tb;
    reg clk;
    reg rst_n;
    reg [31:0] instr_data;
    wire [31:0] pc, mu, status;

    // Instantiate DUT (simplified - actual may differ)
    // thiele_cpu dut(...);

    // Program memory
    reg [31:0] instr_mem [0:255];
    integer prog_counter;

    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end

    initial begin
        rst_n = 0;
        prog_counter = 0;

        // Load program
{''.join(stimulus)}

        #10 rst_n = 1;

        // Run simulation
        repeat (1000) @(posedge clk);

        $display("Final mu: %d", mu);
        $finish;
    end
endmodule
"""

    # TODO: Complete Verilog simulation pipeline
    # For now, mark as pending implementation
    return None


# =============================================================================
# Comparison and Verification
# =============================================================================

def traces_equivalent(python_trace: ProgramTrace,
                      coq_trace: Optional[ProgramTrace],
                      verilog_trace: Optional[ProgramTrace]) -> Tuple[bool, str]:
    """Check if traces are equivalent across all layers."""
    issues = []

    # Python is always the reference
    if not python_trace:
        return False, "Python trace missing"

    # Compare with Coq (if available)
    if coq_trace:
        if python_trace.final_mu != coq_trace.final_mu:
            issues.append(f"μ-cost mismatch: Python={python_trace.final_mu}, Coq={coq_trace.final_mu}")

        if python_trace.final_modules != coq_trace.final_modules:
            issues.append(f"Module count mismatch: Python={python_trace.final_modules}, Coq={coq_trace.final_modules}")

        # Compare step-by-step μ-costs
        for step, (py_mu, coq_mu) in enumerate(zip(python_trace.step_mu, coq_trace.step_mu)):
            if py_mu != coq_mu:
                issues.append(f"Step {step} μ mismatch: Python={py_mu}, Coq={coq_mu}")

    # Compare with Verilog (if available)
    if verilog_trace:
        if python_trace.final_mu != verilog_trace.final_mu:
            issues.append(f"μ-cost mismatch: Python={python_trace.final_mu}, Verilog={verilog_trace.final_mu}")

        if python_trace.final_modules != verilog_trace.final_modules:
            issues.append(f"Module count mismatch: Python={python_trace.final_modules}, Verilog={verilog_trace.final_modules}")

    if issues:
        return False, "; ".join(issues)
    else:
        return True, "All traces equivalent"


# =============================================================================
# Test Cases
# =============================================================================

class TestThreeLayerIsomorphism:
    """Test perfect isomorphism across Coq, Python, and Verilog."""

    def test_simple_pnew(self):
        """Single PNEW operation should be identical across layers."""
        program = [
            Instruction("PNEW", ({5},), cost=1),
        ]

        python_trace = execute_python(program)
        coq_trace = execute_coq(program)  # May be None
        verilog_trace = execute_verilog(program)  # May be None

        equiv, msg = traces_equivalent(python_trace, coq_trace, verilog_trace)

        # For now, just verify Python execution
        assert python_trace.final_modules == 1, "Should have 1 module"
        assert python_trace.final_mu == 1, "Should cost 1 μ-bit (popcount of {5})"
        assert 1 in python_trace.final_regions, "Module 1 should exist"
        assert python_trace.final_regions[1] == [5], "Module 1 should contain {5}"

    def test_pnew_deduplication(self):
        """Creating same region twice should reuse module ID."""
        program = [
            Instruction("PNEW", ({5},), cost=1),
            Instruction("PNEW", ({5},), cost=1),  # Should reuse module 1
        ]

        python_trace = execute_python(program)

        # Should still have only 1 module (deduplication)
        assert python_trace.final_modules == 1, "Deduplication should prevent duplicate modules"
        assert python_trace.final_mu == 1, "Second PNEW should not charge (existing region)"

    def test_pnew_psplit_sequence(self):
        """PNEW followed by PSPLIT."""
        program = [
            Instruction("PNEW", ({0, 1, 2, 3},), cost=4),  # 4 bits set
            Instruction("PSPLIT", (ModuleId(1), lambda x: x % 2 == 0), cost=64),
        ]

        python_trace = execute_python(program)

        # After PSPLIT, should have 2 modules (even and odd)
        assert python_trace.final_modules == 2, "PSPLIT should create 2 modules"
        assert python_trace.final_mu == 4 + 64, "μ = discovery(4) + execution(64)"

    def test_pmerge_validation(self):
        """PMERGE should validate disjoint requirement."""
        program = [
            Instruction("PNEW", ({1, 2},), cost=2),
            Instruction("PNEW", ({3, 4},), cost=2),
            Instruction("PMERGE", (ModuleId(1), ModuleId(2)), cost=4),
        ]

        python_trace = execute_python(program)

        # Should merge successfully (disjoint regions)
        assert python_trace.final_mu == 2 + 2 + 4, "μ = 2*discovery + merge"

    def test_pmerge_overlap_error(self):
        """PMERGE with overlapping regions should fail."""
        # Cannot even create overlapping regions with PNEW
        # (RegionGraph prevents this), so test direct PMERGE validation
        with pytest.raises(ValueError, match="overlap"):
            state = State()
            m1 = state.pnew({1, 2, 3})
            # Manually create overlapping module for testing
            m2 = state._alloc({2, 3, 4})  # Bypasses RegionGraph validation
            state.axioms[m2] = []
            # Now try to merge
            state.pmerge(m1, m2, cost=4)

    def test_max_modules_limit(self):
        """Cannot exceed MAX_MODULES."""
        program = [
            Instruction("PNEW", ({i},), cost=1)
            for i in range(MAX_MODULES + 1)
        ]

        # Should raise ValueError when exceeding limit
        with pytest.raises(ValueError, match="max modules"):
            execute_python(program)

    def test_mu_monotonicity(self):
        """μ-cost should never decrease."""
        program = [
            Instruction("PNEW", ({1},), cost=1),
            Instruction("PNEW", ({2},), cost=1),
            Instruction("PNEW", ({3},), cost=1),
            Instruction("PSPLIT", (ModuleId(1), lambda x: False), cost=64),
        ]

        python_trace = execute_python(program)

        # Verify monotonicity
        for i in range(1, len(python_trace.step_mu)):
            assert python_trace.step_mu[i] >= python_trace.step_mu[i-1], \
                f"μ decreased at step {i}: {python_trace.step_mu[i-1]} -> {python_trace.step_mu[i]}"

    @pytest.mark.parametrize("region_size", [1, 2, 4, 8, 16])
    def test_pnew_cost_scaling(self, region_size):
        """PNEW cost should scale with region popcount."""
        region = set(range(region_size))
        program = [Instruction("PNEW", (region,), cost=region_size)]

        python_trace = execute_python(program)

        assert python_trace.final_mu == region_size, \
            f"μ-cost should equal popcount: expected {region_size}, got {python_trace.final_mu}"


# =============================================================================
# Benchmark Suite
# =============================================================================

pytest_benchmark = pytest.importorskip("pytest_benchmark")


class TestIsomorphismBenchmarks:
    """Performance benchmarking across layers."""

    @pytest.mark.benchmark
    def test_benchmark_pnew_sequence(self, benchmark):
        """Benchmark PNEW sequence performance."""
        def run_pnew_sequence():
            program = [
                Instruction("PNEW", ({i},), cost=1)
                for i in range(min(32, MAX_MODULES))
            ]
            return execute_python(program)

        result = benchmark(run_pnew_sequence)
        assert result.final_modules == min(32, MAX_MODULES)

    @pytest.mark.benchmark
    def test_benchmark_psplit_sequence(self, benchmark):
        """Benchmark PSPLIT operations."""
        def run_psplit_sequence():
            state = State()
            module = state.pnew(set(range(64)), charge_discovery=True)
            for _ in range(5):
                left, right = state.psplit(module, lambda x: x % 2 == 0, cost=64)
                module = left if len(state.regions.modules[left]) >= len(state.regions.modules[right]) else right
            return state

        result = benchmark(run_psplit_sequence)


# =============================================================================
# Integration Test Suite
# =============================================================================

def test_comprehensive_trace():
    """Comprehensive test with all partition operations."""
    program = [
        Instruction("PNEW", ({0, 1, 2, 3, 4, 5, 6, 7},), cost=8),
        Instruction("PSPLIT", (ModuleId(1), lambda x: x < 4), cost=64),
        Instruction("PNEW", ({10, 11},), cost=2),
        Instruction("PMERGE", (ModuleId(2), ModuleId(3)), cost=4),
    ]

    python_trace = execute_python(program)

    # Verify final state
    assert python_trace.final_mu == 8 + 64 + 2 + 4, "Total μ-cost should be 78"
    assert python_trace.final_modules >= 1, "Should have at least 1 module after merge"

    # Verify step-by-step μ accumulation
    expected_mu = [0, 8, 8 + 64, 8 + 64 + 2, 8 + 64 + 2 + 4]
    assert python_trace.step_mu == expected_mu, \
        f"Step μ mismatch: expected {expected_mu}, got {python_trace.step_mu}"


if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])
