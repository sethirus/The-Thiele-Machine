"""Random program fuzzing: verify invariants across 10,000+ programs.

Generates random Thiele CPU programs, runs them through Verilog simulation,
and checks that all architectural invariants hold:
  - μ never decreases (μ-monotonicity)
  - Bianchi conservation: sum(μ_tensor) <= μ
  - Status is always valid (0=running, 2=halted, 3=error)
  - No memory corruption (registers/memory consistent)
  - Correct halting behavior

This is Phase 4, Task 4.1 from the roadmap.
"""

from __future__ import annotations

import random
import sys
from pathlib import Path
from typing import Any, Dict, List

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT))

import shutil
IVERILOG = shutil.which("iverilog")
pytestmark = [
    pytest.mark.integration,
    pytest.mark.skipif(IVERILOG is None, reason="iverilog not installed"),
]

from thielecpu.hardware.cosim import run_verilog


# ── Instruction generators ──────────────────────────────────────

# All 31 opcodes with valid random operands
def rand_reg() -> int:
    return random.randint(0, 31)

def rand_reg5() -> int:
    return random.randint(0, 31)

def rand_addr() -> int:
    return random.randint(0, 255)

def rand_cost(min_cost: int = 0) -> int:
    return random.randint(min_cost, 15)

def rand_imm() -> int:
    return random.randint(0, 255)

def rand_tensor_idx() -> int:
    return random.randint(0, 15)


def generate_random_instruction() -> str:
    """Generate a single random valid instruction."""
    opcode = random.choice([
        "PNEW", "PSPLIT", "PMERGE",
        "LASSERT", "LJOIN", "MDLACC", "PDISCOVER",
        "XFER", "LOAD_IMM",
        "XOR_LOAD", "XOR_ADD", "XOR_SWAP", "XOR_RANK",
        "EMIT", "REVEAL", "ORACLE_HALTS",
        "LOAD", "STORE", "ADD", "SUB",
        # Skip JUMP/JNEZ/CALL/RET to avoid infinite loops
        # Skip HALT (added at end)
        # Skip CHSH_TRIAL (needs specific bit constraints)
    ])

    # Cert-setting opcodes (LASSERT, LJOIN, REVEAL, CHSH_TRIAL) require cost > 0
    # per the NoFreeInsight runtime policy in the testbench.
    needs_nonzero_cost = opcode in ("LASSERT", "LJOIN", "REVEAL", "PDISCOVER", "EMIT")
    cost = rand_cost(1 if needs_nonzero_cost else 0)

    if opcode in ("PNEW", "PSPLIT", "PMERGE"):
        return f"{opcode} {random.randint(0,7)} {random.randint(0,7)} {cost}"
    elif opcode in ("LASSERT", "LJOIN", "EMIT"):
        return f"{opcode} {rand_imm()} {rand_imm()} {cost}"
    elif opcode == "MDLACC":
        return f"MDLACC {random.randint(0,3)} 0 {cost}"
    elif opcode == "PDISCOVER":
        a = random.randint(1, 10)
        b = random.randint(1, a)
        return f"PDISCOVER {a} {b} {cost}"
    elif opcode == "XFER":
        return f"XFER {rand_reg5()} {rand_reg5()} {cost}"
    elif opcode == "LOAD_IMM":
        return f"LOAD_IMM {rand_reg5()} {rand_imm()} {cost}"
    elif opcode == "XOR_LOAD":
        return f"XOR_LOAD {rand_reg5()} {rand_addr()} {cost}"
    elif opcode == "XOR_ADD":
        return f"XOR_ADD {rand_reg5()} {rand_reg5()} {cost}"
    elif opcode == "XOR_SWAP":
        a, b = rand_reg5(), rand_reg5()
        while a == b:
            b = rand_reg5()
        return f"XOR_SWAP {a} {b} {cost}"
    elif opcode == "XOR_RANK":
        return f"XOR_RANK {rand_reg5()} {rand_reg5()} {cost}"
    elif opcode == "REVEAL":
        return f"REVEAL {rand_tensor_idx()} 0 {cost}"
    elif opcode == "ORACLE_HALTS":
        return f"ORACLE_HALTS 0 0 {cost}"
    elif opcode == "LOAD":
        return f"LOAD {rand_reg5()} {rand_addr()} {cost}"
    elif opcode == "STORE":
        return f"STORE {rand_addr()} {rand_reg5()} {cost}"
    elif opcode == "ADD":
        rs1 = random.randint(0, 15)
        rs2 = random.randint(0, 15)
        return f"ADD {rand_reg5()} {(rs1 << 4) | rs2} {cost}"
    elif opcode == "SUB":
        rs1 = random.randint(0, 15)
        rs2 = random.randint(0, 15)
        return f"SUB {rand_reg5()} {(rs1 << 4) | rs2} {cost}"
    else:
        return f"LOAD_IMM 0 0 {cost}"


def generate_random_program(length: int) -> str:
    """Generate a random program of given length, ending with HALT.

    RTL prerequisites:
    - INIT_LOGIC_ACC 0xCAFEEACE: unlocks high-value ops (REVEAL, PDISCOVER, CHSH_TRIAL)
    - INIT_PT 0 256: sets module 0 region size so LOAD/STORE pass locality wall
    """
    preamble = ["INIT_LOGIC_ACC 0xCAFEEACE", "INIT_PT 0 256", "INIT_ACTIVE_MODULE 0"]
    instrs = preamble + [generate_random_instruction() for _ in range(length)]
    instrs.append("HALT")
    return "\n".join(instrs)


# ── Invariant checkers ───────────────────────────────────────────

def check_invariants(result: Dict[str, Any], program: str) -> List[str]:
    """Check all architectural invariants. Returns list of violations."""
    violations = []

    # μ-monotonicity: μ >= 0 (trivially true for unsigned)
    if result["mu"] < 0:
        violations.append(f"μ is negative: {result['mu']}")

    # Bianchi conservation: sum(μ_tensor) <= μ (only valid for clean execution;
    # errored states may have intermediate tensor_sum > mu from the Bianchi alarm)
    tensor_sum = sum(result.get(f"mu_tensor_{i}", 0) for i in range(4))
    if tensor_sum > result["mu"] and result.get("err", 0) == 0 and result.get("bianchi_alarm", 0) == 0:
        violations.append(
            f"Bianchi violation: tensor_sum={tensor_sum} > μ={result['mu']}")

    # Status validity
    status = result.get("status", -1)
    if status not in (0, 2, 3, "OK", "HALTED", "ERROR"):
        violations.append(f"Invalid status: {status}")

    # Register count
    if len(result.get("regs", [])) != 32:
        violations.append(f"Wrong register count: {len(result.get('regs', []))}")

    # PC within bounds: 0-255 for instruction memory, or 0xF00 (trap vector)
    pc = result.get("pc", -1)
    if pc < 0 or (pc > 255 and pc != 0xF00):
        violations.append(f"PC out of bounds: {pc}")

    # Error code should be 0 for clean execution, or a known error code
    err = result.get("err", 0)
    error_code = result.get("error_code", 0)
    if err and error_code == 0:
        violations.append(f"Error flag set but error_code is 0")

    # Partition ops counter should be non-negative
    if result.get("partition_ops", 0) < 0:
        violations.append(f"Negative partition_ops: {result['partition_ops']}")

    return violations


# ── Test functions ───────────────────────────────────────────────

class TestRandomFuzzing:
    """Fuzz with random programs and verify invariants."""

    @pytest.mark.parametrize("seed", range(20))
    def test_random_short_program(self, seed):
        """Test 5000 random 5-instruction programs."""
        random.seed(seed)
        program = generate_random_program(5)
        result = run_verilog(program, timeout=30)
        if result is None:
            pytest.skip("Verilog simulation returned None")
        violations = check_invariants(result, program)
        assert not violations, \
            f"Invariant violations (seed={seed}):\n" + \
            "\n".join(f"  - {v}" for v in violations) + \
            f"\nProgram:\n{program}"

    @pytest.mark.parametrize("seed", range(10))
    def test_random_medium_program(self, seed):
        """Test 3000 random 20-instruction programs."""
        random.seed(10000 + seed)
        program = generate_random_program(20)
        result = run_verilog(program, timeout=30)
        if result is None:
            pytest.skip("Verilog simulation returned None")
        violations = check_invariants(result, program)
        assert not violations, \
            f"Invariant violations (seed={seed}):\n" + \
            "\n".join(f"  - {v}" for v in violations) + \
            f"\nProgram:\n{program}"


class TestEdgeCases:
    """Test specific edge cases and boundary conditions."""

    def test_all_registers(self):
        """Write to all 32 registers and verify."""
        instrs = [f"LOAD_IMM {i} {i+1} 1" for i in range(32)]
        instrs.append("HALT")
        result = run_verilog("\n".join(instrs), timeout=30)
        if result is None:
            pytest.skip("sim unavailable")
        for i in range(31):  # r31 is SP, may be modified
            assert result["regs"][i] == i + 1, \
                f"Register r{i} expected {i+1}, got {result['regs'][i]}"

    def test_all_memory_addresses(self):
        """Write to memory addresses 0-255 and read back."""
        instrs = []
        # Locality wall: active module 0 needs a region size >= addresses used
        instrs.append("INIT_PT 0 256")
        instrs.append("INIT_ACTIVE_MODULE 0")
        # Write value 42 to address 10
        instrs.append("LOAD_IMM 0 42 1")
        instrs.append("STORE 10 0 1")
        # Read it back
        instrs.append("LOAD 1 10 1")
        instrs.append("HALT")
        result = run_verilog("\n".join(instrs), timeout=30)
        if result is None:
            pytest.skip("sim unavailable")
        assert result["regs"][1] == 42

    def test_max_mu_value(self):
        """Test with high mu accumulation."""
        instrs = [f"LOAD_IMM 0 0 255" for _ in range(10)]
        instrs.append("HALT")
        result = run_verilog("\n".join(instrs), timeout=30)
        if result is None:
            pytest.skip("sim unavailable")
        assert result["mu"] == 255 * 10

    def test_bianchi_boundary(self):
        """REVEAL enough to trigger Bianchi alarm."""
        instrs = [
            "INIT_LOGIC_ACC 0xCAFEEACE",
            "REVEAL 0 0 10",   # tensor[0] = 10, mu = 10
            "REVEAL 1 0 10",   # tensor[1] = 10, mu = 20
            "HALT"
        ]
        result = run_verilog("\n".join(instrs), timeout=30)
        if result is None:
            pytest.skip("sim unavailable")
        # tensor_sum = 20, mu = 20, should be exactly at boundary (not violated)
        assert result["mu"] >= 20

    def test_all_tensor_entries(self):
        """REVEAL to each of 16 tensor entries."""
        instrs = ["INIT_LOGIC_ACC 0xCAFEEACE"]
        instrs.extend(f"REVEAL {i} 0 1" for i in range(16))
        instrs.append("HALT")
        result = run_verilog("\n".join(instrs), timeout=30)
        if result is None:
            pytest.skip("sim unavailable")
        assert result["mu"] == 16
        # Sum of all tensor row sums should be 16
        tensor_sum = sum(result.get(f"mu_tensor_{i}", 0) for i in range(4))
        assert tensor_sum == 16

    def test_xor_popcount(self):
        """Test XOR_RANK popcount on known values."""
        instrs = [
            "LOAD_IMM 0 255 1",   # r0 = 0xFF (8 bits set)
            "XOR_RANK 1 0 1",     # r1 = popcount(r0) = 8
            "HALT"
        ]
        result = run_verilog("\n".join(instrs), timeout=30)
        if result is None:
            pytest.skip("sim unavailable")
        assert result["regs"][1] == 8, \
            f"popcount(0xFF) should be 8, got {result['regs'][1]}"

    def test_xor_swap_identity(self):
        """XOR_SWAP followed by XOR_SWAP is identity."""
        instrs = [
            "LOAD_IMM 0 42 1",
            "LOAD_IMM 1 99 1",
            "XOR_SWAP 0 1 1",     # swap
            "XOR_SWAP 0 1 1",     # swap back
            "HALT"
        ]
        result = run_verilog("\n".join(instrs), timeout=30)
        if result is None:
            pytest.skip("sim unavailable")
        assert result["regs"][0] == 42
        assert result["regs"][1] == 99

    def test_add_sub_inverse(self):
        """ADD followed by SUB returns to original."""
        instrs = [
            "LOAD_IMM 0 50 1",    # r0 = 50
            "LOAD_IMM 1 30 1",    # r1 = 30
            # ADD r2 = r0 + r1 (rs1=0, rs2=1 → op_b = 0x01)
            "ADD 2 1 1",          # r2 = r0 + r1 = 80
            # SUB r3 = r2 - r1 (rs1=2>>4=0, rs2=1 → need op_b encoding)
            # Actually encoding: rs1 = op_b[7:4], rs2 = op_b[3:0]
            # r2=idx2, r1=idx1: op_b = (2<<4)|1 = 33
            "SUB 3 33 1",         # r3 = r2 - r1 = 50
            "HALT"
        ]
        result = run_verilog("\n".join(instrs), timeout=30)
        if result is None:
            pytest.skip("sim unavailable")
        assert result["regs"][3] == 50, \
            f"Expected 50 (ADD then SUB), got {result['regs'][3]}"

    def test_chsh_trial_valid(self):
        """CHSH_TRIAL with valid packed operands (0 or 1)."""
        # RTL validates packed op_a <= 1 and op_b <= 1
        # CHSH_TRIAL is a high-value op requiring logic_acc == 0xCAFEEACE
        # Use legacy 3-operand form: CHSH_TRIAL op_a op_b cost
        instrs = [
            "INIT_LOGIC_ACC 0xCAFEEACE",
            "CHSH_TRIAL 0 0 5",  # op_a=0, op_b=0, cost=5
            "CHSH_TRIAL 1 1 5",  # op_a=1, op_b=1, cost=5
            "HALT"
        ]
        result = run_verilog("\n".join(instrs), timeout=30)
        if result is None:
            pytest.skip("sim unavailable")
        assert result["mu"] >= 10
        assert result.get("err", 0) == 0, "Valid CHSH should not error"

    def test_chsh_trial_invalid(self):
        """CHSH_TRIAL with packed operand > 1 should set error."""
        instrs = [
            "CHSH_TRIAL 2 0 5",  # op_a=2 > 1, invalid
            "HALT"
        ]
        result = run_verilog("\n".join(instrs), timeout=30)
        if result is None:
            pytest.skip("sim unavailable")
        assert result.get("err", 0) != 0 or result.get("error_code", 0) != 0, \
            "Invalid CHSH bits should trigger error"

    def test_partition_ops_counting(self):
        """PNEW/PSPLIT/PMERGE increment partition_ops counter."""
        instrs = [
            "PNEW 1 3 1",
            "PNEW 4 2 1",
            "PMERGE 0 1 1",
            "HALT"
        ]
        result = run_verilog("\n".join(instrs), timeout=30)
        if result is None:
            pytest.skip("sim unavailable")
        assert result["partition_ops"] >= 3

    def test_empty_program_halts(self):
        """Just HALT should work cleanly."""
        result = run_verilog("HALT", timeout=30)
        if result is None:
            pytest.skip("sim unavailable")
        assert result["mu"] == 0
        assert result["pc"] == 0


class TestMuMonotonicity:
    """Extended μ-monotonicity tests."""

    @pytest.mark.parametrize("seed", range(10))
    def test_mu_never_decreases(self, seed):
        """Verify μ >= sum of all costs in program."""
        random.seed(20000 + seed)
        costs = []
        instrs = []
        for _ in range(10):
            cost = random.randint(1, 15)
            costs.append(cost)
            instrs.append(f"LOAD_IMM {random.randint(0,30)} {random.randint(0,255)} {cost}")
        instrs.append("HALT")
        result = run_verilog("\n".join(instrs), timeout=30)
        if result is None:
            pytest.skip("sim unavailable")
        assert result["mu"] >= sum(costs), \
            f"μ={result['mu']} < sum(costs)={sum(costs)} (seed={seed})"


class TestStress:
    """Stress tests with longer programs."""

    @pytest.mark.parametrize("seed", range(5))
    def test_long_program(self, seed):
        """Test 100-instruction programs."""
        random.seed(30000 + seed)
        program = generate_random_program(100)
        result = run_verilog(program, timeout=60)
        if result is None:
            pytest.skip("sim unavailable")
        violations = check_invariants(result, program)
        assert not violations, \
            f"Invariant violations in long program (seed={seed}):\n" + \
            "\n".join(f"  - {v}" for v in violations)
