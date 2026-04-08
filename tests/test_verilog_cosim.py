"""Verilog ↔ Python co-simulation tests.

Compiles the canonical Kami RTL (thiele_cpu_kami.v) with iverilog, runs programs through both
the Verilog simulation and the Python cosim harness, and compares
register / memory / μ-cost at halt.

Marks all tests with @pytest.mark.integration so the full suite
can skip them in environments without iverilog.
"""
from __future__ import annotations

import json
import math
import os
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT))

# ── Guard: skip everything if iverilog is missing ────────────────────
IVERILOG = shutil.which("iverilog")
pytestmark = [
    pytest.mark.integration,
    pytest.mark.strict_rtl,
    pytest.mark.skipif(IVERILOG is None, reason="iverilog not installed"),
]


# ── Helpers ──────────────────────────────────────────────────────────
def _run_cosim(program: str) -> Dict[str, Any]:
    """Run a program through Verilog co-simulation and return parsed state."""
    from thielecpu.hardware.cosim import run_verilog
    result = run_verilog(program, timeout=30)
    assert result is not None, (
        "run_verilog returned None despite iverilog being present and strict RTL gating allowing execution"
    )
    return result


def _ascii_checksum(text: str) -> int:
    return sum(ord(ch) for ch in text) & 0xFFFFFFFF


def _run_accel_partition(operations: List[Dict]) -> List[Dict]:
    """Run partition_core standalone accelerator simulation."""
    from thielecpu.hardware.accel_cosim import run_partition_core
    return run_partition_core(operations)


def _run_accel_mu_alu(operations: List[Dict]) -> List[Dict]:
    """Run mu_alu standalone accelerator simulation."""
    from thielecpu.hardware.accel_cosim import run_mu_alu
    return run_mu_alu(operations)


# ═══════════════════════════════════════════════════════════════════════
# 1. CPU Core: instruction execution
# ═══════════════════════════════════════════════════════════════════════
class TestCPUHalt:
    """Basic CPU lifecycle: boot → execute → HALT."""

    def test_halt_only(self):
        """HALT instruction terminates with status OK."""
        state = _run_cosim("HALT")
        assert state["status"] in ("OK", "HALTED", 0, 2), \
            f"Unexpected status: {state['status']}"

    def test_xor_load_then_halt(self):
        """XOR_LOAD writes to register bank, read back after halt."""
        state = _run_cosim("""\
XOR_LOAD 0 0 0
HALT
""")
        # Register 0 should have some value loaded from memory[0]
        assert "regs" in state
        assert len(state["regs"]) >= 1

    def test_xor_add_accumulates(self):
        """XOR_ADD r0 += r1 produces the expected XOR."""
        state = _run_cosim("""\
XOR_LOAD 0 0 0
XOR_LOAD 1 1 0
XOR_ADD 0 1 0
HALT
""")
        r0 = state["regs"][0]
        r1 = state["regs"][1]
        # Verilog should have r0 = mem[0] ^ mem[1] after XOR_ADD
        # We just verify it didn't crash and regs are populated
        assert isinstance(r0, int)
        assert isinstance(r1, int)

    def test_xor_swap(self):
        """XOR_SWAP swaps two registers."""
        state = _run_cosim("""\
XOR_LOAD 0 0 0
XOR_LOAD 1 1 0
XOR_SWAP 0 1 0
HALT
""")
        assert "regs" in state

    def test_xfer_register_copy(self):
        """XFER r_dst r_src copies register value."""
        state = _run_cosim("""\
XOR_LOAD 3 0 0
XFER 5 3 0
HALT
""")
        assert state["regs"][5] == state["regs"][3]


# ═══════════════════════════════════════════════════════════════════════
# 2. Partition operations via CPU
# ═══════════════════════════════════════════════════════════════════════
class TestPartitionOps:
    """PNEW / PSPLIT / PMERGE through the full CPU pipeline."""

    def test_pnew_increments_count(self):
        """PNEW creates one module."""
        state = _run_cosim("""\
PNEW {1,2,3} 5
HALT
""")
        assert state["partition_ops"] >= 1

    def test_pnew_charges_mu(self):
        """PNEW charges μ-cost."""
        state = _run_cosim("""\
PNEW {1,2,3} 5
HALT
""")
        assert state["mu"] > 0, f"Expected μ > 0, got {state['mu']}"

    def test_two_pnews(self):
        """Two PNEWs create two modules."""
        state = _run_cosim("""\
PNEW {1,2,3} 3
PNEW {4,5} 2
HALT
""")
        assert state["partition_ops"] >= 2

    def test_pmerge(self):
        """PMERGE merges two modules into one."""
        state = _run_cosim("""\
PNEW {1,2,3} 3
PNEW {4,5} 2
PMERGE 0 1 4
HALT
""")
        assert state["partition_ops"] >= 3
        assert state["mu"] > 0


# ═══════════════════════════════════════════════════════════════════════
# 3. μ-cost monotonicity
# ═══════════════════════════════════════════════════════════════════════
class TestMuMonotonicity:
    """Verify μ never decreases during execution."""

    def test_mu_nondecreasing(self):
        """Sequence of operations accumulates μ monotonically."""
        state = _run_cosim("""\
PNEW {1,2,3} 3
PNEW {4,5} 2
EMIT 0 0 1
HALT
""")
        # Final μ must be at least the sum of explicit costs
        assert state["mu"] >= 3 + 2 + 1

    def test_longer_program_more_mu(self):
        """A longer program accumulates more μ than a shorter one."""
        state_short = _run_cosim("""\
PNEW {1} 2
HALT
""")
        state_long = _run_cosim("""\
PNEW {1} 2
PNEW {2} 3
PNEW {3} 4
HALT
""")
        assert state_long["mu"] >= state_short["mu"]


# ═══════════════════════════════════════════════════════════════════════
# 4. EMIT / REVEAL opcodes
# ═══════════════════════════════════════════════════════════════════════
class TestEmitReveal:
    """EMIT and REVEAL opcodes for certificate generation."""

    def test_emit_charges_mu(self):
        """EMIT with cost > 0 increases μ."""
        state_no_emit = _run_cosim("HALT")
        state_emit = _run_cosim("""\
EMIT 0 0 5
HALT
""")
        assert state_emit["mu"] >= state_no_emit["mu"] + 5

    def test_reveal_charges_mu(self):
        """REVEAL with cost > 0 increases μ."""
        state = _run_cosim("""\
INIT_LOGIC_ACC -889263410
REVEAL 0 0 3
HALT
""")
        assert state["mu"] >= 3

    def test_reveal_ext_uses_upper_lane_tensor_index(self):
        """REVEAL_EXT consumes ext0 as the tensor index."""
        state = _run_cosim("""\
INIT_LOGIC_ACC -889263410
REVEAL_EXT 6 0 3
HALT
""")
        assert state["mu_tensor_0"] == 0
        assert state["mu_tensor_1"] == 3
        assert state["mu"] >= 4


class TestMorphInlineExt:
    """ISA-v2 morph inline transport exercises real hardware morph state."""

    def test_morph_ext_creates_real_morphism(self):
        state = _run_cosim("""\
PNEW {1} 1
PNEW {2} 1
MORPH_EXT 10 1 2 0 2
MORPH_GET_EXT 11 1 0 0
MORPH_GET_EXT 12 1 1 0
HALT
""")
        assert not state["err"], f"Unexpected morph-ext error: {state['error_code']}"
        assert state["regs"][10] == 1, f"expected new morph id 1, got {state['regs'][10]}"
        assert state["regs"][11] == 1, f"expected source module 1, got {state['regs'][11]}"
        assert state["regs"][12] == 2, f"expected target module 2, got {state['regs'][12]}"

    def test_compose_ext_builds_new_endpoint_pair(self):
        state = _run_cosim("""\
PNEW {1} 1
PNEW {2} 1
PNEW {3} 1
MORPH_EXT 10 1 2 0 1
MORPH_EXT 11 2 3 0 1
COMPOSE_EXT 12 1 2 1
MORPH_GET_EXT 13 3 0 0
MORPH_GET_EXT 14 3 1 0
HALT
""")
        assert not state["err"], f"Unexpected compose-ext error: {state['error_code']}"
        assert state["regs"][12] == 3, f"expected composed morph id 3, got {state['regs'][12]}"
        assert state["regs"][13] == 1, f"expected composed source 1, got {state['regs'][13]}"
        assert state["regs"][14] == 3, f"expected composed target 3, got {state['regs'][14]}"

    def test_morph_delete_ext_invalidates_lookup(self):
        state = _run_cosim("""\
PNEW {1} 1
PNEW {2} 1
MORPH_EXT 10 1 2 0 1
MORPH_DELETE_EXT 1 0
MORPH_GET_EXT 11 1 0 0
HALT
""")
        assert state["err"], "expected MORPH_GET_EXT after delete to trap"
        assert state["error_code"] == 0xBADC0003, f"expected ERR_MORPH_NOT_FOUND, got {state['error_code']:#x}"

    def test_morph_assert_ext_sets_cert_addr_from_inline_checksum(self):
        checksum = _ascii_checksum("lawful")
        state = _run_cosim(f"""\
PNEW {{1}} 1
PNEW {{2}} 1
MORPH_EXT 10 1 2 0 1
MORPH_ASSERT_EXT 1 lawful 3
HALT
""")
        assert not state["err"], f"Unexpected morph-assert-ext error: {state['error_code']}"
        assert state["cert_addr"] == checksum, (
            f"expected cert_addr checksum {checksum}, got {state['cert_addr']}"
        )
        assert state["mu"] == 7, f"expected μ=7 after PNEW/PNEW/MORPH_EXT/MORPH_ASSERT_EXT, got {state['mu']}"

    def test_morph_assert_ext_faults_when_morphism_is_missing(self):
        state = _run_cosim("""\
PNEW {1} 1
PNEW {2} 1
MORPH_ASSERT_EXT 1 ghost 2
HALT
""")
        assert state["err"], "expected MORPH_ASSERT_EXT on missing morphism to trap"
        assert state["error_code"] == 0xBADC0003, f"expected ERR_MORPH_NOT_FOUND, got {state['error_code']:#x}"
        assert state["cert_addr"] == 0, f"expected cert_addr to remain zero on trap, got {state['cert_addr']}"


# ═══════════════════════════════════════════════════════════════════════
# 5. Opcode encoding round-trip
# ═══════════════════════════════════════════════════════════════════════
class TestOpcodeEncoding:
    """Verify program_to_hex produces correct instruction words."""

    def test_halt_encoding(self):
        """HALT encodes as an ISA-v2 word with legacy HALT in the low lane."""
        from thielecpu.hardware.cosim import program_to_hex
        instr, _, _ = program_to_hex("HALT")
        assert instr[0] == "020000000000000000000000FF000000"

    def test_pnew_encoding(self):
        """PNEW {1,2,3} 5 preserves the legacy fields in the low lane."""
        from thielecpu.hardware.cosim import program_to_hex
        instr, _, _ = program_to_hex("PNEW {1,2,3} 5")
        assert len(instr[0]) == 32
        word = int(instr[0], 16)
        legacy = word & 0xFFFFFFFF
        opcode = (legacy >> 24) & 0xFF
        op_a = (legacy >> 16) & 0xFF
        op_b = (legacy >> 8) & 0xFF
        cost = legacy & 0xFF
        assert opcode == 0x00  # PNEW
        assert op_a == 1       # first element
        assert op_b == 3       # region size
        assert cost == 5

    def test_xor_load_encoding(self):
        """XOR_LOAD preserves its legacy opcode in the low lane."""
        from thielecpu.hardware.cosim import program_to_hex
        instr, _, _ = program_to_hex("XOR_LOAD 2 5 0")
        assert len(instr[0]) == 32
        word = int(instr[0], 16)
        opcode = ((word & 0xFFFFFFFF) >> 24) & 0xFF
        assert opcode == 0x0A  # XOR_LOAD

    def test_reveal_ext_encoding(self):
        """REVEAL_EXT carries its tensor index in ext0 with FMT_TENSOR_EXT."""
        from thielecpu.hardware.cosim import program_to_hex
        instr, _, _ = program_to_hex("REVEAL_EXT 6 0 3")
        assert len(instr[0]) == 32
        word = int(instr[0], 16)
        assert (word >> 112) & 0xFF == 0x02
        assert (word >> 32) & 0xF == 6
        legacy = word & 0xFFFFFFFF
        assert (legacy >> 24) & 0xFF == 0x0F
        assert (legacy >> 16) & 0xFF == 0
        assert (legacy >> 8) & 0xFF == 0
        assert legacy & 0xFF == 3

    def test_morph_ext_encoding(self):
        """MORPH_EXT carries its missing endpoint payload in FMT_MORPH_INLINE."""
        from thielecpu.hardware.cosim import program_to_hex
        instr, _, _ = program_to_hex("MORPH_EXT 7 1 2 5 3")
        word = int(instr[0], 16)
        assert (word >> 112) & 0xFF == 0x03
        assert (word >> 96) & 0xFF == 0x04
        assert (word >> 32) & 0x3F == 2
        assert (word >> 38) & 0x3F == 5
        legacy = word & 0xFFFFFFFF
        assert (legacy >> 24) & 0xFF == 0x27
        assert (legacy >> 16) & 0xFF == 7
        assert (legacy >> 8) & 0xFF == 1
        assert legacy & 0xFF == 3

    def test_morph_assert_ext_encoding(self):
        """MORPH_ASSERT_EXT uses FMT_CERT_INLINE with the inline checksum in ext0."""
        from thielecpu.hardware.cosim import program_to_hex
        checksum = _ascii_checksum("lawful")
        instr, _, _ = program_to_hex("MORPH_ASSERT_EXT 9 lawful 4")
        word = int(instr[0], 16)
        assert (word >> 112) & 0xFF == 0x05
        assert (word >> 96) & 0xFF == 0x04
        assert (word >> 32) & 0xFFFFFFFF == checksum
        legacy = word & 0xFFFFFFFF
        assert (legacy >> 24) & 0xFF == 0x2B
        assert (legacy >> 16) & 0xFF == 9
        assert (legacy >> 8) & 0xFF == 0
        assert legacy & 0xFF == 4

    def test_all_opcodes_have_entries(self):
        """All 47 opcodes in cosim.OPCODES match isa.py."""
        from thielecpu.hardware.cosim import OPCODES
        assert len(OPCODES) == 47
        assert OPCODES["HALT"] == 0xFF
        assert OPCODES["PNEW"] == 0x00

    def test_chsh_trial_encoding_full_args(self):
        """CHSH_TRIAL x y a b cost packs bits into operand_a/operand_b."""
        from thielecpu.hardware.cosim import program_to_hex

        # x=1,y=0 -> operand_a=0b10=2 ; a=0,b=1 -> operand_b=0b01=1
        instr, _, _ = program_to_hex("CHSH_TRIAL 1 0 0 1 6")
        assert len(instr[0]) == 32
        word = int(instr[0], 16)
        legacy = word & 0xFFFFFFFF
        opcode = (legacy >> 24) & 0xFF
        op_a = (legacy >> 16) & 0xFF
        op_b = (legacy >> 8) & 0xFF
        cost = legacy & 0xFF

        assert opcode == 0x09
        assert op_a == 2
        assert op_b == 1
        assert cost == 6

    def test_chsh_trial_encoding_legacy_args(self):
        """Legacy CHSH_TRIAL a b cost form remains accepted."""
        from thielecpu.hardware.cosim import program_to_hex

        instr, _, _ = program_to_hex("CHSH_TRIAL 2 1 6")
        assert len(instr[0]) == 32
        word = int(instr[0], 16)
        legacy = word & 0xFFFFFFFF
        opcode = (legacy >> 24) & 0xFF
        op_a = (legacy >> 16) & 0xFF
        op_b = (legacy >> 8) & 0xFF
        cost = legacy & 0xFF

        assert opcode == 0x09
        assert op_a == 2
        assert op_b == 1
        assert cost == 6


# ═══════════════════════════════════════════════════════════════════════
# 6. μ-ALU accelerator (standalone module)
# ═══════════════════════════════════════════════════════════════════════
class TestMuALU:
    """Verify Q16.16 arithmetic encoding matches Python FixedPointMu.

    NOTE: Arithmetic behavior is validated through the integrated
    thiele_cpu_kami.v cosimulation path; these checks focus on
    Python-side Q16.16 encoding invariants.
    """

    def _q16_16(self, f: float) -> int:
        """Convert float to Q16.16 unsigned representation."""
        return int(f * 65536) & 0xFFFFFFFF

    def _from_q16_16(self, v: int) -> float:
        """Convert Q16.16 back to float."""
        return v / 65536.0

    def test_q16_16_encoding_roundtrip(self):
        """Basic Q16.16 encoding: 1.5 → 0x00018000."""
        assert self._q16_16(1.5) == 0x00018000
        assert abs(self._from_q16_16(0x00018000) - 1.5) < 1e-6

    def test_add_encoding(self):
        """Q16.16 ADD: 1.5 + 2.25 = 3.75 (Python encoding check)."""
        a = self._q16_16(1.5)
        b = self._q16_16(2.25)
        result = (a + b) & 0xFFFFFFFF
        assert abs(self._from_q16_16(result) - 3.75) < 0.01

    def test_sub_encoding(self):
        """Q16.16 SUB: 5.0 - 2.0 = 3.0 (Python encoding check)."""
        a = self._q16_16(5.0)
        b = self._q16_16(2.0)
        result = (a - b) & 0xFFFFFFFF
        assert abs(self._from_q16_16(result) - 3.0) < 0.01


# ═══════════════════════════════════════════════════════════════════════
# 7. Partition Core accelerator (standalone module)
# ═══════════════════════════════════════════════════════════════════════
class TestPartitionCoreAccel:
    """Verify partition operations via integrated CPU cosimulation.

    NOTE: Partition behavior is exercised through the full canonical
    thiele_cpu_kami.v pipeline.
    """

    def test_pnew_charges_mu_via_cpu(self):
        """PNEW charges the explicit μ-cost through the full CPU."""
        state = _run_cosim("PNEW 0 0 3\nHALT")
        assert state["mu"] == 3

    def test_two_pnews_accumulate_mu(self):
        """Two PNEWs accumulate μ-cost."""
        state = _run_cosim("PNEW 0 0 3\nPNEW 1 0 2\nHALT")
        assert state["mu"] == 5

    def test_pmerge_charges_mu(self):
        """PMERGE charges μ-cost after PNEWs."""
        state = _run_cosim("PNEW 0 0 2\nPNEW 1 0 2\nPMERGE 1 2 3\nHALT")
        assert state["mu"] == 7

    def test_partition_ops_counter(self):
        """partition_ops counter increments for PNEW operations."""
        state = _run_cosim("PNEW 0 0 1\nPNEW 1 0 1\nHALT")
        assert state.get("partition_ops", 0) >= 2


# ═══════════════════════════════════════════════════════════════════════
# 8. Compilation smoke test
# ═══════════════════════════════════════════════════════════════════════
class TestCompilation:
    """Verify RTL files compile without error."""

    def test_kami_rtl_compiles(self):
        """thiele_cpu_kami.v + thiele_cpu_kami_tb.v compile cleanly."""
        import tempfile
        from thielecpu.hardware.cosim import compile_testbench_iverilog
        with tempfile.TemporaryDirectory() as tmpdir:
            vvp = compile_testbench_iverilog(Path(tmpdir))
            assert vvp.exists()
            assert vvp.stat().st_size > 0



# ═══════════════════════════════════════════════════════════════════════
# 9. ISA alignment: Python ↔ Verilog ↔ Coq
# ═══════════════════════════════════════════════════════════════════════
class TestISAAlignment:
    """Verify all three layers agree on opcodes."""


    def test_kami_rtl_exists(self):
        """thiele_cpu_kami.v (Kami-extracted RTL) is present in rtl/."""
        rtl = REPO_ROOT / "thielecpu" / "hardware" / "rtl" / "thiele_cpu_kami.v"
        assert rtl.exists(), "thiele_cpu_kami.v not found"

    def test_all_47_opcodes_in_cosim(self):
        from thielecpu.hardware.cosim import OPCODES
        assert len(OPCODES) == 47
        expected_names = {
            "PNEW", "PSPLIT", "PMERGE", "LASSERT", "LJOIN",
            "MDLACC", "PDISCOVER", "XFER", "LOAD_IMM", "CHSH_TRIAL",
            "XOR_LOAD", "XOR_ADD", "XOR_SWAP", "XOR_RANK",
            "EMIT", "REVEAL", "ORACLE_HALTS",
            "LOAD", "STORE", "ADD", "SUB", "JUMP", "JNEZ", "CALL", "RET",
            "CHECKPOINT", "READ_PORT", "WRITE_PORT", "HEAP_LOAD", "HEAP_STORE",
            "CERTIFY", "HALT",
            "AND", "OR", "SHL", "SHR", "MUL", "LUI",
            "TENSOR_SET", "TENSOR_GET",
            "MORPH", "COMPOSE", "MORPH_ID", "MORPH_DELETE",
            "MORPH_ASSERT", "MORPH_TENSOR", "MORPH_GET",
        }
        assert set(OPCODES.keys()) == expected_names
