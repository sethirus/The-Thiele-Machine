"""RTL-level tests for categorical MORPH opcodes (plan item 44).

These tests validate that the 7 MORPH categorical opcodes execute correctly
through the Kami-generated Verilog RTL (thiele_cpu_kami.v), exercising:
  - μ-cost charging (plain cost for most, cost+1 for MORPH_ASSERT cert-setter)
  - Register write semantics (0 written to dst for morphism-creating ops)
  - Error-free execution
  - Accumulated μ over multi-opcode sequences
"""

from __future__ import annotations

from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent


def _run_cosim(program: str):
    from thielecpu.hardware.cosim import run_verilog

    result = run_verilog(program, timeout=30)
    assert result is not None, "run_verilog returned None"
    return result


# ─────────────────────────────────────────────────────────────────────────────
# Individual opcode smoke tests
# ─────────────────────────────────────────────────────────────────────────────

class TestMorphRTLSmoke:
    """Each MORPH opcode executes cleanly and charges μ."""

    def test_morph_charges_mu(self):
        """MORPH creates a morphism slot; charges cost μ."""
        state = _run_cosim("MORPH 0 1 3\nHALT")
        assert not state.get("err"), "MORPH set error flag"
        assert state["mu"] == 3

    @pytest.mark.strict_rtl
    def test_morph_graph_surface_is_exposed(self):
        """RTL cosim exposes the bounded morphism table as graph.morphisms."""
        state = _run_cosim("PNEW {1} 1\nPNEW {2} 1\nMORPH_EXT 5 1 2 0 2\nHALT")
        assert not state.get("err"), "MORPH set error flag"
        graph = state["graph"]
        assert graph["next_id"] == 3
        assert graph["next_morph_id"] == 2
        assert graph["modules"] == [
            {"id": 1, "region": [1]},
            {"id": 2, "region": [2]},
        ]
        assert graph["morphisms"] == [
            {
                "id": 1,
                "source": 1,
                "target": 2,
                "is_identity": 0,
                "coupling": {"label": "empty", "pairs": []},
            },
        ]

    def test_compose_charges_mu(self):
        """COMPOSE composes two morphisms; charges cost μ."""
        state = _run_cosim("COMPOSE 0 1 4\nHALT")
        assert not state.get("err"), "COMPOSE set error flag"
        assert state["mu"] == 4

    def test_morph_id_charges_mu(self):
        """MORPH_ID creates an identity morphism; charges cost μ."""
        state = _run_cosim("MORPH_ID 0 0 2\nHALT")
        assert not state.get("err"), "MORPH_ID set error flag"
        assert state["mu"] == 2

    def test_morph_delete_charges_mu(self):
        """MORPH_DELETE removes a morphism; charges cost μ."""
        state = _run_cosim("MORPH_DELETE 0 0 3\nHALT")
        assert not state.get("err"), "MORPH_DELETE set error flag"
        assert state["mu"] == 3

    def test_morph_assert_charges_cost_plus_one(self):
        """MORPH_ASSERT is a cert-setter: μ-cost = cost + 1."""
        state = _run_cosim("MORPH_ASSERT 0 0 4\nHALT")
        assert not state.get("err"), "MORPH_ASSERT set error flag"
        assert state["mu"] == 5  # cost=4 → charges 4+1=5

    def test_morph_tensor_charges_mu(self):
        """MORPH_TENSOR computes the tensor product of two morphisms; charges cost μ."""
        state = _run_cosim("MORPH_TENSOR 0 1 3\nHALT")
        assert not state.get("err"), "MORPH_TENSOR set error flag"
        assert state["mu"] == 3

    def test_morph_get_charges_mu(self):
        """MORPH_GET reads a morphism field; charges cost μ."""
        state = _run_cosim("MORPH_GET 0 1 2\nHALT")
        assert not state.get("err"), "MORPH_GET set error flag"
        assert state["mu"] == 2


# ─────────────────────────────────────────────────────────────────────────────
# Register-write semantics
# ─────────────────────────────────────────────────────────────────────────────

class TestMorphRTLRegisterWrite:
    """Morphism-creating opcodes write 0 to dst register (graph managed in SW)."""

    def _verify_writes_zero_to_dst(self, opcode_line: str, dst_reg: int) -> None:
        # Pre-load dst with a non-zero value, then execute the opcode.
        program = f"LOAD_IMM {dst_reg} 42 0\n{opcode_line}\nHALT"
        state = _run_cosim(program)
        assert state["regs"][dst_reg] == 0, (
            f"{opcode_line!r}: expected regs[{dst_reg}]=0 after write, "
            f"got {state['regs'][dst_reg]}"
        )

    def test_morph_writes_zero_to_dst(self):
        """MORPH writes 0 to destination register."""
        self._verify_writes_zero_to_dst("MORPH 0 1 1", 0)

    def test_compose_writes_zero_to_dst(self):
        """COMPOSE writes 0 to destination register."""
        self._verify_writes_zero_to_dst("COMPOSE 0 1 1", 0)

    def test_morph_id_writes_zero_to_dst(self):
        """MORPH_ID writes 0 to destination register."""
        self._verify_writes_zero_to_dst("MORPH_ID 0 1 1", 0)

    def test_morph_tensor_writes_zero_to_dst(self):
        """MORPH_TENSOR writes 0 to destination register."""
        self._verify_writes_zero_to_dst("MORPH_TENSOR 0 1 1", 0)

    def test_morph_get_writes_zero_to_dst(self):
        """MORPH_GET writes 0 to destination register."""
        self._verify_writes_zero_to_dst("MORPH_GET 0 1 1", 0)

    def test_morph_delete_does_not_touch_registers(self):
        """MORPH_DELETE has no destination register — pre-loaded value preserved."""
        state = _run_cosim("LOAD_IMM 0 99 0\nMORPH_DELETE 0 0 1\nHALT")
        # MORPH_DELETE encodes morph_id in op_a; no dst write.
        # The register should retain its LOAD_IMM value.
        assert state["regs"][0] == 99, (
            f"MORPH_DELETE unexpectedly modified regs[0]: {state['regs'][0]}"
        )

    def test_morph_assert_does_not_touch_dst_register(self):
        """MORPH_ASSERT is a property-assertion; it does not write a result register."""
        state = _run_cosim("LOAD_IMM 0 77 0\nMORPH_ASSERT 0 0 1\nHALT")
        assert state["regs"][0] == 77, (
            f"MORPH_ASSERT unexpectedly modified regs[0]: {state['regs'][0]}"
        )


# ─────────────────────────────────────────────────────────────────────────────
# μ accumulation across sequences
# ─────────────────────────────────────────────────────────────────────────────

class TestMorphRTLMuAccumulation:
    """μ-cost accumulates correctly across mixed MORPH opcode sequences."""

    def test_three_morphs_accumulate(self):
        """Three standard MORPH opcodes accumulate μ = sum of costs."""
        state = _run_cosim(
            "MORPH 0 0 2\n"
            "COMPOSE 1 0 3\n"
            "MORPH_ID 2 0 1\n"
            "HALT"
        )
        assert not state.get("err")
        assert state["mu"] == 6  # 2 + 3 + 1

    def test_morph_assert_inflates_cost(self):
        """MORPH_ASSERT (cert-setter) adds 1 extra μ on top of cost."""
        state = _run_cosim(
            "MORPH 0 0 2\n"     # cost=2, charges 2
            "MORPH_ASSERT 0 0 3\n"  # cost=3, charges 4 (cert-setter)
            "HALT"
        )
        assert state["mu"] == 6  # 2 + (3+1) = 6

    def test_full_morph_sequence_accumulates(self):
        """All 7 MORPH opcodes in sequence — μ is their sum (with MORPH_ASSERT +1)."""
        state = _run_cosim(
            "MORPH 0 1 1\n"          # +1
            "COMPOSE 0 1 1\n"        # +1
            "MORPH_ID 0 0 1\n"       # +1
            "MORPH_DELETE 0 0 1\n"   # +1
            "MORPH_ASSERT 0 0 1\n"   # +2 (cert-setter)
            "MORPH_TENSOR 0 1 1\n"   # +1
            "MORPH_GET 0 1 1\n"      # +1
            "HALT"
        )
        assert not state.get("err")
        assert state["mu"] == 8  # 1+1+1+1+2+1+1

    def test_morph_interleaved_with_pnew(self):
        """MORPH opcodes accumulate correctly when interleaved with partition ops."""
        state = _run_cosim(
            "PNEW 0 0 2\n"    # partition op, +2
            "MORPH 0 0 3\n"   # morph op, +3
            "PNEW 1 0 1\n"    # partition op, +1
            "MORPH_ID 0 0 2\n"  # morph op, +2
            "HALT"
        )
        assert state["mu"] == 8  # 2 + 3 + 1 + 2

    def test_zero_cost_morph_opcodes(self):
        """MORPH opcodes with cost=0 do not advance μ."""
        baseline = _run_cosim("HALT")
        state = _run_cosim(
            "MORPH 0 0 0\n"
            "COMPOSE 0 0 0\n"
            "MORPH_ID 0 0 0\n"
            "MORPH_DELETE 0 0 0\n"
            "MORPH_TENSOR 0 0 0\n"
            "MORPH_GET 0 0 0\n"
            "HALT"
        )
        assert state["mu"] == baseline["mu"]

    def test_morph_assert_zero_cost_still_charges_one(self):
        """MORPH_ASSERT with cost=0 still charges μ=1 (cert-setter minimum)."""
        state = _run_cosim("MORPH_ASSERT 0 0 0\nHALT")
        assert state["mu"] == 1  # S(0) = 1
