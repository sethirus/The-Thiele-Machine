"""RTL-level tests for categorical MORPH opcodes (plan item 44).

These tests validate that the 7 MORPH categorical opcodes execute correctly
through the Kami-generated Verilog RTL (thiele_cpu_kami.v), exercising:
  - μ-cost charging (plain cost for most, cost+1 for MORPH_ASSERT cert-setter)
  - Register write semantics (new morphism ID written to dst for creating ops)
  - Successful execution and specified MORPH_TENSOR failure
  - Accumulated μ over multi-opcode sequences

The RTL validates preconditions: modules must exist in the partition table
before MORPH/MORPH_ID, and morphisms must be valid in morph_valid_table
before COMPOSE/DELETE/ASSERT/GET. COMPOSE requires the _EXT
(FMT_MORPH_INLINE) encoding. MORPH_TENSOR always faults because represented
module regions overlap, so the kernel tensor product cannot exist.
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


pytestmark = pytest.mark.strict_rtl

# Zero-cost preamble: create two modules and two morphisms so that
# subsequent MORPH opcodes operate on valid state.
# After this preamble: modules {1,2}, morphisms {1: 1→2, 2: 2→1},
# morph_next_id=3, mu=0.
_MORPH_PREAMBLE = (
    "PNEW {1} 0\n"
    "PNEW {2} 0\n"
    "MORPH_EXT 0 1 2 0 0\n"
    "MORPH_EXT 0 2 1 0 0\n"
)

# ─────────────────────────────────────────────────────────────────────────────
# Individual opcode smoke tests
# ─────────────────────────────────────────────────────────────────────────────

class TestMorphRTLSmoke:
    """Each MORPH opcode executes cleanly and charges μ."""

    def test_morph_charges_mu(self):
        """MORPH creates a morphism slot; charges cost μ."""
        state = _run_cosim(_MORPH_PREAMBLE + "MORPH 0 1 3\nHALT")
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
        state = _run_cosim(_MORPH_PREAMBLE + "COMPOSE_EXT 0 1 2 4\nHALT")
        assert not state.get("err"), "COMPOSE set error flag"
        assert state["mu"] == 4

    def test_morph_id_charges_mu(self):
        """MORPH_ID creates an identity morphism; charges cost μ."""
        state = _run_cosim(_MORPH_PREAMBLE + "MORPH_ID 0 1 2\nHALT")
        assert not state.get("err"), "MORPH_ID set error flag"
        assert state["mu"] == 2

    def test_morph_delete_charges_mu(self):
        """MORPH_DELETE removes a morphism; charges cost μ."""
        state = _run_cosim(_MORPH_PREAMBLE + "MORPH_DELETE 1 0 3\nHALT")
        assert not state.get("err"), "MORPH_DELETE set error flag"
        assert state["mu"] == 3

    def test_morph_assert_charges_cost_plus_one(self):
        """MORPH_ASSERT is a cert-setter: μ-cost = cost + 1."""
        state = _run_cosim(_MORPH_PREAMBLE + "MORPH_ASSERT 1 0 4\nHALT")
        assert not state.get("err"), "MORPH_ASSERT set error flag"
        assert state["mu"] == 5  # cost=4 → charges 4+1=5

    def test_morph_tensor_charges_mu(self):
        """The unavailable tensor product faults and still charges its cost."""
        state = _run_cosim(_MORPH_PREAMBLE + "MORPH_TENSOR_EXT 0 1 2 3\nHALT")
        assert state["err"]
        assert state["error_code"] == 0xBADC0003
        assert state["mu"] == 3

    def test_morph_get_charges_mu(self):
        """MORPH_GET reads a morphism field; charges cost μ."""
        state = _run_cosim(_MORPH_PREAMBLE + "MORPH_GET 0 1 2\nHALT")
        assert not state.get("err"), "MORPH_GET set error flag"
        assert state["mu"] == 2


# ─────────────────────────────────────────────────────────────────────────────
# Register-write semantics
# ─────────────────────────────────────────────────────────────────────────────

class TestMorphRTLRegisterWrite:
    """Morphism-creating opcodes write new morphism ID to dst register."""

    _SENTINEL = 42  # value pre-loaded into dst to detect writes

    def _verify_writes_to_dst(self, opcode_line: str, dst_reg: int) -> None:
        # Pre-load dst with a sentinel value, then execute the opcode.
        # The RTL writes the new morphism/field ID to dst on success.
        program = f"{_MORPH_PREAMBLE}LOAD_IMM {dst_reg} {self._SENTINEL} 0\n{opcode_line}\nHALT"
        state = _run_cosim(program)
        assert not state.get("err"), f"{opcode_line!r}: set error flag"
        assert state["regs"][dst_reg] != self._SENTINEL, (
            f"{opcode_line!r}: expected regs[{dst_reg}] to be written, "
            f"but it still holds sentinel {self._SENTINEL}"
        )

    def test_morph_writes_to_dst(self):
        """MORPH writes new morphism ID to destination register."""
        self._verify_writes_to_dst("MORPH 0 1 1", 0)

    def test_compose_writes_to_dst(self):
        """COMPOSE writes new morphism ID to destination register."""
        self._verify_writes_to_dst("COMPOSE_EXT 0 1 2 1", 0)

    def test_morph_id_writes_to_dst(self):
        """MORPH_ID writes new morphism ID to destination register."""
        self._verify_writes_to_dst("MORPH_ID 0 1 1", 0)

    def test_morph_tensor_preserves_dst_on_fault(self):
        state = _run_cosim(_MORPH_PREAMBLE +
                           f"LOAD_IMM 0 {self._SENTINEL} 0\nMORPH_TENSOR_EXT 0 1 2 1\nHALT")
        assert state["err"]
        assert state["error_code"] == 0xBADC0003
        assert state["regs"][0] == self._SENTINEL
        assert len(state["graph"]["morphisms"]) == 2

    def test_morph_get_writes_to_dst(self):
        """MORPH_GET writes field value to destination register."""
        self._verify_writes_to_dst("MORPH_GET 0 1 1", 0)

    def test_morph_delete_does_not_touch_registers(self):
        """MORPH_DELETE has no destination register — pre-loaded value preserved."""
        state = _run_cosim(_MORPH_PREAMBLE + "LOAD_IMM 0 99 0\nMORPH_DELETE 1 0 1\nHALT")
        # MORPH_DELETE encodes morph_id in op_a; no dst write.
        # The register should retain its LOAD_IMM value.
        assert state["regs"][0] == 99, (
            f"MORPH_DELETE unexpectedly modified regs[0]: {state['regs'][0]}"
        )

    def test_morph_assert_does_not_touch_dst_register(self):
        """MORPH_ASSERT is a property-assertion; it does not write a result register."""
        state = _run_cosim(_MORPH_PREAMBLE + "LOAD_IMM 0 77 0\nMORPH_ASSERT 1 0 1\nHALT")
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
            _MORPH_PREAMBLE +
            "MORPH 0 1 2\n"
            "COMPOSE_EXT 1 1 2 3\n"
            "MORPH_ID 2 1 1\n"
            "HALT"
        )
        assert not state.get("err")
        assert state["mu"] == 6  # 2 + 3 + 1

    def test_morph_assert_inflates_cost(self):
        """MORPH_ASSERT (cert-setter) adds 1 extra μ on top of cost."""
        state = _run_cosim(
            _MORPH_PREAMBLE +
            "MORPH 0 1 2\n"          # cost=2, charges 2
            "MORPH_ASSERT 1 0 3\n"   # cost=3, charges 4 (cert-setter)
            "HALT"
        )
        assert state["mu"] == 6  # 2 + (3+1) = 6

    def test_full_morph_sequence_accumulates(self):
        """All 7 MORPH opcodes in sequence — μ is their sum (with MORPH_ASSERT +1)."""
        state = _run_cosim(
            _MORPH_PREAMBLE +
            "MORPH 0 1 1\n"              # +1, creates morph3
            "COMPOSE_EXT 0 1 2 1\n"      # +1, creates morph4
            "MORPH_ID 0 1 1\n"           # +1, creates morph5
            "MORPH_DELETE 3 0 1\n"        # +1, deletes morph3
            "MORPH_ASSERT 1 0 1\n"        # +2 (cert-setter)
            "MORPH_GET 0 1 1\n"           # +1
            "MORPH_TENSOR_EXT 0 1 2 1\n"  # +1, specified fault
            "HALT"
        )
        assert state["err"]
        assert state["error_code"] == 0xBADC0003
        assert state["mu"] == 8  # 1+1+1+1+2+1+1

    def test_morph_interleaved_with_pnew(self):
        """MORPH opcodes accumulate correctly when interleaved with partition ops."""
        state = _run_cosim(
            "PNEW {1} 2\n"           # partition op, +2
            "PNEW {2} 0\n"           # partition op, +0 (module setup)
            "MORPH_EXT 0 1 2 0 0\n"  # setup morphism, +0
            "MORPH 0 1 3\n"          # morph op, +3
            "PNEW {3} 1\n"           # partition op, +1
            "MORPH_ID 0 1 2\n"       # morph op, +2
            "HALT"
        )
        assert state["mu"] == 8  # 2 + 0 + 0 + 3 + 1 + 2

    def test_zero_cost_morph_opcodes(self):
        """MORPH opcodes with cost=0 do not advance μ."""
        baseline = _run_cosim(_MORPH_PREAMBLE + "HALT")
        state = _run_cosim(
            _MORPH_PREAMBLE +
            "MORPH 0 1 0\n"
            "COMPOSE_EXT 0 1 2 0\n"
            "MORPH_ID 0 1 0\n"
            "MORPH_DELETE 1 0 0\n"
            "MORPH_TENSOR_EXT 0 1 2 0\n"
            "MORPH_GET 0 1 0\n"
            "HALT"
        )
        assert state["mu"] == baseline["mu"]

    def test_morph_assert_zero_cost_still_charges_one(self):
        """MORPH_ASSERT with cost=0 still charges μ=1 (cert-setter minimum)."""
        state = _run_cosim(_MORPH_PREAMBLE + "MORPH_ASSERT 1 0 0\nHALT")
        assert state["mu"] == 1  # S(0) = 1


def _coupling_memory(base, pairs):
    words = [len(pairs)] + [cell for pair in pairs for cell in pair]
    return "".join(f"INIT_MEM {base + offset} {word}\n" for offset, word in enumerate(words))


def _pairs(state, morph_id):
    return next(m["coupling"]["pairs"] for m in state["graph"]["morphisms"] if m["id"] == morph_id)


class TestMorphRTLCouplingData:
    def test_morph_reads_upper_half_memory(self):
        program = _coupling_memory(80, [(1, 2)])
        state = _run_cosim(program + "PNEW {1} 0\nPNEW {2} 0\nMORPH_EXT 0 1 2 80 0\nHALT")
        assert not state["err"]
        assert _pairs(state, 1) == [[1, 2]]

    def test_empty_morph_preserves_existing_pairs(self):
        program = _coupling_memory(80, [(1, 2)])
        state = _run_cosim(program + "PNEW {1} 0\nPNEW {2} 0\nMORPH_EXT 0 1 2 80 0\nMORPH_EXT 0 1 2 0 0\nHALT")
        assert not state["err"]
        assert _pairs(state, 1) == [[1, 2]]
        assert _pairs(state, 2) == []

    def test_compose_joins_nonempty_pairs(self):
        program = _coupling_memory(80, [(1, 2)]) + _coupling_memory(90, [(2, 3)])
        state = _run_cosim(program + "PNEW {1} 0\nPNEW {2} 0\nPNEW {3} 0\nMORPH_EXT 0 1 2 80 0\nMORPH_EXT 0 2 3 90 0\nCOMPOSE_EXT 0 1 2 0\nHALT")
        assert not state["err"]
        assert _pairs(state, 3) == [[1, 3]]

    @pytest.mark.parametrize("empty_first", [True, False])
    def test_compose_empty_relation(self, empty_first):
        memory = _coupling_memory(80, [(1, 2)]) + _coupling_memory(90, [(2, 3)])
        first, second = (0, 90) if empty_first else (80, 0)
        state = _run_cosim(memory + f"PNEW {{1}} 0\nPNEW {{2}} 0\nPNEW {{3}} 0\nMORPH_EXT 0 1 2 {first} 0\nMORPH_EXT 0 2 3 {second} 0\nCOMPOSE_EXT 0 1 2 0\nHALT")
        assert not state["err"]
        assert _pairs(state, 3) == []

    def test_compose_identity_copies_pairs(self):
        program = _coupling_memory(80, [(1, 2)])
        state = _run_cosim(program + "PNEW {1} 0\nPNEW {2} 0\nMORPH_ID 0 1 0\nMORPH_EXT 0 1 2 80 0\nCOMPOSE_EXT 0 1 2 0\nHALT")
        assert not state["err"]
        assert _pairs(state, 3) == [[1, 2]]

    def test_tensor_fault_preserves_both_pair_ranges(self):
        program = _coupling_memory(80, [(1, 2)]) + _coupling_memory(90, [(3, 4)])
        state = _run_cosim(program + "PNEW {1} 0\nPNEW {2} 0\nPNEW {3} 0\nPNEW {4} 0\nMORPH_EXT 0 1 2 80 0\nMORPH_EXT 0 3 4 90 0\nMORPH_TENSOR_EXT 0 1 2 0\nHALT")
        assert state["err"]
        assert state["error_code"] == 0xBADC0003
        assert len(state["graph"]["morphisms"]) == 2
        assert _pairs(state, 1) == [[1, 2]]
        assert _pairs(state, 2) == [[3, 4]]

    def test_last_pair_slot_and_empty_allocation(self):
        pairs = [(1, i) for i in range(16)]
        program = _coupling_memory(64, pairs)
        state = _run_cosim(program + "PNEW {1} 0\nPNEW {2} 0\nMORPH_EXT 0 1 2 64 0\nMORPH_EXT 0 1 2 0 0\nHALT")
        assert not state["err"]
        assert _pairs(state, 1) == [list(pair) for pair in pairs]
        assert _pairs(state, 2) == []

    def test_oversized_coupling_traps(self):
        program = _coupling_memory(64, [(1, i) for i in range(17)])
        state = _run_cosim(program + "PNEW {1} 0\nPNEW {2} 0\nMORPH_EXT 0 1 2 64 0\nHALT")
        assert state["err"]

    def test_copy_overflow_preserves_source_pairs(self):
        pairs = [(1, i) for i in range(9)]
        program = _coupling_memory(64, pairs)
        state = _run_cosim(program + "PNEW {1} 0\nPNEW {2} 0\nMORPH_ID 0 1 0\nMORPH_EXT 0 1 2 64 0\nCOMPOSE_EXT 0 1 2 0\nHALT")
        assert state["err"]
        assert _pairs(state, 2) == [list(pair) for pair in pairs]

    def test_first_descriptor_count_and_identity_remain_distinct(self):
        program = _coupling_memory(80, [(1, 2)])
        state = _run_cosim(program + "PNEW {1} 0\nPNEW {2} 0\nMORPH_EXT 0 1 2 80 0\nMORPH_ID 0 1 0\nMORPH_GET_EXT 4 1 2 0\nMORPH_GET_EXT 5 2 2 0\nHALT")
        assert not state["err"]
        assert state["regs"][4] == 1
        assert state["regs"][5] == 0
        assert _pairs(state, 2) == []

    def test_join_uses_last_pair_slot(self):
        first = [(i, i + 20) for i in range(14)]
        program = _coupling_memory(64, first) + _coupling_memory(100, [(20, 40)])
        state = _run_cosim(program + "PNEW {50} 0\nPNEW {50} 0\nPNEW {50} 0\nMORPH_EXT 0 1 2 64 0\nMORPH_EXT 0 2 3 100 0\nCOMPOSE_EXT 0 1 2 0\nHALT")
        assert not state["err"]
        assert _pairs(state, 3) == [[0, 40]]
        assert _pairs(state, 1) == [list(pair) for pair in first]


class TestPnewRTLRegionLength:
    @pytest.mark.parametrize("start", [0, 20])
    @pytest.mark.parametrize("address, expected_error", [(2, False), (3, True)])
    def test_partition_wall_uses_encoded_length(self, start, address, expected_error):
        """The hardware stores a local range of length three, regardless of start."""
        region = ",".join(str(start + i) for i in range(3))
        state = _run_cosim(
            f"INIT_ACTIVE_MODULE 1\nINIT_MEM 2 42\n"
            f"PNEW {{{region}}} 0\nLOAD_IMM 1 {address} 0\nLOAD 2 1 0\nHALT"
        )
        assert bool(state["err"]) == expected_error
        if not expected_error:
            assert state["regs"][2] == 42


class TestRTLCouplingNormalization:
    def test_morph_keeps_last_occurrence_and_reclaims_slots(self):
        pairs = [(1, 2), (3, 4), (1, 2)]
        program = _coupling_memory(64, pairs) + _coupling_memory(80, [(5, i) for i in range(14)])
        state = _run_cosim(program + "PNEW {1} 0\nPNEW {2} 0\nMORPH_EXT 0 1 2 64 0\nMORPH_EXT 0 1 2 80 0\nMORPH_GET_EXT 4 1 2 0\nHALT")
        assert not state["err"]
        assert _pairs(state, 1) == [[3, 4], [1, 2]]
        assert state["regs"][4] == 2
        assert len(_pairs(state, 2)) == 14

    def test_compose_normalizes_duplicate_join_results(self):
        program = _coupling_memory(64, [(1, 2), (1, 3)]) + _coupling_memory(80, [(2, 4), (3, 4)])
        state = _run_cosim(program + "PNEW {1} 0\nPNEW {2} 0\nPNEW {3} 0\nMORPH_EXT 0 1 2 64 0\nMORPH_EXT 0 2 3 80 0\nCOMPOSE_EXT 0 1 2 0\nHALT")
        assert not state["err"]
        assert _pairs(state, 3) == [[1, 4]]
        assert _pairs(state, 1) == [[1, 2], [1, 3]]

    def test_tensor_fault_preserves_overlapping_pair_ranges(self):
        program = _coupling_memory(64, [(1, 2), (3, 4)]) + _coupling_memory(80, [(1, 2), (5, 6)])
        state = _run_cosim(program + "PNEW {1} 0\nPNEW {2} 0\nPNEW {3} 0\nPNEW {4} 0\nMORPH_EXT 0 1 2 64 0\nMORPH_EXT 0 3 4 80 0\nMORPH_TENSOR_EXT 0 1 2 0\nHALT")
        assert state["err"]
        assert state["error_code"] == 0xBADC0003
        assert len(state["graph"]["morphisms"]) == 2
        assert _pairs(state, 1) == [[1, 2], [3, 4]]
        assert _pairs(state, 2) == [[1, 2], [5, 6]]
