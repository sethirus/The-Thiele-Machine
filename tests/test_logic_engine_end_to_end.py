"""End-to-end Logic Engine tests.

Tests the full certificate pipeline across layers:
    - OCaml/Python VM: DIMACS formula -> SAT model plus countermodel / LRAT proof -> LASSERT -> verified
  - RTL cosim: integer-encoded LASSERT -> logic bridge -> verified
  - Logic gate key unlock: LASSERT success -> REVEAL permitted

Cross-layer note: RTL encodes LASSERT operands as integers (no string formulas
in 32-bit instruction words). The OCaml VM uses full DIMACS/LRAT string
certificates. LogicEngineEquivalence.v proves these are equivalent given a
correct oracle. These tests verify each layer independently and confirm
matching observable state (mu, err, PC advancement).
"""

import pytest

pytestmark = pytest.mark.strict_rtl

from thielecpu.vm import VMState, vm_run


def _rtl_lassert_sat_program(cost: int) -> list[str]:
    """Memory-backed SAT package for formula (x1) with a falsifying countermodel."""
    return [
        "INIT_MEM 16 2",    # two literal words: +x1, end-of-clause
        "INIT_MEM 17 1",    # num_vars
        "INIT_MEM 18 1",    # num_clauses
        "INIT_MEM 19 1",    # literal +x1
        "INIT_MEM 20 0",    # end-of-clause
        "INIT_MEM 97 1",    # model at cbase+1: x1=true
        "INIT_MEM 98 0",    # countermodel at cbase+nvars+1: x1=false
        "LOAD_IMM 28 16 0",
        "LOAD_IMM 29 96 0",
        f"LASSERT 28 29 1 2 {cost}",
    ]


# ---------------------------------------------------------------------------
# M6.1: LASSERT SAT -- DIMACS formula with valid model
# ---------------------------------------------------------------------------

class TestLassertSatDimacsToRtl:
    """Test LASSERT with a valid SAT witness package through OCaml VM and RTL."""

    def test_ocaml_vm_lassert_sat_valid_model(self):
        """OCaml VM: LASSERT SAT accepts a valid model-plus-countermodel package."""
        s0 = VMState.default()
        program = [
            {"op": "pnew", "region": [0, 256], "cost": 1},
            {"op": "lassert", "module": 0,
             "formula": "p_cnf_2_1__1_2_0",
             "cert_type": "sat", "cert": "v_1_-2_0", "countermodel": "v_-1_-2_0",
             "cost": 1},
            {"op": "halt", "cost": 0},
        ]
        result = vm_run(s0, program, max_steps=10)
        assert result.vm_mu >= 2, "mu should include PNEW(1) + LASSERT(1)"
        assert result.vm_err is False, "Valid witness package should pass"
        assert result.vm_pc >= 2, "PC should advance past LASSERT"

    def test_ocaml_vm_lassert_sat_invalid_model(self):
        """OCaml VM: LASSERT with invalid SAT model sets error."""
        s0 = VMState.default()
        # Formula: (x1 OR x2), Model: x1=false, x2=false -- doesn't satisfy
        program = [
            {"op": "pnew", "region": [0, 256], "cost": 1},
            {"op": "lassert", "module": 0,
             "formula": "p_cnf_2_1__1_2_0",
             "cert_type": "sat", "cert": "v_-1_-2_0", "countermodel": "v_-1_-2_0",
             "cost": 1},
            {"op": "halt", "cost": 0},
        ]
        result = vm_run(s0, program, max_steps=10)
        assert result.vm_err is True, "Invalid SAT model should set error"
        assert result.vm_mu >= 2

    def test_rtl_lassert_sat(self):
        """RTL: LASSERT SAT path — on-chip FSM verifies a trivial formula.

        Registers 28/29 point to the binary formula and dual witness blocks.
        Formula is (x1), model sets x1=true, countermodel sets x1=false.
        """
        from thielecpu.hardware.cosim import run_verilog

        program = [
            "INIT_LOGIC_ACC 0xCAFEEACE",
            "PNEW {0,256} 1",
            *_rtl_lassert_sat_program(2),
            "HALT 0",
        ]
        state = run_verilog(program)
        assert state["status"] == 2  # halted — SAT path succeeded
        assert state["mu"] >= 1 + (2 * 8 + 3), "mu should include PNEW + LASSERT"

    def test_rtl_lassert_unsat(self):
        """RTL: LASSERT UNSAT path — immediate error trap.

        op_a=2, bit 5=0 → kind=UNSAT. RTL immediately sets err=true,
        error_code=ERR_LOGIC, PC→trap vector. Status=3 (error, not halted).
        """
        from thielecpu.hardware.cosim import run_verilog

        program = [
            "INIT_LOGIC_ACC 0xCAFEEACE",
            "PNEW {0,256} 1",
            "LASSERT 2 9 0 1 2",  # freg=2, creg=9, kind=0 (UNSAT), flen=1, cost=2 → immediate trap
            "HALT 0",
        ]
        state = run_verilog(program)
        assert state["status"] == 3  # err trap (not halted)
        assert state["err"] is True
        assert state["mu"] >= 2


# ---------------------------------------------------------------------------
# M6.2: LASSERT UNSAT -- always latches error per Coq spec
# ---------------------------------------------------------------------------

class TestLassertUnsatDimacsToRtl:
    """Test LASSERT with UNSAT certificates."""

    def test_ocaml_vm_lassert_unsat_valid_proof(self):
        """OCaml VM: LASSERT UNSAT always latches error even with valid proof."""
        s0 = VMState.default()
        program = [
            {"op": "pnew", "region": [0, 256], "cost": 1},
            {"op": "lassert", "module": 0,
             "formula": "p_cnf_1_1__1_0",
             "cert_type": "unsat", "cert": "1_1_0_0",
             "cost": 1},
            {"op": "halt", "cost": 0},
        ]
        result = vm_run(s0, program, max_steps=10)
        # Per Coq spec: ALL UNSAT paths latch error regardless of proof validity
        assert result.vm_err is True, "UNSAT always latches error"
        assert result.vm_mu >= 2

    def test_ocaml_vm_lassert_unsat_invalid_proof(self):
        """OCaml VM: LASSERT UNSAT with invalid proof also latches error."""
        s0 = VMState.default()
        program = [
            {"op": "pnew", "region": [0, 256], "cost": 1},
            {"op": "lassert", "module": 0,
             "formula": "p_cnf_1_1__1_0",
             "cert_type": "unsat", "cert": "garbage",
             "cost": 1},
            {"op": "halt", "cost": 0},
        ]
        result = vm_run(s0, program, max_steps=10)
        assert result.vm_err is True, "UNSAT with invalid proof latches error"
        assert result.vm_mu >= 2


# ---------------------------------------------------------------------------
# M6.3: Logic gate key unlock -- LASSERT success enables REVEAL
# ---------------------------------------------------------------------------

class TestLogicGateUnlockFullPipeline:
    """Verify logic gate key mechanism across layers."""

    def test_python_vm_logic_acc_field_exists(self):
        """Python VM: vm_logic_acc field exists and defaults to 0."""
        import dataclasses
        state = VMState.default()
        assert state.vm_logic_acc == 0, "logic_acc starts at 0"

        # Simulate setting the logic gate key
        state_with_key = dataclasses.replace(state, vm_logic_acc=0xCAFEEACE)
        assert state_with_key.vm_logic_acc == 0xCAFEEACE

    def test_rtl_reveal_requires_logic_gate_key(self):
        """RTL: REVEAL succeeds only when logic_acc == 0xCAFEEACE."""
        from thielecpu.hardware.cosim import run_verilog

        # With logic gate key: REVEAL should succeed
        program_with_key = [
            "INIT_LOGIC_ACC 0xCAFEEACE",
            "PNEW {0,256} 1",
            "REVEAL 0 1 0",    # index=0, bits=1, cost=0
            "HALT 0",
        ]
        state = run_verilog(program_with_key)
        assert state["status"] == 2  # halted

    def test_rtl_reveal_without_key_triggers_error(self):
        """RTL: REVEAL without logic gate key triggers ERR_LOGIC."""
        from thielecpu.hardware.cosim import run_verilog

        # Without logic gate key: should trigger logic error -> trap
        program_no_key = [
            "PNEW {0,256} 1",
            "REVEAL 0 1 0",    # index=0, bits=1, cost=0
            "HALT 0",
        ]
        state = run_verilog(program_no_key)
        # Should trap to error vector or set error code
        assert state.get("error_code") == 0xC43471A1 or state.get("err") or state["pc"] != 3

    def test_rtl_lassert_then_reveal_pipeline(self):
        """RTL: LASSERT SAT → REVEAL — full pipeline.

        LASSERT SAT succeeds via on-chip FSM with trivial formula, then
        REVEAL executes. Both charge mu.
        """
        from thielecpu.hardware.cosim import run_verilog

        program = [
            "PNEW {0,256} 1",
            *_rtl_lassert_sat_program(2),
            "REVEAL 0 1 0",    # index=0, bits=1, cost=0
            "HALT 0",
        ]
        state = run_verilog(program)
        assert state["status"] == 2  # halted
        assert state["mu"] >= 1 + (2 * 8 + 3) + 2, (
            "mu should include PNEW + LASSERT + REVEAL"
        )

    def test_mu_isomorphism_lassert(self):
        """Both OCaml VM and RTL charge mu for LASSERT."""
        from thielecpu.hardware.cosim import run_verilog

        # OCaml VM side
        s0 = VMState.default()
        py_program = [
            {"op": "pnew", "region": [0, 256], "cost": 1},
            {"op": "lassert", "module": 0,
             "formula": "p_cnf_2_1__1_2_0",
             "cert_type": "sat", "cert": "v_1_-2_0", "countermodel": "v_-1_-2_0",
             "cost": 5},
            {"op": "halt", "cost": 0},
        ]
        py_result = vm_run(s0, py_program, max_steps=10)
        assert py_result.vm_mu >= 6, "OCaml VM should charge PNEW(1) + LASSERT(5)"

        # RTL side — use SAT path with trivial formula
        rtl_program = [
            "INIT_LOGIC_ACC 0xCAFEEACE",
            "PNEW {0,256} 1",
            *_rtl_lassert_sat_program(5),
            "HALT 0",
        ]
        rtl_state = run_verilog(rtl_program)
        assert rtl_state["mu"] >= 1 + (2 * 8 + 6), (
            "RTL should charge PNEW plus full LASSERT formula cost"
        )


# ---------------------------------------------------------------------------
# LJOIN end-to-end tests
# ---------------------------------------------------------------------------

class TestLjoinEndToEnd:
    """Test LJOIN across layers."""

    def test_ocaml_vm_ljoin_equal_certs(self):
        """OCaml VM: LJOIN with equal certificates succeeds."""
        s0 = VMState.default()
        program = [
            {"op": "pnew", "region": [0, 256], "cost": 1},
            {"op": "ljoin", "cert1": "abc", "cert2": "abc", "cost": 3},
            {"op": "halt", "cost": 0},
        ]
        result = vm_run(s0, program, max_steps=10)
        assert result.vm_err is False, "Equal certs should not error"
        assert result.vm_mu >= 4  # PNEW(1) + LJOIN(3)

    def test_ocaml_vm_ljoin_unequal_certs(self):
        """OCaml VM: LJOIN with unequal certificates does not set error.

        Per coq/kernel/foundation/VMStep.v step_ljoin proof, LJOIN never sets vm_err —
        it only advances the program counter regardless of cert equality.
        """
        s0 = VMState.default()
        program = [
            {"op": "pnew", "region": [0, 256], "cost": 1},
            {"op": "ljoin", "cert1": "abc", "cert2": "xyz", "cost": 3},
            {"op": "halt", "cost": 0},
        ]
        result = vm_run(s0, program, max_steps=10)
        assert result.vm_err is False, "LJOIN never sets vm_err (proven in VMStep.v)"
        assert result.vm_mu >= 4

    def test_rtl_ljoin(self):
        """RTL: LJOIN with deterministic bridge."""
        from thielecpu.hardware.cosim import run_verilog

        program = [
            "INIT_LOGIC_ACC 0xCAFEEACE",
            "PNEW {0,256} 1",
            "LJOIN 5 5 3",    # Same operands -> should match
            "HALT 0",
        ]
        state = run_verilog(program)
        assert state["status"] == 2  # halted
        assert state["mu"] >= 3
