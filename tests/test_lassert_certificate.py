"""Tests for LASSERT certificate verification pipeline.

Validates that real SAT witness packages can flow through the OCaml runner.
All certificate checking is done by the Coq-extracted OCaml binary —
there are no Python reimplementations of check_model or check_lrat.

On-chip model: formula and witness blocks are stored in VM memory via
INIT_MEM_STR directives; instr_lassert uses register indices (freg, creg)
to address them. The vm.py serializer handles this automatically.
"""

import pytest

from thielecpu.vm import VMState, vm_run, _runner_available

SKIP_OCAML = not _runner_available()


@pytest.mark.skipif(SKIP_OCAML, reason="OCaml runner not compiled")
class TestLassertOcamlRunner:
    """Test LASSERT witness passing through the OCaml runner via vm_run().

    Uses the vm_run() API which internally calls extracted_vm_runner via
    _call_runner(). The on-chip model writes formula/witnesses to reserved VM
    memory and uses register indices in the LASSERT instruction.
    """

    def test_lassert_sat_via_vm_run(self):
        """LASSERT with SAT model plus countermodel runs through OCaml runner."""
        s0 = VMState.default()
        program = [
            {"op": "lassert",
             "formula": "p_cnf_1_1__1_0",
             "cert_type": "sat", "cert": "v_1_0", "countermodel": "v_-1_0",
             "cost": 1},
            {"op": "halt", "cost": 0},
        ]
        result = vm_run(s0, program, max_steps=10)
        # mu = flen*8 + S(cost) = ceil(13/4)*8 + 2 = 32 + 2 = 34
        assert result.vm_mu >= 2
        assert result.vm_err is False, \
            "Valid SAT witness package should not set error"

    def test_lassert_missing_dual_witness(self):
        """LASSERT without the required SAT dual witnesses sets error."""
        s0 = VMState.default()
        program = [
            {"op": "lassert",
             "formula": "p_cnf_1_1__1_0",
             "cost": 1},
            {"op": "halt", "cost": 0},
        ]
        result = vm_run(s0, program, max_steps=10)
        assert result.vm_mu >= 2
        # Missing model/countermodel should fail the tightened SAT check.
        assert result.vm_err is True, \
            "Expected error without the required SAT witness package"

    def test_lassert_unsat_always_errors(self):
        """LASSERT_UNSAT path always sets error per Coq spec."""
        s0 = VMState.default()
        program = [
            {"op": "lassert",
             "formula": "p_cnf_1_1__1_0",
             "cert_type": "unsat", "cert": "1_1_0_0",
             "cost": 1},
            {"op": "halt", "cost": 0},
        ]
        result = vm_run(s0, program, max_steps=10)
        assert result.vm_mu >= 2
        # Both step_lassert_unsat and step_lassert_unsat_failure set error
        assert result.vm_err is True, \
            "UNSAT path always sets error per Coq spec"

    def test_lassert_sat_invalid_model(self):
        """LASSERT_SAT with wrong model sets error even if countermodel exists."""
        s0 = VMState.default()
        program = [
            {"op": "lassert",
             "formula": "p_cnf_1_1__1_0",
             "cert_type": "sat", "cert": "v_-1_0", "countermodel": "v_-1_0",
             "cost": 1},
            {"op": "halt", "cost": 0},
        ]
        result = vm_run(s0, program, max_steps=10)
        assert result.vm_mu >= 2
        assert result.vm_err is True, \
            "Expected error with invalid SAT model"
