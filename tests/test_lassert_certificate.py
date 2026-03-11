"""Tests for LASSERT certificate verification pipeline.

Validates that real SAT certificates can flow through the OCaml runner.
All certificate checking is done by the Coq-extracted OCaml binary —
there are no Python reimplementations of check_model or check_lrat.
"""

import pytest

from thielecpu.vm import VMState, vm_run, _runner_available

SKIP_OCAML = not _runner_available()


@pytest.mark.skipif(SKIP_OCAML, reason="OCaml runner not compiled")
class TestLassertOcamlRunner:
    """Test LASSERT certificate passing through the OCaml runner via vm_run().

    Uses the vm_run() API which internally calls extracted_vm_runner via
    _call_runner(). The LASSERT_SAT and LASSERT_UNSAT text formats are
    extensions added to extracted_vm_runner.ml.
    """

    def test_lassert_sat_via_vm_run(self):
        """LASSERT with SAT cert runs through OCaml runner, charges mu."""
        s0 = VMState.default()
        program = [
            {"op": "pnew", "region": [0, 256], "cost": 1},
            {"op": "lassert", "module": 0,
             "formula": "p_cnf_1_1__1_0",
             "cert_type": "sat", "cert": "v_1_0",
             "cost": 1},
            {"op": "halt", "cost": 0},
        ]
        result = vm_run(s0, program, max_steps=10)
        # mu should advance by at least PNEW(1) + LASSERT(1) = 2
        assert result.vm_mu >= 2

    def test_lassert_legacy_empty_cert(self):
        """Legacy LASSERT (empty cert) sets error for real formulas."""
        s0 = VMState.default()
        program = [
            {"op": "pnew", "region": [0, 256], "cost": 1},
            {"op": "lassert", "module": 0,
             "formula": "p_cnf_1_1__1_0",
             "cost": 1},
            {"op": "halt", "cost": 0},
        ]
        result = vm_run(s0, program, max_steps=10)
        assert result.vm_mu >= 2
        # Empty cert "" should fail check_model
        assert result.vm_err is True, \
            "Expected error with empty certificate (OCaml check_model fails)"

    def test_lassert_unsat_always_errors(self):
        """LASSERT_UNSAT path always sets error per Coq spec."""
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
        assert result.vm_mu >= 2
        # Both step_lassert_unsat and step_lassert_unsat_failure set error
        assert result.vm_err is True, \
            "UNSAT path always sets error per Coq spec"

    def test_lassert_sat_invalid_model(self):
        """LASSERT_SAT with wrong model sets error."""
        s0 = VMState.default()
        program = [
            {"op": "pnew", "region": [0, 256], "cost": 1},
            {"op": "lassert", "module": 0,
             "formula": "p_cnf_1_1__1_0",
             "cert_type": "sat", "cert": "v_-1_0",
             "cost": 1},
            {"op": "halt", "cost": 0},
        ]
        result = vm_run(s0, program, max_steps=10)
        assert result.vm_mu >= 2
        assert result.vm_err is True, \
            "Expected error with invalid SAT model"
