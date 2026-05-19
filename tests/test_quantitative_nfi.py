"""Quantitative LASSERT pricing tests.

Current kernel semantics split the story into two layers:
1. Every LASSERT charges at least the encoded length: flen * 8.
2. If the execution guard passes, the encoded length must equal the in-memory
   formula header hw_flen, so the paid cost is honest: hw_flen * 8 + S(cost).

The Python VM wrapper must therefore serialize dict-style LASSERT using
flen = hw_flen, not decoded source-text length.
"""

import os
from pathlib import Path

import pytest

from thielecpu.vm import VMState, vm_run

_REPO_ROOT = Path(__file__).resolve().parent.parent
EXTRACTED_VM_RUNNER = _REPO_ROOT / "build" / "extracted_vm_runner"


def _run(instrs):
    return vm_run(VMState.default(), instrs, max_steps=500)


class TestLassertExactCost:
    def test_single_clause_formula_cost_zero(self):
        s = _run([
            {"op": "lassert", "formula": "p_cnf_1_1__1_0",
             "cert_type": "sat", "cert": "v_1_0", "countermodel": "v_-1_0", "cost": 0},
        ])
        assert s.vm_mu == 17
        assert s.vm_err is False

    def test_single_clause_formula_cost_two(self):
        s = _run([
            {"op": "lassert", "formula": "p_cnf_1_1__1_0",
             "cert_type": "sat", "cert": "v_1_0", "countermodel": "v_-1_0", "cost": 2},
        ])
        assert s.vm_mu == 19
        assert s.vm_err is False

    def test_two_clause_formula_cost_zero(self):
        s = _run([
            {"op": "lassert", "formula": "p_cnf_2_2__1_0__2_0",
             "cert_type": "sat", "cert": "v_1_2_0", "countermodel": "v_-1_-2_0", "cost": 0},
        ])
        assert s.vm_mu == 33
        assert s.vm_err is False

    def test_formula_and_extra_cost(self):
        s = _run([
            {"op": "lassert", "formula": "p_cnf_2_1__1_2_0",
             "cert_type": "sat", "cert": "v_1_-2_0", "countermodel": "v_-1_-2_0", "cost": 3},
        ])
        assert s.vm_mu == 28
        assert s.vm_err is False


class TestQuantitativeLowerBound:
    @pytest.mark.parametrize(
        "formula,cert,countermodel,hw_flen,cost",
        [
            ("p_cnf_1_1__1_0", "v_1_0", "v_-1_0", 2, 0),
            ("p_cnf_1_1__1_0", "v_1_0", "v_-1_0", 2, 1),
            ("p_cnf_2_1__1_2_0", "v_1_-2_0", "v_-1_-2_0", 3, 0),
            ("p_cnf_2_2__1_0__2_0", "v_1_2_0", "v_-1_-2_0", 4, 0),
            ("p_cnf_3_3__1_0__2_0__3_0", "v_1_2_3_0", "v_-1_-2_-3_0", 6, 0),
        ],
    )
    def test_lower_bound_holds(self, formula, cert, countermodel, hw_flen, cost):
        s = _run([
            {"op": "lassert", "formula": formula,
             "cert_type": "sat", "cert": cert, "countermodel": countermodel, "cost": cost},
        ])
        assert s.vm_mu >= hw_flen * 8


class TestFormulaLengthMonotonicity:
    def test_longer_binary_formula_costs_more(self):
        programs = [
            {"op": "lassert", "formula": "p_cnf_1_1__1_0",
             "cert_type": "sat", "cert": "v_1_0", "countermodel": "v_-1_0", "cost": 0},
            {"op": "lassert", "formula": "p_cnf_2_1__1_2_0",
             "cert_type": "sat", "cert": "v_1_-2_0", "countermodel": "v_-1_-2_0", "cost": 0},
            {"op": "lassert", "formula": "p_cnf_3_3__1_0__2_0__3_0",
             "cert_type": "sat", "cert": "v_1_2_3_0", "countermodel": "v_-1_-2_-3_0", "cost": 0},
        ]
        mus = [_run([program]).vm_mu for program in programs]
        assert mus[0] < mus[1] < mus[2]


class TestOcamlRunnerAgreement:
    def test_ocaml_charges_hw_flen(self):
        if not EXTRACTED_VM_RUNNER.exists():
            pytest.skip("OCaml runner not built")

        s = vm_run(VMState.default(), [
            {"op": "lassert", "formula": "p_cnf_2_1__1_2_0",
             "cert_type": "sat", "cert": "v_1_-2_0", "countermodel": "v_-1_-2_0", "cost": 0},
        ], max_steps=500)
        assert s.vm_mu == 25  # hw_flen=3 words → 3*8+S(0) = 25
        assert s.vm_err is False
