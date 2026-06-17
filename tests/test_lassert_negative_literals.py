"""Regression test: LASSERT must accept clauses containing negative literals.

Background: the OCaml runner extracted from coq/kernel/nfi/CertCheck.v was
routing word32_to_signed through Z.of_nat, which in turn called
Pos.of_succ_nat — a Peano successor chain. For literal words like
0xFFFFFFFF (= 2^32 - 1 = the wrap-around encoding of DIMACS literal -1),
that chain has roughly 2^32 steps and overflowed the OCaml stack the moment
LASSERT's SAT-checker scanned the first negative literal in a formula.

Symptom: any formula with a negative literal in a clause caused
`extracted_vm_runner failed (exit 3): Stack overflow during execution`.
The bug was invisible to the existing test suite because every other
LASSERT test in the repo uses positive-literal formulas only (a quick
audit of grep 'p_cnf' across tests/ confirms this).

The fix: an Extract Constant directive in coq/Extraction.v that gives
CertCheck.word32_to_signed a direct int-level implementation. The Coq
definition (and proofs about it) are unchanged; the extraction surface
is what was wrong. Both nat and Z extract to plain OCaml int in this
build, so the bypass is semantically identical.

Discovered by: the µ-MDL learner M1 sanity check
(learner/m1_sanity.py) on 2026-05-11. Periodicity claims emit clauses
like (-x_i v x_{i+k}), which are the smallest natural formulas that
require negative literals.
"""
import pytest

from thielecpu.vm import VMState, vm_run

# Every test below drives the extracted OCaml runner (no Python fallback).
pytestmark = pytest.mark.strict_extracted


def _run(formula: str, cert: str, countermodel: str) -> VMState:
    s0 = VMState.default()
    program = [
        {
            "op": "lassert",
            "module": 0,
            "formula": formula,
            "cert_type": "sat",
            "cert": cert,
            "countermodel": countermodel,
            "cost": 0,
        },
        {"op": "halt", "cost": 0},
    ]
    return vm_run(s0, program, max_steps=10)


class TestNegativeLiteralsInFormula:
    """LASSERT must scan formulas containing negated DIMACS literals without
    crashing the runner. These would all stack-overflow before the
    word32_to_signed extraction fix."""

    def test_unit_clause_negative_literal_satisfied(self):
        """Formula (¬x_1), assignment x_1=false. Satisfies; LASSERT accepts."""
        sf = _run("p_cnf_1_1__-1_0", cert="v_-1_0", countermodel="v_1_0")
        assert sf.vm_err is False, "valid cert for (¬x_1) must verify"
        assert sf.vm_mu == 17, (
            "hw_flen=2 (one negative-literal word + 0 terminator) -> mu = 2*8 + 1"
        )

    def test_unit_clause_negative_literal_unsatisfied(self):
        """Formula (¬x_1), assignment x_1=true. Fails; vm_err latches but mu still charged."""
        sf = _run("p_cnf_1_1__-1_0", cert="v_1_0", countermodel="v_-1_0")
        assert sf.vm_err is True, "x_1=true does not satisfy (¬x_1); must fail"
        assert sf.vm_mu == 17, "failed checks still pay the full µ cost"

    def test_two_literal_clause_one_negation(self):
        """Formula (¬x_1 v x_2). Mixed-sign clause exercises the
        word32_to_signed branch on a real two-literal scan."""
        sf = _run(
            "p_cnf_2_1__-1_2_0",
            cert="v_-1_2_0",       # x_1=false, x_2=true -> satisfies
            countermodel="v_1_-2_0",  # x_1=true,  x_2=false -> falsifies
        )
        assert sf.vm_err is False
        # hw_flen = 3 (two literal words + 0 terminator) -> mu = 3*8 + 1 = 25
        assert sf.vm_mu == 25

    def test_equivalence_clauses(self):
        """Periodicity (x_1 ↔ x_2) as two CNF clauses. The original case
        that surfaced the bug (period-1 over a 2-bit stream). Both bits
        equal => assignment satisfies both clauses."""
        # (¬x_1 v x_2) and (x_1 v ¬x_2)
        sf = _run(
            "p_cnf_2_2__-1_2_0__1_-2_0",
            cert="v_1_2_0",          # both true -> satisfies both clauses
            countermodel="v_1_-2_0", # x_1=T, x_2=F -> fails first clause
        )
        assert sf.vm_err is False
        # hw_flen = 6 (two clauses * 3 words each) -> mu = 6*8 + 1 = 49
        assert sf.vm_mu == 49

    def test_equivalence_violated(self):
        """Same formula, assignment x_1=true x_2=false. Violates the equivalence."""
        sf = _run(
            "p_cnf_2_2__-1_2_0__1_-2_0",
            cert="v_1_-2_0",        # x_1=T, x_2=F -> fails (¬x_1 v x_2)
            countermodel="v_1_2_0",
        )
        assert sf.vm_err is True
        assert sf.vm_mu == 49


class TestPositiveLiteralRegressionGuard:
    """Make sure the extraction fix didn't break the existing positive-literal path."""

    def test_unit_clause_positive_literal(self):
        sf = _run("p_cnf_1_1__1_0", cert="v_1_0", countermodel="v_-1_0")
        assert sf.vm_err is False
        assert sf.vm_mu == 17

    def test_two_literal_clause_positive(self):
        sf = _run("p_cnf_2_1__1_2_0", cert="v_1_-2_0", countermodel="v_-1_-2_0")
        assert sf.vm_err is False
        assert sf.vm_mu == 25
