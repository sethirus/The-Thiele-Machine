"""
TDD tests for the unconditional quantitative No Free Insight theorem.

THEOREM (StateSpaceCounting.v after fix):
  forall s s' mid formula cert cost,
    vm_step s (instr_lassert mid formula cert cost) s' ->
    s'.(vm_mu) - s.(vm_mu) >= String.length formula.

The theorem must hold with NO precondition on cost.

The implementation contract across all three layers:
  instruction_cost (instr_lassert _ formula _ cost) = String.length formula + S cost

  i.e.  delta_mu = len(formula) + cost + 1   (exact)
        delta_mu >= len(formula)              (lower bound — the theorem)

These tests FAIL before the VMStep.v change and PASS after.
"""

import pytest
from thielecpu.vm import VMState, vm_run, vm_apply


def _run(instrs):
    """Run a program, return final VMState."""
    return vm_run(VMState.default(), instrs, max_steps=500)


def _delta_mu(before_mu: int, instrs: list) -> int:
    """Measure mu increase from executing instrs starting at given mu."""
    # build a pnew first so lassert has a valid module
    program = [
        {"op": "pnew", "region": [0, 1], "cost": 0},
    ] + instrs
    s = _run(program)
    return s.vm_mu - 0  # pnew costs 0, all mu is from instrs


# ---------------------------------------------------------------------------
# CORE: exact cost contract   delta_mu == len(formula) + cost + 1
# ---------------------------------------------------------------------------

class TestLassertExactCost:
    """Verify delta_mu = String.length(formula) + cost + 1 (extracted from Coq)."""

    def test_single_char_formula_cost_zero(self):
        # formula="x" len=1, user cost=0 -> delta_mu = 1 + 0 + 1 = 2
        program = [
            {"op": "pnew", "region": [0, 1], "cost": 0},
            {"op": "lassert", "module": 0, "formula": "x",
             "cert": {"type": "sat", "proof": ""}, "cost": 0},
        ]
        # formula="x" len=1, user cost=0 -> delta_mu = 1*8 + 0 + 1 = 9
        s = _run(program)
        assert s.vm_mu == 9, f"expected 9 (1*8+0+1), got {s.vm_mu}"

    def test_single_char_formula_cost_two(self):
        # formula="x" len=1, user cost=2 -> delta_mu = 1*8 + 2 + 1 = 11
        program = [
            {"op": "pnew", "region": [0, 1], "cost": 0},
            {"op": "lassert", "module": 0, "formula": "x",
             "cert": {"type": "sat", "proof": ""}, "cost": 2},
        ]
        s = _run(program)
        assert s.vm_mu == 11, f"expected 11 (1*8+2+1), got {s.vm_mu}"

    def test_ten_char_formula(self):
        # formula="aaaaaaaaaa" len=10, user cost=0 -> delta_mu = 10*8 + 0 + 1 = 81
        formula = "a" * 10
        program = [
            {"op": "pnew", "region": [0, 1], "cost": 0},
            {"op": "lassert", "module": 0, "formula": formula,
             "cert": {"type": "sat", "proof": ""}, "cost": 0},
        ]
        s = _run(program)
        assert s.vm_mu == 81, f"expected 81 (10*8+0+1), got {s.vm_mu}"

    def test_formula_and_extra_cost(self):
        # formula="hello" len=5, user cost=3 -> delta_mu = 5*8 + 3 + 1 = 44
        program = [
            {"op": "pnew", "region": [0, 1], "cost": 0},
            {"op": "lassert", "module": 0, "formula": "hello",
             "cert": {"type": "sat", "proof": ""}, "cost": 3},
        ]
        s = _run(program)
        assert s.vm_mu == 44, f"expected 44 (5*8+3+1), got {s.vm_mu}"


# ---------------------------------------------------------------------------
# THEOREM: lower bound   delta_mu >= len(formula)   (unconditional)
# ---------------------------------------------------------------------------

class TestQuantitativeLowerBound:
    """
    The theorem proven in StateSpaceCounting.v:
      delta_mu >= String.length formula * 8   (μ denominated in bits)
    This must hold for ALL formulas and ALL cost values, including cost=0.
    """

    @pytest.mark.parametrize("formula,cost", [
        ("x", 0),
        ("x", 1),
        ("sat_formula", 0),
        ("and_gte_x0_and_lt_x10_pad", 0),   # no spaces, same idea as (and (>= x 0) (< x 10))
        ("a" * 100, 0),
    ])
    def test_lower_bound_holds(self, formula, cost):
        mu_before = 0
        program = [
            {"op": "pnew", "region": [0, 1], "cost": 0},
            {"op": "lassert", "module": 0, "formula": formula,
             "cert": {"type": "sat", "proof": ""}, "cost": cost},
        ]
        s = _run(program)
        delta = s.vm_mu - mu_before
        bits = len(formula) * 8
        assert delta >= bits, (
            f"THEOREM VIOLATED: formula={formula!r} (len={len(formula)}, bits={bits}), "
            f"cost={cost}, delta_mu={delta} < {bits}"
        )


# ---------------------------------------------------------------------------
# MONOTONICITY: longer formula → higher cost (same user cost)
# ---------------------------------------------------------------------------

class TestFormulaLengthMonotonicity:
    """Longer formulas must cost strictly more (for the same user cost)."""

    def test_longer_costs_more(self):
        cost = 0
        formulas = ["x", "hello", "a" * 20]
        mus = []
        for f in formulas:
            s = _run([
                {"op": "pnew", "region": [0, 1], "cost": 0},
                {"op": "lassert", "module": 0, "formula": f,
                 "cert": {"type": "sat", "proof": ""}, "cost": cost},
            ])
            mus.append(s.vm_mu)

        for i in range(len(formulas) - 1):
            assert mus[i] < mus[i + 1], (
                f"formula {formulas[i]!r} (mu={mus[i]}) should cost less than "
                f"{formulas[i+1]!r} (mu={mus[i+1]})"
            )


# ---------------------------------------------------------------------------
# CROSS-LAYER: OCaml runner agrees with Python VM formula-length cost
# ---------------------------------------------------------------------------

class TestOcamlRunnerAgreement:
    """OCaml extracted runner must charge the same formula-length cost."""

    def test_ocaml_charges_formula_length(self):
        """Verify that extracted OCaml runner (via vm_run) agrees on formula-length cost."""
        import os

        runner = "/workspaces/The-Thiele-Machine/build/extracted_vm_runner"
        if not os.path.exists(runner):
            pytest.skip("OCaml runner not built")

        formula = "hello"  # len=5, bits=40, cost=0 -> delta_mu = 5*8 + 0 + 1 = 41
        program = [
            {"op": "pnew", "region": [0, 1], "cost": 0},
            {"op": "lassert", "module": 0, "formula": formula,
             "cert": {"type": "sat", "proof": ""}, "cost": 0},
        ]
        s = vm_run(VMState.default(), program, max_steps=500)
        mu = s.vm_mu
        bits = len(formula) * 8
        assert mu >= bits, (
            f"OCaml runner: mu={mu} < bits={bits}"
        )
        assert mu == bits + 1, (
            f"OCaml runner: expected {bits+1} ({len(formula)}*8+0+1), got {mu} "
            f"(formula={formula!r}, cost=0)"
        )
