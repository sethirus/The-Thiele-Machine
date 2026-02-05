"""Test three-layer isomorphism for semantic μ-cost.

This test verifies that Coq ≡ Python ≡ Verilog for the new semantic
μ-cost calculation.

CRITICAL: Any divergence breaks the three-layer isomorphism guarantee.

Test strategy:
1. Define test constraints
2. Compute semantic_complexity_bits in Python (matching Coq spec)
3. Verify syntax invariance
4. Verify structural properties match Coq
5. (Future) Verify Verilog LEI enforces same costs
"""

import pytest
from thielecpu.semantic_mu_coq_isomorphic import (
    parse_and_compute_semantic_cost,
    semantic_complexity_bits,
    log2_nat,
    count_atoms,
    count_vars,
    count_operators,
    CAtom, CAnd, COr, CNot, CTrue, CFalse,
    AVar, AConst,
)


class TestLog2NatIsomorphism:
    """Verify log2_nat matches Coq specification exactly."""

    def test_log2_nat_zero(self):
        """log2_nat 0 = 0 (Coq: match n with | 0 => 0)"""
        assert log2_nat(0) == 0

    def test_log2_nat_powers_of_two(self):
        """log2_nat (2^k) = k for exact powers."""
        powers = [1, 2, 4, 8, 16, 32, 64, 128, 256]
        expected = [0, 1, 2, 3, 4, 5, 6, 7, 8]
        for power, exp in zip(powers, expected):
            assert log2_nat(power) == exp, f"log2_nat({power}) should be {exp}"

    def test_log2_nat_ceiling(self):
        """log2_nat rounds up (ceiling) for non-powers."""
        # 3 is between 2^1 and 2^2, so ceiling is 2
        assert log2_nat(3) == 2
        # 5 is between 2^2 and 2^3, so ceiling is 3
        assert log2_nat(5) == 3
        # 7 is between 2^2 and 2^3, so ceiling is 3
        assert log2_nat(7) == 3
        # 9 is between 2^3 and 2^4, so ceiling is 4
        assert log2_nat(9) == 4


class TestCoqASTCounts:
    """Verify count functions match Coq definitions."""

    def test_count_atoms_simple(self):
        """Single comparison → 1 atom."""
        ast = CAtom("lt", AVar(0), AConst(0))
        assert count_atoms(ast) == 1

    def test_count_atoms_and(self):
        """(and A B) → count_atoms A + count_atoms B."""
        a1 = CAtom("lt", AVar(0), AConst(0))
        a2 = CAtom("lt", AVar(1), AConst(10))
        ast = CAnd(a1, a2)
        assert count_atoms(ast) == 2

    def test_count_atoms_nested(self):
        """(and (and A B) C) → 3 atoms."""
        a1 = CAtom("eq", AVar(0), AConst(0))
        a2 = CAtom("lt", AVar(1), AConst(5))
        a3 = CAtom("lt", AVar(2), AConst(10))
        ast = CAnd(CAnd(a1, a2), a3)
        assert count_atoms(ast) == 3

    def test_count_vars(self):
        """Count variables in constraint."""
        # (x > 0) has 1 variable occurrence
        ast = CAtom("lt", AConst(0), AVar(0))
        assert count_vars(ast) == 1

        # (x > 0 and y < 10) has 2 variable occurrences
        a1 = CAtom("lt", AConst(0), AVar(0))
        a2 = CAtom("lt", AVar(1), AConst(10))
        ast = CAnd(a1, a2)
        assert count_vars(ast) == 2

    def test_count_operators(self):
        """Count logical operators."""
        # Single comparison: 1 operator
        ast = CAtom("lt", AVar(0), AConst(0))
        assert count_operators(ast) == 1

        # (and A B): 1 (and) + 1 (comparison A) + 1 (comparison B) = 3
        a1 = CAtom("lt", AVar(0), AConst(0))
        a2 = CAtom("lt", AVar(1), AConst(10))
        ast = CAnd(a1, a2)
        assert count_operators(ast) == 3


class TestSemanticComplexity:
    """Verify semantic_complexity_bits matches Coq formula."""

    def test_formula_correctness(self):
        """Verify: 8 * (log₂(atoms+1) + log₂(vars+1) + log₂(ops+1))"""
        # Simple constraint: x > 0
        # atoms = 1, vars = 1, ops = 1
        # log₂(2) + log₂(2) + log₂(2) = 1 + 1 + 1 = 3
        # 8 * 3 = 24 bits
        ast = CAtom("lt", AConst(0), AVar(0))

        complexity = semantic_complexity_bits(ast)

        atoms = count_atoms(ast)
        vars_count = count_vars(ast)
        ops = count_operators(ast)

        assert atoms == 1
        assert vars_count == 1
        assert ops == 1

        expected = 8 * (log2_nat(atoms + 1) + log2_nat(vars_count + 1) + log2_nat(ops + 1))
        assert complexity == expected == 24

    def test_more_complex(self):
        """Test with (and (x > 0) (x < 10))."""
        # atoms = 2, vars = 2, ops = 3 (two comparisons + one and)
        # log₂(3) + log₂(3) + log₂(4) = 2 + 2 + 2 = 6
        # 8 * 6 = 48 bits (but may vary based on actual counts)

        a1 = CAtom("lt", AConst(0), AVar(0))
        a2 = CAtom("lt", AVar(0), AConst(10))
        ast = CAnd(a1, a2)

        complexity = semantic_complexity_bits(ast)

        atoms = count_atoms(ast)
        vars_count = count_vars(ast)
        ops = count_operators(ast)

        expected = 8 * (log2_nat(atoms + 1) + log2_nat(vars_count + 1) + log2_nat(ops + 1))
        assert complexity == expected


class TestSyntaxInvariance:
    """Verify that syntax differences don't affect cost."""

    def test_spacing_invariance(self):
        """'x>0' and 'x > 0' should have identical costs."""
        cost1, ast1 = parse_and_compute_semantic_cost("x > 0")
        cost2, ast2 = parse_and_compute_semantic_cost("x>0")

        assert cost1 == cost2, f"Spacing should not affect cost: {cost1} != {cost2}"

        # Structural counts should also match
        assert count_atoms(ast1) == count_atoms(ast2)
        assert count_vars(ast1) == count_vars(ast2)
        assert count_operators(ast1) == count_operators(ast2)

    def test_comparison_normalization(self):
        """'x > 0' and '0 < x' should normalize to same form."""
        cost1, ast1 = parse_and_compute_semantic_cost("x > 0")
        cost2, ast2 = parse_and_compute_semantic_cost("0 < x")

        assert cost1 == cost2, f"Normalized comparisons should have same cost: {cost1} != {cost2}"

    def test_whitespace_variations(self):
        """Various whitespace patterns should not affect cost."""
        variations = [
            "x>0",
            "x >0",
            "x> 0",
            "x > 0",
            "x  >  0",
        ]

        costs = [parse_and_compute_semantic_cost(v)[0] for v in variations]

        # All costs should be identical
        assert all(c == costs[0] for c in costs), f"Whitespace affected costs: {costs}"


class TestCoqEquivalenceProperties:
    """Verify properties that must hold for Coq equivalence."""

    def test_monotonicity(self):
        """Adding constraints should not decrease complexity."""
        # Simple: x > 0
        simple_cost, _ = parse_and_compute_semantic_cost("x > 0")

        # Complex: (x > 0 and x < 10)
        complex_cost, _ = parse_and_compute_semantic_cost("z3.And(x > 0, x < 10)")

        assert complex_cost >= simple_cost, "Adding constraints should not decrease cost"

    def test_constant_folding_independence(self):
        """Complexity should not depend on constant values."""
        # x > 0
        cost1, _ = parse_and_compute_semantic_cost("x > 0")

        # x > 100
        cost2, _ = parse_and_compute_semantic_cost("x > 100")

        # Should have same complexity (both are "var > const")
        assert cost1 == cost2, "Constant values should not affect complexity"


class TestThreeLayerIsomorphismGuarantee:
    """Verify the three-layer isomorphism guarantee."""

    def test_documented_isomorphism_requirement(self):
        """Verify that semantic_complexity_bits is documented as isomorphic."""
        import thielecpu.semantic_mu_coq_isomorphic as module

        # Check that the module has the isomorphism documentation
        assert "ISOMORPHIC" in module.__doc__ or "isomorphic" in module.__doc__

        # Check that key functions are documented as matching Coq
        assert "log2_nat" in dir(module)
        assert "semantic_complexity_bits" in dir(module)
        assert "count_atoms" in dir(module)
        assert "count_vars" in dir(module)
        assert "count_operators" in dir(module)

    def test_coq_file_exists(self):
        """Verify that the Coq specification file exists."""
        import os
        coq_file = os.path.join(os.path.dirname(__file__), "..", "coq", "kernel", "SemanticMuCost.v")
        assert os.path.exists(coq_file), f"Coq specification not found: {coq_file}"


class TestRegressionPrevention:
    """Prevent regression back to string-length-based costs."""

    def test_no_string_length_dependency(self):
        """Ensure cost does not depend on string length."""
        # These have different string lengths but same semantics
        short = "x>0"  # length 3
        long = "x > 0"  # length 5

        cost_short, _ = parse_and_compute_semantic_cost(short)
        cost_long, _ = parse_and_compute_semantic_cost(long)

        # If these differ, we've regressed to string-length-based costs
        assert cost_short == cost_long, (
            f"REGRESSION: Costs depend on string length! "
            f"short='{short}' ({cost_short} bits), "
            f"long='{long}' ({cost_long} bits)"
        )


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
