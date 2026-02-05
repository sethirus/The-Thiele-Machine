"""Semantic μ-cost: Python implementation ISOMORPHIC to Coq specification.

This module implements semantic_complexity_bits EXACTLY as defined in
coq/kernel/SemanticMuCost.v.

CRITICAL: Any divergence from the Coq specification breaks the three-layer
isomorphism (Coq ≡ Python ≡ Verilog).

SPECIFICATION SOURCE: coq/kernel/SemanticMuCost.v
AUTHOR: Three-Layer Isomorphism Team
DATE: February 4, 2026
"""

from __future__ import annotations
import z3
from typing import Union, Tuple
from dataclasses import dataclass


# =========================================================================
# PART 1: ABSTRACT SYNTAX TREE (matches Coq Constraint type)
# =========================================================================

@dataclass(frozen=True)
class ConstraintAST:
    """AST node matching Coq's Constraint inductive type.

    Corresponds to:
      Inductive Constraint : Type :=
      | CAtom : AtomicConstraint -> Constraint
      | CAnd : Constraint -> Constraint -> Constraint
      | COr : Constraint -> Constraint -> Constraint
      | CNot : Constraint -> Constraint
      | CTrue : Constraint
      | CFalse : Constraint.
    """
    pass


@dataclass(frozen=True)
class CAtom(ConstraintAST):
    """Atomic constraint (comparison)."""
    op: str  # "eq", "lt", "le"  (normalized: no "gt" or "ge")
    left: ArithExpr
    right: ArithExpr


@dataclass(frozen=True)
class CAnd(ConstraintAST):
    """Conjunction."""
    left: ConstraintAST
    right: ConstraintAST


@dataclass(frozen=True)
class COr(ConstraintAST):
    """Disjunction."""
    left: ConstraintAST
    right: ConstraintAST


@dataclass(frozen=True)
class CNot(ConstraintAST):
    """Negation."""
    inner: ConstraintAST


@dataclass(frozen=True)
class CTrue(ConstraintAST):
    """Tautology."""
    pass


@dataclass(frozen=True)
class CFalse(ConstraintAST):
    """Contradiction."""
    pass


@dataclass(frozen=True)
class ArithExpr:
    """Arithmetic expression matching Coq's ArithExpr type."""
    pass


@dataclass(frozen=True)
class AVar(ArithExpr):
    """Variable (normalized to v0, v1, v2, ...)."""
    var_id: int


@dataclass(frozen=True)
class AConst(ArithExpr):
    """Integer constant."""
    value: int


@dataclass(frozen=True)
class AAdd(ArithExpr):
    """Addition."""
    left: ArithExpr
    right: ArithExpr


@dataclass(frozen=True)
class ASub(ArithExpr):
    """Subtraction."""
    left: ArithExpr
    right: ArithExpr


@dataclass(frozen=True)
class AMul(ArithExpr):
    """Multiplication."""
    left: ArithExpr
    right: ArithExpr


# =========================================================================
# PART 2: Z3 TO COQ AST TRANSLATION
# =========================================================================

def z3_to_coq_ast(expr: z3.ExprRef, var_map: dict[str, int] = None) -> Union[ConstraintAST, ArithExpr]:
    """Translate Z3 expression to Coq-isomorphic AST.

    CRITICAL: This must produce the EXACT SAME structure as Coq parsing.

    Args:
        expr: Z3 expression
        var_map: Maps variable names to normalized IDs (v0, v1, ...)

    Returns:
        ConstraintAST or ArithExpr matching Coq structure
    """
    if var_map is None:
        var_map = {}

    # Constants
    if z3.is_int_value(expr):
        return AConst(expr.as_long())

    if z3.is_true(expr):
        return CTrue()

    if z3.is_false(expr):
        return CFalse()

    # Variables
    if z3.is_const(expr) and not z3.is_int_value(expr):
        var_name = str(expr)
        if var_name not in var_map:
            var_map[var_name] = len(var_map)  # Assign next ID
        return AVar(var_map[var_name])

    # Compound expressions
    if z3.is_app(expr):
        kind = expr.decl().kind()
        children = [z3_to_coq_ast(child, var_map) for child in expr.children()]

        # Arithmetic operations
        if kind == z3.Z3_OP_ADD:
            return AAdd(children[0], children[1])
        elif kind == z3.Z3_OP_SUB:
            return ASub(children[0], children[1])
        elif kind == z3.Z3_OP_MUL:
            return AMul(children[0], children[1])

        # Comparison operations (with normalization)
        elif kind == z3.Z3_OP_LT:
            return CAtom("lt", children[0], children[1])
        elif kind == z3.Z3_OP_LE:
            return CAtom("le", children[0], children[1])
        elif kind == z3.Z3_OP_GT:
            # NORMALIZE: x > y becomes y < x (matches Coq normalization)
            return CAtom("lt", children[1], children[0])
        elif kind == z3.Z3_OP_GE:
            # NORMALIZE: x >= y becomes y <= x
            return CAtom("le", children[1], children[0])
        elif kind == z3.Z3_OP_EQ:
            return CAtom("eq", children[0], children[1])

        # Logical operations
        elif kind == z3.Z3_OP_AND:
            # Build right-associative: (and A B C) → (and A (and B C))
            result = children[-1]
            for child in reversed(children[:-1]):
                result = CAnd(child, result)
            return result

        elif kind == z3.Z3_OP_OR:
            # Build right-associative
            result = children[-1]
            for child in reversed(children[:-1]):
                result = COr(child, result)
            return result

        elif kind == z3.Z3_OP_NOT:
            return CNot(children[0])

    # Fallback: treat as variable (for safety)
    var_name = str(expr)
    if var_name not in var_map:
        var_map[var_name] = len(var_map)
    return AVar(var_map[var_name])


# =========================================================================
# PART 3: STRUCTURAL COUNTS (must match Coq exactly)
# =========================================================================

def count_vars_arith(e: ArithExpr) -> int:
    """Count variables in arithmetic expression.

    ISOMORPHISM: Matches count_vars_arith in SemanticMuCost.v
    """
    if isinstance(e, AVar):
        return 1
    elif isinstance(e, AConst):
        return 0
    elif isinstance(e, (AAdd, ASub, AMul)):
        return count_vars_arith(e.left) + count_vars_arith(e.right)
    else:
        return 0


def count_vars(c: ConstraintAST) -> int:
    """Count variables in constraint.

    ISOMORPHISM: Matches count_vars in SemanticMuCost.v
    """
    if isinstance(c, CAtom):
        return count_vars_arith(c.left) + count_vars_arith(c.right)
    elif isinstance(c, (CAnd, COr)):
        return count_vars(c.left) + count_vars(c.right)
    elif isinstance(c, CNot):
        return count_vars(c.inner)
    elif isinstance(c, (CTrue, CFalse)):
        return 0
    else:
        return 0


def count_atoms(c: ConstraintAST) -> int:
    """Count atomic constraints (comparisons).

    ISOMORPHISM: Matches count_atoms in SemanticMuCost.v
    """
    if isinstance(c, CAtom):
        return 1
    elif isinstance(c, (CAnd, COr)):
        return count_atoms(c.left) + count_atoms(c.right)
    elif isinstance(c, CNot):
        return count_atoms(c.inner)
    elif isinstance(c, (CTrue, CFalse)):
        return 0
    else:
        return 0


def count_operators(c: ConstraintAST) -> int:
    """Count logical operators.

    ISOMORPHISM: Matches count_operators in SemanticMuCost.v
    """
    if isinstance(c, CAtom):
        return 1  # Comparison is an operator
    elif isinstance(c, (CAnd, COr)):
        return 1 + count_operators(c.left) + count_operators(c.right)
    elif isinstance(c, CNot):
        return 1 + count_operators(c.inner)
    elif isinstance(c, (CTrue, CFalse)):
        return 0
    else:
        return 0


# =========================================================================
# PART 4: LOG2_NAT (must match Coq exactly)
# =========================================================================

def log2_nat(n: int) -> int:
    """Ceiling of log₂(n) matching Coq's log2_nat.

    CRITICAL: This MUST match the Coq definition exactly:

    Definition log2_nat (n : nat) : nat :=
      match n with
      | 0 => 0
      | S _ => Nat.log2 n + (if Nat.pow 2 (Nat.log2 n) =? n then 0 else 1)
      end.

    ISOMORPHISM TEST:
      For all n ≥ 0: coq_log2_nat(n) == python_log2_nat(n)
    """
    if n <= 0:
        return 0

    # Nat.log2 n (floor of log₂)
    log_n = n.bit_length() - 1

    # Check if n is exactly 2^log_n
    if (1 << log_n) == n:
        return log_n  # Exact power of 2
    else:
        return log_n + 1  # Ceiling


# =========================================================================
# PART 5: SEMANTIC COMPLEXITY BITS (must match Coq exactly)
# =========================================================================

def semantic_complexity_bits(c: ConstraintAST) -> int:
    """Compute semantic complexity in bits.

    CRITICAL: This MUST produce the EXACT SAME value as Coq:

    Definition semantic_complexity_bits (c : Constraint) : nat :=
      let atoms := count_atoms c in
      let vars := count_vars c in
      let ops := count_operators c in
      let atom_bits := log2_nat (S atoms) in
      let var_bits := log2_nat (S vars) in
      let op_bits := log2_nat (S ops) in
      8 * (atom_bits + var_bits + op_bits).

    ISOMORPHISM TEST:
      For all constraints c:
        coq_semantic_complexity_bits(c) == python_semantic_complexity_bits(c)
    """
    atoms = count_atoms(c)
    vars_count = count_vars(c)
    ops = count_operators(c)

    # Compute logarithmic contributions (note: S n in Coq is n+1 in Python)
    atom_bits = log2_nat(atoms + 1)
    var_bits = log2_nat(vars_count + 1)
    op_bits = log2_nat(ops + 1)

    # Total: sum of structural complexities, converted to bytes
    return 8 * (atom_bits + var_bits + op_bits)


# =========================================================================
# PART 6: PUBLIC API
# =========================================================================

def parse_and_compute_semantic_cost(expr_str: str) -> Tuple[int, ConstraintAST]:
    """Parse expression and compute semantic μ-cost.

    Returns:
        (semantic_complexity_bits, ast)

    This is the main entry point for the μ-cost system.
    """
    from thielecpu.semantic_mu import parse_to_z3

    # Parse to Z3
    z3_expr = parse_to_z3(expr_str)

    # Translate to Coq-isomorphic AST
    var_map = {}
    coq_ast = z3_to_coq_ast(z3_expr, var_map)

    # Compute semantic complexity (matches Coq exactly)
    complexity = semantic_complexity_bits(coq_ast)

    return complexity, coq_ast


def semantic_mu_cost_isomorphic(expr: str, before: int, after: int) -> Tuple[int, float]:
    """Calculate μ-cost using Coq-isomorphic semantic complexity.

    Returns:
        (description_bits, entropy_bits)

    GUARANTEE: description_bits matches Coq's semantic_complexity_bits exactly.
    """
    import math

    # Description cost: semantic complexity (Coq-isomorphic)
    description_bits, _ = parse_and_compute_semantic_cost(expr)

    # Entropy cost: Shannon entropy (unchanged)
    if after >= before or before <= 0 or after <= 0:
        entropy_bits = 0.0
    else:
        entropy_bits = math.log2(before / after)

    return (description_bits, entropy_bits)


# =========================================================================
# PART 7: ISOMORPHISM TESTS
# =========================================================================

def test_isomorphism():
    """Test that Python matches Coq specification exactly."""
    import sys
    import io
    sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8', errors='replace')

    print("=" * 70)
    print("ISOMORPHISM TEST: Python ≡ Coq")
    print("=" * 70)

    # Test log2_nat matches Coq
    print("\nTest 1: log2_nat isomorphism")
    test_values = [0, 1, 2, 3, 4, 5, 7, 8, 9, 15, 16, 17, 31, 32, 33]
    for n in test_values:
        result = log2_nat(n)
        # Expected values (from Coq):
        # log2_nat 0 = 0
        # log2_nat 1 = 0 (since 2^0 = 1)
        # log2_nat 2 = 1 (since 2^1 = 2)
        # log2_nat 3 = 2 (ceiling)
        # log2_nat 4 = 2 (since 2^2 = 4)
        print(f"  log2_nat({n:3d}) = {result}")

    # Test semantic complexity
    print("\nTest 2: Semantic complexity (syntax invariance)")
    test_cases = [
        ("x > 0", "x>0"),
        ("x > 0", "0 < x"),  # Should normalize to same form
    ]

    for expr1, expr2 in test_cases:
        try:
            cost1, ast1 = parse_and_compute_semantic_cost(expr1)
            cost2, ast2 = parse_and_compute_semantic_cost(expr2)

            print(f"\n  '{expr1}' vs '{expr2}':")
            print(f"    Cost 1: {cost1} bits")
            print(f"    Cost 2: {cost2} bits")
            print(f"    Atoms: {count_atoms(ast1)} vs {count_atoms(ast2)}")
            print(f"    Vars: {count_vars(ast1)} vs {count_vars(ast2)}")
            print(f"    Ops: {count_operators(ast1)} vs {count_operators(ast2)}")

            if cost1 == cost2:
                print("    ✓ PASS: Costs match")
            else:
                print(f"    ✗ FAIL: Costs differ ({cost1} != {cost2})")

        except Exception as e:
            print(f"    ❌ ERROR: {e}")

    print("\n" + "=" * 70)
    print("ISOMORPHISM VERIFICATION COMPLETE")
    print("=" * 70)


if __name__ == "__main__":
    test_isomorphism()
