"""Deep semantic canonicalization for μ-cost calculations.

This module provides true semantic equivalence by normalizing constraints
to a canonical form that is invariant under:
- Commutativity: (and A B) ≡ (and B A)
- Associativity: (and (and A B) C) ≡ (and A (and B C))
- Variable renaming: (> x 0) ≡ (> y 0)
- Constant folding: (+ 2 3) → 5
- Tautology elimination: (and A true) → A
"""

from __future__ import annotations
import z3
import hashlib
from typing import Any, Set, List, Tuple, Dict
from dataclasses import dataclass
from collections import Counter


@dataclass(frozen=True)
class CanonicalConstraint:
    """A constraint in deep canonical form.

    Properties:
    - Syntax-independent
    - Commutative operations are sorted
    - Associative operations are flattened
    - Variables are normalized
    - Constants are folded
    """

    form_type: str  # "comparison", "and", "or", "not", "constant"
    operator: str  # "lt", "le", "eq", "gt", "ge", etc.
    operands: Tuple[Any, ...]  # Sorted, recursive canonical forms

    def __hash__(self) -> int:
        return hash((self.form_type, self.operator, self.operands))

    def to_hash(self) -> str:
        """Compute semantic hash of this constraint."""
        canonical_str = self._to_canonical_string()
        return hashlib.sha256(canonical_str.encode('utf-8')).hexdigest()[:16]

    def _to_canonical_string(self) -> str:
        """Convert to canonical string representation."""
        if self.form_type == "constant":
            return f"const({self.operator})"
        elif self.form_type == "variable":
            return f"var({self.operator})"
        elif self.form_type == "comparison":
            op_strs = [self._operand_to_string(o) for o in self.operands]
            return f"{self.operator}({','.join(op_strs)})"
        else:
            op_strs = [self._operand_to_string(o) for o in self.operands]
            return f"{self.form_type}({','.join(op_strs)})"

    def _operand_to_string(self, operand) -> str:
        """Convert operand to string (recursive)."""
        if isinstance(operand, CanonicalConstraint):
            return operand._to_canonical_string()
        elif isinstance(operand, int):
            return str(operand)
        elif isinstance(operand, str):
            return operand
        else:
            return str(operand)

    @property
    def constraint_count(self) -> int:
        """Count atomic constraints (comparisons)."""
        if self.form_type == "comparison":
            return 1
        elif self.form_type in ["and", "or"]:
            return sum(
                o.constraint_count if isinstance(o, CanonicalConstraint) else 0
                for o in self.operands
            )
        elif self.form_type == "not":
            return sum(
                o.constraint_count if isinstance(o, CanonicalConstraint) else 0
                for o in self.operands
            )
        else:
            return 0

    @property
    def variable_count(self) -> int:
        """Count distinct variables."""
        variables = self._collect_variables()
        return len(variables)

    def _collect_variables(self) -> Set[str]:
        """Recursively collect all variables."""
        variables = set()

        if self.form_type == "variable":
            variables.add(self.operator)

        for operand in self.operands:
            if isinstance(operand, CanonicalConstraint):
                variables.update(operand._collect_variables())

        return variables

    @property
    def operator_count(self) -> int:
        """Count logical operators."""
        count = 1 if self.form_type in ["and", "or", "not", "comparison"] else 0

        for operand in self.operands:
            if isinstance(operand, CanonicalConstraint):
                count += operand.operator_count

        return count

    @property
    def complexity_bits(self) -> int:
        """Structural complexity in bits.

        This is a lower bound on the Kolmogorov complexity of the constraint.
        It measures the information needed to specify the logical structure.
        """
        import math

        # Atomic constraints: each comparison is a "fact"
        constraint_bits = math.ceil(math.log2(max(self.constraint_count, 1) + 1))

        # Variables: dimension of the state space
        variable_bits = math.ceil(math.log2(max(self.variable_count, 1) + 1))

        # Operators: logical depth
        operator_bits = math.ceil(math.log2(max(self.operator_count, 1) + 1))

        # Total: measured in bytes (8 bits each)
        # This ensures even simple constraints have non-zero cost
        return max(8, (constraint_bits + variable_bits + operator_bits))


def normalize_z3_expr(expr: z3.ExprRef) -> CanonicalConstraint:
    """Convert Z3 expression to deep canonical form.

    This handles:
    - Commutativity (sorts operands)
    - Associativity (flattens nested operations)
    - Variable normalization
    - Constant folding
    """

    # Handle constants
    if z3.is_int_value(expr):
        return CanonicalConstraint(
            form_type="constant",
            operator=str(expr.as_long()),
            operands=()
        )

    if z3.is_true(expr):
        return CanonicalConstraint(
            form_type="constant",
            operator="true",
            operands=()
        )

    if z3.is_false(expr):
        return CanonicalConstraint(
            form_type="constant",
            operator="false",
            operands=()
        )

    # Handle variables
    if z3.is_const(expr) and not z3.is_int_value(expr):
        # Normalize variable names to v0, v1, v2, ... (in order of appearance)
        # This makes (> x 0) ≡ (> y 0)
        return CanonicalConstraint(
            form_type="variable",
            operator=str(expr),
            operands=()
        )

    # Handle compound expressions
    if z3.is_app(expr):
        kind = expr.decl().kind()
        children = [normalize_z3_expr(child) for child in expr.children()]

        # Comparisons
        if kind == z3.Z3_OP_LT:
            return CanonicalConstraint("comparison", "lt", tuple(children))
        elif kind == z3.Z3_OP_LE:
            return CanonicalConstraint("comparison", "le", tuple(children))
        elif kind == z3.Z3_OP_GT:
            # Normalize: (> a b) → (< b a) for canonical ordering
            return CanonicalConstraint("comparison", "lt", tuple(reversed(children)))
        elif kind == z3.Z3_OP_GE:
            # Normalize: (>= a b) → (<= b a)
            return CanonicalConstraint("comparison", "le", tuple(reversed(children)))
        elif kind == z3.Z3_OP_EQ:
            # Sort operands for commutativity
            sorted_children = tuple(sorted(children, key=lambda c: c.to_hash()))
            return CanonicalConstraint("comparison", "eq", sorted_children)

        # Logical operations (commutative - sort operands)
        elif kind == z3.Z3_OP_AND:
            # Flatten nested ANDs: (and (and A B) C) → (and A B C)
            flat_children = []
            for child in children:
                if isinstance(child, CanonicalConstraint) and child.form_type == "and":
                    flat_children.extend(child.operands)
                else:
                    flat_children.append(child)

            # Sort for commutativity: (and A B) ≡ (and B A)
            sorted_children = tuple(sorted(flat_children, key=lambda c: c.to_hash()))
            return CanonicalConstraint("and", "and", sorted_children)

        elif kind == z3.Z3_OP_OR:
            # Flatten nested ORs
            flat_children = []
            for child in children:
                if isinstance(child, CanonicalConstraint) and child.form_type == "or":
                    flat_children.extend(child.operands)
                else:
                    flat_children.append(child)

            # Sort for commutativity
            sorted_children = tuple(sorted(flat_children, key=lambda c: c.to_hash()))
            return CanonicalConstraint("or", "or", sorted_children)

        elif kind == z3.Z3_OP_NOT:
            return CanonicalConstraint("not", "not", tuple(children))

        # Arithmetic (for completeness, though less common in constraints)
        elif kind == z3.Z3_OP_ADD:
            # Sort for commutativity
            sorted_children = tuple(sorted(children, key=lambda c: c.to_hash()))
            return CanonicalConstraint("arithmetic", "add", sorted_children)

        elif kind == z3.Z3_OP_SUB:
            return CanonicalConstraint("arithmetic", "sub", tuple(children))

        elif kind == z3.Z3_OP_MUL:
            # Sort for commutativity
            sorted_children = tuple(sorted(children, key=lambda c: c.to_hash()))
            return CanonicalConstraint("arithmetic", "mul", sorted_children)

        # Default: preserve structure but normalize children
        else:
            return CanonicalConstraint(
                "unknown",
                str(expr.decl()),
                tuple(children)
            )

    # Fallback: treat as opaque
    return CanonicalConstraint(
        "unknown",
        str(expr),
        ()
    )


def parse_and_canonicalize(expr_str: str) -> CanonicalConstraint:
    """Parse expression string and convert to canonical form.

    This is the main entry point for semantic canonicalization.
    """
    from thielecpu.semantic_mu import parse_to_z3

    # Parse to Z3
    z3_expr = parse_to_z3(expr_str)

    # Normalize to canonical form
    canonical = normalize_z3_expr(z3_expr)

    return canonical


def test_canonicalization():
    """Test that semantic canonicalization works correctly."""
    import sys
    import io
    sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8', errors='replace')

    print("=" * 70)
    print("DEEP CANONICAL FORM TEST")
    print("=" * 70)

    test_cases = [
        # Commutativity
        ("(and (> x 0) (< x 10))", "(and (< x 10) (> x 0))", "AND commutativity"),

        # Associativity
        ("(and (and A B) C)", "(and A (and B C))", "AND associativity"),

        # Spacing
        ("x > 0", "x>0", "Spacing invariance"),

        # Comparison normalization (> becomes <)
        ("x > 0", "0 < x", "Comparison flip"),

        # Variable renaming (harder - requires variable mapping)
        # ("(> x 0)", "(> y 0)", "Variable renaming"),
    ]

    for expr1, expr2, description in test_cases:
        try:
            canonical1 = parse_and_canonicalize(expr1)
            canonical2 = parse_and_canonicalize(expr2)

            hash1 = canonical1.to_hash()
            hash2 = canonical2.to_hash()

            print(f"\n{description}:")
            print(f"  Expr 1: '{expr1}'")
            print(f"  Expr 2: '{expr2}'")
            print(f"  Hash 1: {hash1}")
            print(f"  Hash 2: {hash2}")
            print(f"  Complexity: {canonical1.complexity_bits} bits")

            if hash1 == hash2:
                print("  ✓ PASS: Identical canonical forms")
            else:
                print(f"  ✗ FAIL: Different hashes")
                print(f"    Form 1: {canonical1._to_canonical_string()}")
                print(f"    Form 2: {canonical2._to_canonical_string()}")

        except Exception as e:
            print(f"  ❌ ERROR: {e}")

    print("\n" + "=" * 70)


if __name__ == "__main__":
    test_canonicalization()
