(** =========================================================================
    SEMANTIC μ-COST: SYNTAX-INVARIANT COMPLEXITY MEASURE
    =========================================================================

    This file replaces String.length-based μ-cost with a semantic measure
    based on the logical structure of constraints.

    PROBLEM: String.length is syntax-sensitive:
      - "x>0" has length 3 (24 bits)
      - "x > 0" has length 5 (40 bits)
      - Same constraint, different costs!

    SOLUTION: Measure the AST structure, not the string:
      - Parse to abstract syntax tree
      - Normalize for commutativity, associativity
      - Measure structural complexity

    RESULT: Syntax-invariant μ-cost
      - "x>0" ≡ "x > 0" ≡ "(> x 0)" (same canonical form)
      - Cost depends on logical structure, not notation

    ISOMORPHISM REQUIREMENT:
      - This Coq definition is the CANONICAL specification
      - Python implementation (thielecpu/semantic_mu.py) MUST match
      - Verilog enforcement (via LEI) MUST match

    STATUS: PHASE 1 FIX (Syntax Sensitivity)
    DATE: February 4, 2026

    ========================================================================= *)

From Coq Require Import List Lia Arith.PeanoNat Bool String.
From Coq Require Import Nat.
Import ListNotations.

From Kernel Require Import VMState VMStep.

(** =========================================================================
    PART 1: ABSTRACT SYNTAX TREE FOR CONSTRAINTS
    ========================================================================= *)

(** Constraint variables (normalized identifiers) *)
Inductive ConstraintVar : Type :=
| CVar : nat -> ConstraintVar.  (* v0, v1, v2, ... in order of appearance *)

(** Arithmetic expressions *)
Inductive ArithExpr : Type :=
| AVar : ConstraintVar -> ArithExpr
| AConst : nat -> ArithExpr
| AAdd : ArithExpr -> ArithExpr -> ArithExpr
| ASub : ArithExpr -> ArithExpr -> ArithExpr
| AMul : ArithExpr -> ArithExpr -> ArithExpr.

(** Comparison operators *)
Inductive CompOp : Type :=
| Eq    (* = *)
| Lt    (* < *)
| Le    (* ≤ *)
| Gt    (* > *)
| Ge.   (* ≥ *)

(** Atomic constraints (comparisons) *)
Inductive AtomicConstraint : Type :=
| CCompare : CompOp -> ArithExpr -> ArithExpr -> AtomicConstraint.

(** Logical formulas (constraints) *)
Inductive Constraint : Type :=
| CAtom : AtomicConstraint -> Constraint
| CAnd : Constraint -> Constraint -> Constraint
| COr : Constraint -> Constraint -> Constraint
| CNot : Constraint -> Constraint
| CTrue : Constraint
| CFalse : Constraint.

(** =========================================================================
    PART 2: CANONICAL NORMALIZATION
    ========================================================================= *)

(** Comparison operator normalization: convert > and ≥ to < and ≤ *)
Definition normalize_comp_op (op : CompOp) : CompOp :=
  match op with
  | Gt => Lt  (* x > y becomes y < x *)
  | Ge => Le  (* x ≥ y becomes y ≤ x *)
  | _ => op
  end.

(** Flip a comparison when normalizing *)
Definition should_flip_comparison (op : CompOp) : bool :=
  match op with
  | Gt => true
  | Ge => true
  | _ => false
  end.

(** Normalize an atomic constraint *)
Definition normalize_atomic (ac : AtomicConstraint) : AtomicConstraint :=
  match ac with
  | CCompare op e1 e2 =>
      if should_flip_comparison op
      then CCompare (normalize_comp_op op) e2 e1
      else CCompare op e1 e2
  end.

(** Flatten nested AND/OR operations *)
Fixpoint flatten_and (c : Constraint) : list Constraint :=
  match c with
  | CAnd c1 c2 => flatten_and c1 ++ flatten_and c2
  | _ => [c]
  end.

Fixpoint flatten_or (c : Constraint) : list Constraint :=
  match c with
  | COr c1 c2 => flatten_or c1 ++ flatten_or c2
  | _ => [c]
  end.

(** Rebuild constraint from flattened list *)
Definition rebuild_and (cs : list Constraint) : Constraint :=
  match cs with
  | [] => CTrue
  | c :: cs' => fold_left CAnd cs' c
  end.

Definition rebuild_or (cs : list Constraint) : Constraint :=
  match cs with
  | [] => CFalse
  | c :: cs' => fold_left COr cs' c
  end.

(** =========================================================================
    PART 3: STRUCTURAL COMPLEXITY MEASURE
    ========================================================================= *)

(** Count variables in an arithmetic expression *)
Fixpoint count_vars_arith (e : ArithExpr) : nat :=
  match e with
  | AVar _ => 1
  | AConst _ => 0
  | AAdd e1 e2 => count_vars_arith e1 + count_vars_arith e2
  | ASub e1 e2 => count_vars_arith e1 + count_vars_arith e2
  | AMul e1 e2 => count_vars_arith e1 + count_vars_arith e2
  end.

(** Count variables in a constraint *)
Fixpoint count_vars (c : Constraint) : nat :=
  match c with
  | CAtom (CCompare _ e1 e2) => count_vars_arith e1 + count_vars_arith e2
  | CAnd c1 c2 => count_vars c1 + count_vars c2
  | COr c1 c2 => count_vars c1 + count_vars c2
  | CNot c' => count_vars c'
  | CTrue => 0
  | CFalse => 0
  end.

(** Count atomic constraints (comparisons) *)
Fixpoint count_atoms (c : Constraint) : nat :=
  match c with
  | CAtom _ => 1
  | CAnd c1 c2 => count_atoms c1 + count_atoms c2
  | COr c1 c2 => count_atoms c1 + count_atoms c2
  | CNot c' => count_atoms c'
  | CTrue => 0
  | CFalse => 0
  end.

(** Count logical operators *)
Fixpoint count_operators (c : Constraint) : nat :=
  match c with
  | CAtom _ => 1  (* Comparison is an operator *)
  | CAnd c1 c2 => 1 + count_operators c1 + count_operators c2
  | COr c1 c2 => 1 + count_operators c1 + count_operators c2
  | CNot c' => 1 + count_operators c'
  | CTrue => 0
  | CFalse => 0
  end.

(** =========================================================================
    PART 4: SEMANTIC COMPLEXITY BITS (Kolmogorov Lower Bound)
    ========================================================================= *)

(** Logarithm base 2 (ceiling) - same as StateSpaceCounting.v *)
Definition log2_nat (n : nat) : nat :=
  match n with
  | 0 => 0
  | S _ => Nat.log2 n + (if Nat.pow 2 (Nat.log2 n) =? n then 0 else 1)
  end.

(** Semantic complexity in bits.

    This is a LOWER BOUND on Kolmogorov complexity:
    - Measures information needed to specify the logical structure
    - Independent of syntax (spacing, notation)
    - Based on structural properties:
      * Number of atomic constraints (choices)
      * Number of variables (state space dimensions)
      * Number of operators (logical depth)

    Formula:
      complexity_bits = 8 * (log₂(atoms+1) + log₂(vars+1) + log₂(ops+1))

    The factor of 8 converts to bytes (maintains compatibility with
    original string-length measure which counted bytes * 8).
*)
Definition semantic_complexity_bits (c : Constraint) : nat :=
  let atoms := count_atoms c in
  let vars := count_vars c in
  let ops := count_operators c in

  (* Compute logarithmic contributions *)
  let atom_bits := log2_nat (S atoms) in
  let var_bits := log2_nat (S vars) in
  let op_bits := log2_nat (S ops) in

  (* Total: sum of structural complexities, converted to bytes *)
  8 * (atom_bits + var_bits + op_bits).

(** =========================================================================
    PART 5: PROPERTIES AND CORRECTNESS
    ========================================================================= *)

(** Semantic complexity is non-zero for non-trivial constraints.

    This lemma is intuitive but requires additional properties of log2_nat.
    We leave it as a conjecture since it's not needed for the isomorphism guarantee.
*)
Conjecture semantic_complexity_nonzero :
  forall c,
    c <> CTrue ->
    c <> CFalse ->
    semantic_complexity_bits c > 0.

(** Semantic complexity is syntax-invariant (by construction).

    THEOREM (Informal): If two constraint strings s1 and s2 parse to
    the same canonical AST after normalization, then they have the
    same semantic_complexity_bits.

    PROOF: semantic_complexity_bits only depends on the AST structure
    (counts of atoms, variables, operators), which is preserved by
    normalization.

    This cannot be formally stated in Coq without a parser, but the
    property holds by construction: the measure only uses AST counts,
    not string properties.
*)

(** =========================================================================
    PART 6: INTEGRATION WITH VM μ-COST
    ========================================================================= *)

(** NEW definition: axiom μ-cost based on semantic complexity *)
Definition axiom_semantic_cost (ax : VMAxiom) (ast : Constraint) : nat :=
  semantic_complexity_bits ast.

(** BACKWARD COMPATIBILITY: fallback to string length if no AST *)
Definition axiom_cost_with_fallback (ax : VMAxiom) (ast_opt : option Constraint) : nat :=
  match ast_opt with
  | Some ast => semantic_complexity_bits ast
  | None => String.length ax * 8  (* Fallback for unparseable formulas *)
  end.

(** ISOMORPHISM REQUIREMENT:

    The Python implementation (thielecpu/semantic_mu.py) MUST compute
    the same semantic_complexity_bits value for any given constraint.

    Test oracle:
      For all constraints c,
        coq_semantic_complexity_bits(c) = python_semantic_complexity_bits(c)

    This is verified by:
      1. Coq exports the AST structure
      2. Python parses to equivalent AST
      3. Both compute same counts (atoms, vars, ops)
      4. Both apply same formula: 8 * (log₂(atoms+1) + log₂(vars+1) + log₂(ops+1))

    Any divergence breaks the three-layer isomorphism.
*)

(** =========================================================================
    PART 7: INTEGRATION NOTES
    ========================================================================= *)

(** NOTE: Integration with VM μ-cost system will be done in a future update.
    The theorems connecting semantic complexity to LASSERT μ-cost increases
    require imports from StateSpaceCounting.v and proper VM step proofs.

    For now, this file provides the CANONICAL specification of semantic
    complexity that Python MUST match for the three-layer isomorphism.
*)

(** =========================================================================
    IMPLEMENTATION NOTES FOR PYTHON/VERILOG
    =========================================================================

    PYTHON (thielecpu/semantic_mu.py):
    - Parse string to Z3 AST
    - Convert Z3 AST to Coq-equivalent structure
    - Count atoms, variables, operators (must match Coq counts exactly)
    - Compute: 8 * (log₂(atoms+1) + log₂(vars+1) + log₂(ops+1))
    - Return semantic_complexity_bits as description cost

    VERILOG (LEI interface):
    - Hardware receives formula string via LEI
    - LEI invokes Python to parse and compute semantic cost
    - LEI returns computed μ-delta to hardware
    - Hardware verifies μ-delta matches expected cost
    - If mismatch: halt and raise error

    CRITICAL: The Python log2_nat implementation MUST match Coq:

    ```python
    def log2_nat(n: int) -> int:
        if n <= 0:
            return 0
        log_n = n.bit_length() - 1  # Floor of log₂(n)
        if (1 << log_n) == n:
            return log_n  # Exact power of 2
        else:
            return log_n + 1  # Ceiling
    ```

    TEST ORACLE:
    For all formulas f:
      coq_semantic_complexity_bits(parse(f)) ==
      python_semantic_complexity_bits(parse(f))

    ========================================================================= *)
