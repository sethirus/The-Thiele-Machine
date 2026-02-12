(** * Concrete μ-cost alignment example
    
    This file demonstrates the alignment between the Python VM μ-cost
    calculation and the Coq formalization for a specific LASSERT operation.
    
    Test case: LASSERT "x1 XOR x2"
    Expected μ-cost: 72 bits (9 characters × 8 bits/char)
*)

From Coq Require Import String ZArith Lia.
Open Scope string_scope.
Open Scope Z_scope.

(** A tiny, explicit string size function (character count). *)
Fixpoint str_size (s : string) : nat :=
  match s with
  | EmptyString => 0%nat
  | String _ rest => S (str_size rest)
  end.

(** The μ-cost formula for LASSERT: size(query) × 8 bits *)
Definition lassert_mu_cost (query : string) : Z :=
  Z.of_nat (str_size query) * 8.

(** Concrete example: "x1 XOR x2" has 9 characters *)
Definition test_clause : string := "x1 XOR x2".

(** The clause size is 9 *)
Lemma test_clause_size : str_size test_clause = 9%nat.
Proof. reflexivity. Qed.

(** Therefore the μ-cost is exactly 72 bits *)
(* ARITHMETIC — 9 * 8 = 72 *)
Theorem lassert_xor_mu_cost :
  lassert_mu_cost test_clause = 72.
Proof.
  unfold lassert_mu_cost, test_clause.
  (* String.length "x1 XOR x2" = 9 *)
  (* 9 * 8 = 72 *)
  reflexivity.
Qed.

(** General theorem: μ-cost is always 8× the query length *)
(* DEFINITIONAL — lassert_mu_cost is defined as str_size * 8 *)
Theorem lassert_mu_cost_formula :
  forall query : string,
    lassert_mu_cost query = Z.of_nat (str_size query) * 8.
Proof.
  intros query. unfold lassert_mu_cost. reflexivity.
Qed.

(** The μ-cost is always non-negative *)
(** HELPER: Non-negativity property *)
(** HELPER: Non-negativity property *)
Theorem lassert_mu_cost_nonneg :
  forall query : string,
    0 <= lassert_mu_cost query.
Proof.
  intros query. unfold lassert_mu_cost.
  apply Z.mul_nonneg_nonneg.
  - apply Nat2Z.is_nonneg.
  - lia.
Qed.

(** This matches:
    - Python VM: question_cost_bits("x1 XOR x2") = 72
    - Verilog: mu_accumulator += 72 after LASSERT
    - Coq: lassert_mu_cost "x1 XOR x2" = 72
    
    Validated by tests/alignment/test_mu_alignment.py
*)
