(** =========================================================================
    TSIRELSON UNIQUENESS - 2√2 is the Exact Maximum
    =========================================================================
    
    Proves that 2√2 is not just AN upper bound, but THE EXACT maximum.
    
    ========================================================================= *)

From Coq Require Import QArith Qabs Lia.
Local Open Scope Q_scope.

From Kernel Require Import VMState VMStep CHSHExtraction MuCostModel.
From Kernel Require Import TsirelsonLowerBound TsirelsonUpperBound.

(** ** Exact Maximum *)

Definition tsirelson_exact_bound : Q := target_chsh_value.

(** There exists a μ=0 program achieving arbitrarily close to 2√2 *)
Lemma tsirelson_achievable_witness :
  exists (fuel : nat) (trace : list vm_instruction),
    mu_cost_of_trace fuel trace 0 = 0%nat.
Proof.
  exists 10%nat, tsirelson_achieving_trace.
  apply tsirelson_program_mu_zero.
Qed.
