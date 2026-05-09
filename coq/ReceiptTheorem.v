(** * ReceiptTheorem: the Receipt Theorem in twelve lines

    Statement: no total function from the strict classical shadow
    [(mem, regs, pc)] can recover [vm_mu] on every reachable VM state.

    Proof outline. Instantiate the would-be function [f] at the two
    witness states constructed in [NecessityOfMuLedger.v]:

      - [po1_cond2_final_shadow_equal] gives [strict_shadow po1_state_A
        = strict_shadow po1_state_B].
      - [po1_cond4_trace_A_mu_paid] gives [vm_mu po1_state_A = 1].
      - [po1_cond5_trace_B_mu_zero] gives [vm_mu po1_state_B = 0].

    Any [f] satisfying [f (strict_shadow s) = vm_mu s] for both states
    would have to return both 1 and 0 on the same input. The
    contradiction is discharged by [congruence].

    Standalone build (from [coq/], after [make]):

        coqc -Q kernel Kernel -Q nofi NoFI ReceiptTheorem.v
*)

From Kernel Require Import VMState VMStep.
Require Import NecessityOfMuLedger.

Theorem ReceiptTheorem :
  ~ exists f : StrictClassicalState -> nat,
      forall s : VMState, f (strict_shadow s) = s.(vm_mu).
Proof.
  intros [f Hf].
  pose proof (Hf po1_state_A) as HA.
  pose proof (Hf po1_state_B) as HB.
  rewrite po1_cond2_final_shadow_equal in HA.
  rewrite po1_cond4_trace_A_mu_paid in HA.
  rewrite po1_cond5_trace_B_mu_zero in HB.
  congruence.
Qed.

Print Assumptions ReceiptTheorem.
