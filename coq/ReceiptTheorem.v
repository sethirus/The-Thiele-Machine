(** ReceiptTheorem.v — The Receipt Theorem in twelve lines.

    Statement: there is no total function from the strict classical
    shadow (mem, regs, pc) that recovers vm_mu on every reachable VM
    state.

    Proof: instantiate at the two witness states from
    NecessityOfMuLedger.v.  Their shadows are equal (cond 2), Trace A
    has mu = 1 (cond 4), Trace B has mu = 0 (cond 5).  Any total f
    would have to return both 1 and 0 on the same input.  Done by
    [congruence].

    Build (from coq/, after `make`):
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
