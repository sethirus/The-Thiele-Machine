(** SCOPE NOTE: standalone proof scope. These results concern the separately
    scoped PCC fragment, not a Thiele machine's execution.

    Proved results for the PCC consumer fragment. *)

From Coq Require Import List Bool.
Import ListNotations.
From Kernel Require Import NeculaPCCTarget.

Theorem pcc_checker_accepts_iff_vc : checker_accepts_iff_vc.
Proof.
  intros limit program. induction program as [|i rest IH]; simpl.
  - split; constructor.
  - rewrite andb_true_iff, IH. split.
    + intros [Hi Hr]. constructor; assumption.
    + intros H. inversion H; subst. auto.
Qed.

Theorem pcc_certificate_implies_vc : certificate_implies_vc.
Proof.
  intros limit program certificate. induction certificate.
  - constructor.
  - constructor; assumption.
Qed.

Theorem pcc_unsafe_program_rejected : unsafe_program_rejected.
Proof. reflexivity. Qed.

Example pcc_safe_instance :
  verification_condition 2 [PRead 0; PWrite 1 7; PHalt].
Proof. repeat constructor. Qed.

Print Assumptions pcc_checker_accepts_iff_vc.
Print Assumptions pcc_certificate_implies_vc.
Print Assumptions pcc_unsafe_program_rejected.
Print Assumptions pcc_safe_instance.
