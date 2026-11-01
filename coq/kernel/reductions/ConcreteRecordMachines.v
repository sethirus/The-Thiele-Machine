(** SCOPE NOTE: standalone proof scope. These outcomes are about the
    comparison machines and deliberately have no unused kernel import.

    Proved outcomes for the RAM and Janus-like cases. *)

From Coq Require Import List ZArith Lia Ring.
Import ListNotations.
From Kernel Require Import ConcreteRecordMachinesTarget.

Theorem ram_tied_overwrite_records_old_value :
  tied_overwrite_records_old_value.
Proof. intros [x record] v. reflexivity. Qed.

Theorem ram_untied_overwrite_has_no_record :
  untied_overwrite_has_no_record.
Proof. intros [x record] v. reflexivity. Qed.

Theorem janus_like_unbounded_inverse : janus_unbounded_inverse.
Proof. intros [d|d] x; unfold junbounded_step, jinverse; simpl; ring. Qed.

Theorem janus_like_bounded_inverse : janus_bounded_inverse.
Proof.
  intros modulus [d|d] x Hpositive Hrange;
    unfold jbounded_step, junbounded_step, jinverse; simpl;
    assert (Hnonzero : (modulus <> 0)%Z) by lia.
  - change (((x + d) mod modulus + - d) mod modulus = x)%Z.
    rewrite Z.add_mod_idemp_l by exact Hnonzero.
    replace (x + d + - d)%Z with x by ring.
    apply Z.mod_small. exact Hrange.
  - change (((x - d) mod modulus + d) mod modulus = x)%Z.
    rewrite Z.add_mod_idemp_l by exact Hnonzero.
    replace (x - d + d)%Z with x by ring.
    apply Z.mod_small. exact Hrange.
Qed.

Theorem ram_untied_record_not_determined_by_base :
  untied_record_not_determined_by_base.
Proof.
  exists {| rr_value := 0; rr_record := [] |},
         {| rr_value := 0; rr_record := [1] |}.
  simpl. split; [reflexivity | discriminate].
Qed.

Print Assumptions ram_tied_overwrite_records_old_value.
Print Assumptions ram_untied_overwrite_has_no_record.
Print Assumptions janus_like_unbounded_inverse.
Print Assumptions janus_like_bounded_inverse.
Print Assumptions ram_untied_record_not_determined_by_base.
