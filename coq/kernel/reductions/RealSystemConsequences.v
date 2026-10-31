(** SCOPE NOTE: standalone proof scope. These proofs close the independent
    two-state models and do not use the kernel's semantic anchors.

    Proofs of the top-five narrow consequences. *)

From Coq Require Import Bool Arith.PeanoNat.
From Kernel Require Import RealSystemConsequencesTarget.

Theorem ct_local_view_insufficient :
  ct_local_view_cannot_decide_global_consistency.
Proof.
  intros [decide H].
  pose proof (H {| ct_local_sth := 0; ct_world_consistent := true |}) as Ht.
  pose proof (H {| ct_local_sth := 0; ct_world_consistent := false |}) as Hf.
  simpl in Ht, Hf. rewrite Ht in Hf. discriminate.
Qed.

Theorem tpm_selection_binding_is_necessary :
  incomplete_quote_check_accepts_selection_mismatch.
Proof.
  exists {| signed_selection := 0; supplied_selection := 1;
            composite_digest_matches := true |}.
  simpl. split; [reflexivity | discriminate].
Qed.

Theorem weak_subjective_suffix_insufficient :
  suffix_cannot_decide_trusted_anchor.
Proof.
  intros [decide H].
  pose proof (H {| ws_local_suffix := 0; ws_trusted_anchor := true |}) as Ht.
  pose proof (H {| ws_local_suffix := 0; ws_trusted_anchor := false |}) as Hf.
  simpl in Ht, Hf. rewrite Ht in Hf. discriminate.
Qed.

Theorem wal_ack_requires_durability :
  ack_without_durable_commit_can_be_lost.
Proof.
  exists {| wal_client_ack := true; wal_commit_record_durable := false |}.
  split; reflexivity.
Qed.

Theorem audit_local_snapshot_insufficient :
  current_local_log_cannot_decide_history.
Proof.
  intros [decide H].
  pose proof (H {| audit_current_local_log := false;
                   audit_event_occurred := true |}) as Ht.
  pose proof (H {| audit_current_local_log := false;
                   audit_event_occurred := false |}) as Hf.
  simpl in Ht, Hf. rewrite Ht in Hf. discriminate.
Qed.

Print Assumptions ct_local_view_insufficient.
Print Assumptions tpm_selection_binding_is_necessary.
Print Assumptions weak_subjective_suffix_insufficient.
Print Assumptions wal_ack_requires_durability.
Print Assumptions audit_local_snapshot_insufficient.
