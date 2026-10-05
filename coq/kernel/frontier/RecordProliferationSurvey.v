(** SCOPE NOTE: standalone proof scope. These measurements concern fixed
    observer maps, not a machine's semantics or real-system security.

    Measurements over the observer maps and the event-swap check. *)

From Coq Require Import List Lia Bool.
Import ListNotations.
From Kernel Require Import RecordProliferationSurveyTarget.
From Kernel Require Import PointerObservable PointerObservableReductions
  PointerObservableCounterexamples.

Theorem twelve_candidate_measurements_checked :
  twelve_candidate_measurements.
Proof.
  destruct PoS_model_unique_pointer as [Hpos Hposr].
  pose proof (Forall_inv Hposr) as Hwork.
  destruct Gas_model_unique_pointer as [Hgas Hgasr].
  pose proof (Forall_inv Hgasr) as Hscratch.
  destruct TEE_model_unique_pointer as [Htee Hteer].
  pose proof (Forall_inv Hteer) as Hnoise.
  destruct CT_model_unique_pointer as [Hct Hctr].
  pose proof (Forall_inv Hctr) as Hctwork.
  destruct PCC_model_unique_pointer as [Hpcc Hpccr].
  pose proof (Forall_inv Hpccr) as Hpccwork.
  exact (conj Hpos
    (conj Hwork
    (conj Hgas
    (conj Hscratch
    (conj Htee
    (conj Hnoise
    (conj Hct
    (conj Hctwork
    (conj Hpcc
    (conj Hpccwork
    (conj SymmetricMAC.mac_model_not_proliferating
          DigitalSignature.signature_model_proliferating))))))))))).
Qed.

Lemma first_event_not_proliferating :
  ~ redundantly_proliferating swap_ecosystem first_event.
Proof.
  intro H. specialize (H 0 ltac:(simpl; lia)
    {| swap_first := true; swap_second := false |}).
  unfold first_event in H. simpl in H.
  destruct H as [Hforward _]. specialize (Hforward eq_refl). discriminate.
Qed.

Theorem swapped_event_is_pointer_checked : swapped_event_is_pointer.
Proof.
  split.
  - intros i Hi s. unfold second_event. simpl. reflexivity.
  - constructor; [exact first_event_not_proliferating | constructor].
Qed.

Print Assumptions twelve_candidate_measurements_checked.
Print Assumptions first_event_not_proliferating.
Print Assumptions swapped_event_is_pointer_checked.
