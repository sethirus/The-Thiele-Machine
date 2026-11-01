(** LatchConst.v: latch_core_honest admits the constant event,
    i.e. an "honest" record that distinguishes nothing; the neutral
    distinction clause is what rules that out. *)
From Kernel Require Import StructuralCore StructuralCoreCover StructuralCoreAnyBase RecordAxisDiscrimination.

Theorem const_latch_honest : forall B b0, b_init B b0 ->
  HonestBaseExtension (LatchCore B (fun _ => true)) B (latch_cover B (fun _ => true)).
Proof.
  intros B b0 Hb0. apply latch_core_honest. exists b0, 0. split; [exact Hb0 |].
  simpl. split; reflexivity.
Qed.

(* Its record after one step is up from EVERY start: no two starts are
   told apart. *)
Theorem const_latch_no_distinction : forall B b,
  rc_cert (LatchCore B (fun _ => true)) (rc_run (LatchCore B (fun _ => true)) 1 (b, false, 0)) = true.
Proof. intros B b. reflexivity. Qed.

Print Assumptions const_latch_honest.
Print Assumptions const_latch_no_distinction.
