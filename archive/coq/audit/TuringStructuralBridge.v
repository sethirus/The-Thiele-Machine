(* Bridge the standalone tape model to the actual sliced interface.
   This is a structural theorem for each transition function delta. No
   effectivity follows for an arbitrary Coq function delta; the effective
   universal-host theorem has its own cg_presentation hypothesis. *)
From Coq Require Import List Arith.
Import ListNotations.
Require Kernel.ProperSubsumption Minimal.ThieleComplete
  Minimal.NeutralComplete Minimal.SlicedEstablishment Audit.StructuralBridge.
Module P := Kernel.ProperSubsumption.ProperSubsumption.
Module T := Minimal.ThieleComplete.
Module N := Minimal.NeutralComplete.
Module S := Minimal.SlicedEstablishment.
Module B := Audit.StructuralBridge.

Section TapeBridge.
Variable delta : P.TM_Delta.
Definition tape_next (c : P.TM_Config) : P.TM_Config :=
  match P.tm_step delta c with Some d => d | None => c end.
Definition tape_base : T.machine :=
  T.mk_machine P.TM_Config unit (fun c _ => tape_next c)
    (fun _ => 0) (fun _ => false).
Variable event : P.TM_Config -> bool.
Definition tape_lift := N.nlift tape_base unit (fun _ => event).
Definition tape_slice : S.SlicedInterface (T.m_state tape_lift)
    P.TM_Config unit unit := B.lift_as_sliced tape_base unit (fun _ => event).

Lemma tape_run_is_native : forall n c,
  T.run tape_base (repeat tt n) c = P.tm_run n delta c.
Proof.
  induction n as [|n IH]; intro c; cbn; [reflexivity|].
  change (T.run tape_base (repeat tt n) (tape_next c) =
    match P.tm_step delta c with
    | Some d => P.tm_run n delta d | None => c end).
  unfold tape_next. destruct (P.tm_step delta c) as [d|] eqn:E.
  - apply IH.
  - rewrite IH. clear IH. induction n; cbn; rewrite ?E; reflexivity.
Qed.

Theorem native_tape_runs_embed : forall n c,
  T.run tape_lift (map (@N.NBase tape_base unit) (repeat tt n))
    (B.embed tape_base c) = B.embed tape_base (P.tm_run n delta c).
Proof.
  intros. unfold tape_lift. rewrite B.full_horizontal_embedding,
    tape_run_is_native. reflexivity.
Qed.

Theorem hidden_tape_record : forall c,
  event c = true ->
  ~ exists decode : P.TM_Config -> bool,
      forall s : T.m_state tape_lift,
        decode (B.base_view tape_base s) = B.record_view tape_base s.
Proof.
  intros c H. exact (B.raised_record_cannot_be_decoded_from_base
    tape_base unit (fun _ => event) tt c H).
Qed.
End TapeBridge.

Print Assumptions tape_slice.
Print Assumptions native_tape_runs_embed.
Print Assumptions hidden_tape_record.
