(** NecFPaperToys: the paper board of the toll chapter, and the strip
    machine's infinity, as checked statements.

    - The board: two boxes, NO and YES, and four moves. STAY and WORK leave
      the state alone and cost nothing; VOUCH moves NO to YES and costs one;
      CHECK leaves the state alone and costs nothing. It is a certification
      system ([nec_f_board_cs]). Raw observation is free: STAY, WORK and CHECK
      never move the reading and cost zero ([nec_f_board_raw_free]). The floor
      is one and it is reached: every run from NO to YES costs at least one
      ([nec_f_board_floor]), and the run [VOUCH] costs exactly one, so no
      hypothesis about the end state beyond its reading raises the bound
      ([nec_f_board_floor_flat]). Nothing makes the crossing wait for a
      check: [VOUCH] crosses from NO with one mark and no CHECK before it,
      and so does [CHECK; VOUCH] ([nec_f_board_no_wait]).
    - The history machine of PermanentCertification.v, which keeps every
      step, has no finite list of all its states ([nec_f_history_infinite]). *)

From Coq Require Import List Arith Lia.
Import ListNotations.
From Kernel Require Import UniversalCertificationCost.
From Kernel Require Import PermanentCertification.

(** * The board *)

Inductive nec_f_box : Type := NO | YES.
Inductive nec_f_board_move : Type := STAY | WORK | VOUCH | CHECK.

Definition nec_f_board_step (s : nec_f_box) (m : nec_f_board_move) : nec_f_box :=
  match m with VOUCH => YES | _ => s end.

Definition nec_f_board_cost (m : nec_f_board_move) : nat :=
  match m with VOUCH => 1 | _ => 0 end.

Definition nec_f_board_read (s : nec_f_box) : bool := match s with NO => false | YES => true end.

Lemma nec_f_board_toll : forall s m,
  nec_f_board_read s = false -> nec_f_board_read (nec_f_board_step s m) = true ->
  nec_f_board_cost m >= 1.
Proof. intros [] []; simpl; intros; try discriminate; lia. Qed.

Definition nec_f_board_cs : CertificationSystem :=
  mk_cert_system nec_f_box nec_f_board_move nec_f_board_step nec_f_board_cost
                 nec_f_board_read nec_f_board_toll.

Theorem nec_f_board_raw_free : forall s m, m <> VOUCH ->
  nec_f_board_step s m = s /\ nec_f_board_cost m = 0.
Proof. intros s [] H; try (split; reflexivity). contradiction H; reflexivity. Qed.

Theorem nec_f_board_floor : forall tr,
  nec_f_board_read (cs_run nec_f_board_cs tr NO) = true ->
  cs_total_cost nec_f_board_cs tr >= 1.
Proof. intros tr H. exact (universal_nfi_any_substrate nec_f_board_cs tr NO eq_refl H). Qed.

Theorem nec_f_board_floor_flat : forall P : nec_f_box -> Prop,
  P YES ->
  exists tr, P (cs_run nec_f_board_cs tr NO) /\
             nec_f_board_read (cs_run nec_f_board_cs tr NO) = true /\
             cs_total_cost nec_f_board_cs tr = 1.
Proof. intros P HP. exists [VOUCH]. split; [exact HP | split; reflexivity]. Qed.

Theorem nec_f_board_no_wait :
  cs_run nec_f_board_cs [VOUCH] NO = YES /\ cs_total_cost nec_f_board_cs [VOUCH] = 1 /\
  ~ In CHECK [VOUCH] /\
  cs_run nec_f_board_cs [CHECK; VOUCH] NO = YES /\ cs_total_cost nec_f_board_cs [CHECK; VOUCH] = 1.
Proof. repeat split; simpl; try reflexivity. intros [H | []]. discriminate. Qed.

(** * The history machine is infinite *)

Theorem nec_f_history_infinite : ~ exists all : list (list bool), finite_states all.
Proof.
  intros [all [_ Hall]].
  set (M := list_max (map (@length bool) all)).
  assert (Hin : In (repeat true (S M)) all) by apply Hall.
  assert (Hle : length (repeat true (S M)) <= M).
  { assert (Hf : Forall (fun k => k <= M) (map (@length bool) all)) by (apply list_max_le; lia).
    rewrite Forall_forall in Hf. apply Hf. apply in_map. exact Hin. }
  rewrite repeat_length in Hle. lia.
Qed.

Print Assumptions nec_f_board_raw_free.
Print Assumptions nec_f_board_floor.
Print Assumptions nec_f_board_floor_flat.
Print Assumptions nec_f_board_no_wait.
Print Assumptions nec_f_history_infinite.
