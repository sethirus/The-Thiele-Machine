(** Redirect every exit of an alternate Minsky program through a constructive
    epilogue that moves counter zero into a fresh final counter. *)

From Coq Require Import Arith Lia List.
Import ListNotations.
From Undecidability.Shared.Libs.DLW.Vec Require Import pos vec.
From Undecidability.Shared.Libs.DLW.Code Require Import subcode sss.
From Undecidability.MinskyMachines Require Import MM MMA.

Definition mma_in_pc (len pc : nat) : bool :=
  (1 <=? pc) && (pc <? 1 + len).

Definition mma_exit_link (len pc : nat) : nat :=
  if mma_in_pc len pc then pc else 1 + len.

Lemma mma_exit_link_inside : forall len pc,
  1 <= pc < 1 + len -> mma_exit_link len pc = pc.
Proof.
  intros len pc H. unfold mma_exit_link, mma_in_pc.
  assert ((1 <=? pc) = true) as Hlo by (apply Nat.leb_le; lia).
  assert ((pc <? 1 + len) = true) as Hhi by (apply Nat.ltb_lt; lia).
  rewrite Hlo, Hhi. reflexivity.
Qed.

Lemma mma_exit_link_outside : forall len pc,
  pc < 1 \/ 1 + len <= pc -> mma_exit_link len pc = 1 + len.
Proof.
  intros len pc [H|H]; unfold mma_exit_link, mma_in_pc.
  - assert ((1 <=? pc) = false) as Hlo by (apply Nat.leb_gt; lia).
    rewrite Hlo. reflexivity.
  - destruct (1 <=? pc) eqn:E; [|reflexivity].
    assert ((pc <? 1 + len) = false) as Hhi by (apply Nat.ltb_ge; lia).
    rewrite Hhi. reflexivity.
Qed.

Lemma mma_exit_link_next : forall len pc,
  1 <= pc < 1 + len -> mma_exit_link len (S pc) = S pc.
Proof.
  intros len pc H. destruct (Nat.eq_dec (S pc) (1 + len)) as [->|Hne].
  - apply mma_exit_link_outside. right. lia.
  - apply mma_exit_link_inside. lia.
Qed.

Lemma mma_exit_link_one : forall len, mma_exit_link len 1 = 1.
Proof.
  intros [|len].
  - apply mma_exit_link_outside. right. lia.
  - apply mma_exit_link_inside. lia.
Qed.

Definition mma_lift_pos {n} (x : Fin.t n) : Fin.t (n + 1) := pos_left 1 x.
Definition mma_last_pos (n : nat) : Fin.t (n + 1) := pos_right n pos0.

Definition mma_lift_instr {n} (len : nat) (i : mm_instr (Fin.t n))
    : mm_instr (Fin.t (n + 1)) :=
  match i with
  | mm_inc x => mm_inc (mma_lift_pos x)
  | mm_dec x target => mm_dec (mma_lift_pos x) (mma_exit_link len target)
  end.

Definition mma_output_epilogue {n} (control : Fin.t (S n)) (len : nat)
    : list (mm_instr (Fin.t (S n + 1))) :=
  let start := 1 + len in
  let ctrl := mma_lift_pos control in
  let src := mma_lift_pos pos0 in
  let dst := mma_last_pos (S n) in
  [ mm_dec ctrl start;
    mm_inc ctrl;
    mm_dec ctrl (start + 7);
    mm_inc ctrl;
    mm_inc dst;
    mm_inc ctrl;
    mm_dec ctrl (start + 7);
    mm_dec src (start + 4) ].

Definition mma_with_output {n} (control : Fin.t (S n))
    (p : list (mm_instr (Fin.t (S n))))
    : list (mm_instr (Fin.t (S n + 1))) :=
  map (mma_lift_instr (length p)) p ++ mma_output_epilogue control (length p).

Definition mma_extend_vec {n} (v : vec nat n) (out : nat) : vec nat (n + 1) :=
  vec_app v (out ## vec_nil).

Lemma mma_extend_vec_old : forall n (v : vec nat n) out x,
  vec_pos (mma_extend_vec v out) (mma_lift_pos x) = vec_pos v x.
Proof. intros. unfold mma_extend_vec, mma_lift_pos. apply vec_pos_app_left. Qed.

Lemma mma_extend_vec_last : forall n (v : vec nat n) out,
  vec_pos (mma_extend_vec v out) (mma_last_pos n) = out.
Proof. intros. unfold mma_extend_vec, mma_last_pos. rewrite vec_pos_app_right. reflexivity. Qed.

Lemma mma_extend_vec_change : forall n (v : vec nat n) out x value,
  vec_change (mma_extend_vec v out) (mma_lift_pos x) value =
  mma_extend_vec (vec_change v x value) out.
Proof.
  intros. unfold mma_extend_vec, mma_lift_pos. apply vec_change_app_left.
Qed.

Lemma mma_lift_instr_step : forall n len (i : mm_instr (Fin.t n))
    pc v pc' v' out,
  1 <= pc < 1 + len ->
  @mma_sss n i (pc, v) (pc', v') ->
  @mma_sss (n + 1) (mma_lift_instr len i)
    (pc, mma_extend_vec v out)
    (mma_exit_link len pc', mma_extend_vec v' out).
Proof.
  intros n len i pc v pc' v' out Hpc Hstep.
  inversion Hstep; subst; cbn [mma_lift_instr].
  - rewrite mma_exit_link_next by exact Hpc.
    rewrite <- mma_extend_vec_change.
    rewrite <- (@mma_extend_vec_old n v out x). apply in_mma_sss_inc.
  - rewrite mma_exit_link_next by exact Hpc.
    apply in_mma_sss_dec_0. rewrite mma_extend_vec_old. assumption.
  - rewrite <- mma_extend_vec_change.
    apply in_mma_sss_dec_1 with (u := u).
    rewrite mma_extend_vec_old. assumption.
Qed.

Lemma mma_output_epilogue_length : forall n (control : Fin.t (S n)) len,
  length (@mma_output_epilogue n control len) = 8.
Proof. reflexivity. Qed.

Lemma mma_with_output_length : forall n (control : Fin.t (S n)) p,
  length (@mma_with_output n control p) = length p + 8.
Proof.
  intros. unfold mma_with_output. rewrite app_length, map_length,
    mma_output_epilogue_length. lia.
Qed.

Lemma mma_with_output_nth_main : forall n (control : Fin.t (S n)) p a i,
  nth_error p a = Some i ->
  nth_error (mma_with_output control p) a =
    Some (mma_lift_instr (length p) i).
Proof.
  intros n control p a i Hi. unfold mma_with_output.
  rewrite nth_error_app1.
  - rewrite nth_error_map, Hi. reflexivity.
  - rewrite map_length. apply nth_error_Some. rewrite Hi. discriminate.
Qed.

Lemma mma_with_output_nth_epilogue : forall n (control : Fin.t (S n))
    p j,
  j < 8 ->
  nth_error (mma_with_output control p) (length p + j) =
  nth_error (mma_output_epilogue control (length p)) j.
Proof.
  intros n control p j Hj. unfold mma_with_output.
  rewrite nth_error_app2 by (rewrite map_length; lia).
  rewrite map_length. replace (length p + j - length p) with j by lia.
  reflexivity.
Qed.

Lemma mma_source_control_neq : forall n,
  @mma_lift_pos (S (S n)) pos0 <> mma_lift_pos pos1.
Proof.
  intros n H. unfold mma_lift_pos in H.
  apply pos_left_inj in H. discriminate.
Qed.

Lemma mma_source_last_neq : forall n,
  @mma_lift_pos (S (S n)) pos0 <> mma_last_pos (S (S n)).
Proof. intros. apply pos_left_right_neq. Qed.

Lemma mma_control_last_neq : forall n,
  @mma_lift_pos (S (S n)) pos1 <> mma_last_pos (S (S n)).
Proof. intros. apply pos_left_right_neq. Qed.

Definition mma_epi_obs n (w : vec nat (S (S n) + 1))
    (source control output : nat) : Prop :=
  vec_pos w (@mma_lift_pos (S (S n)) pos0) = source /\
  vec_pos w (@mma_lift_pos (S (S n)) pos1) = control /\
  vec_pos w (mma_last_pos (S (S n))) = output.

Lemma mma_epi_change_source : forall n w source control output source',
  mma_epi_obs n w source control output ->
  mma_epi_obs n
    (vec_change w (@mma_lift_pos (S (S n)) pos0) source')
    source' control output.
Proof.
  intros n w source control output source' (Hs & Hc & Ho).
  unfold mma_epi_obs. split.
  - apply vec_change_eq. reflexivity.
  - split; rewrite vec_change_neq; auto using mma_source_control_neq,
      mma_source_last_neq.
Qed.

Lemma mma_epi_change_control : forall n w source control output control',
  mma_epi_obs n w source control output ->
  mma_epi_obs n
    (vec_change w (@mma_lift_pos (S (S n)) pos1) control')
    source control' output.
Proof.
  intros n w source control output control' (Hs & Hc & Ho).
  unfold mma_epi_obs. split.
  - rewrite vec_change_neq; auto. intro Heq.
    exact (mma_source_control_neq n (eq_sym Heq)).
  - split.
    + apply vec_change_eq. reflexivity.
    + rewrite vec_change_neq; auto using mma_control_last_neq.
Qed.

Lemma mma_epi_change_output : forall n w source control output output',
  mma_epi_obs n w source control output ->
  mma_epi_obs n
    (vec_change w (mma_last_pos (S (S n))) output')
    source control output'.
Proof.
  intros n w source control output output' (Hs & Hc & Ho).
  unfold mma_epi_obs. split.
  - rewrite vec_change_neq; auto. intro Heq.
    exact (mma_source_last_neq n (eq_sym Heq)).
  - split.
    + rewrite vec_change_neq; auto. intro Heq.
      exact (mma_control_last_neq n (eq_sym Heq)).
    + apply vec_change_eq. reflexivity.
Qed.

Lemma sss_step_from_nth : forall (X : Set) data
    (step : X -> (nat * data) -> (nat * data) -> Prop)
    p a i d final,
  nth_error p a = Some i ->
  step i (S a, d) final ->
  sss_step step (1, p) (S a, d) final.
Proof.
  intros X data step p a i d final Hi Hstep.
  apply nth_error_split in Hi. destruct Hi as (left & right & -> & Hlen).
  eapply in_sss_step with (l := left) (r := right); [cbn; lia|exact Hstep].
Qed.

Lemma mma_epilogue_step : forall n p j i w final,
  j < 8 ->
  nth_error (@mma_output_epilogue (S n) pos1 (length p)) j = Some i ->
  @mma_sss (S (S n) + 1) i (1 + length p + j, w) final ->
  sss_step (@mma_sss (S (S n) + 1))
    (1, @mma_with_output (S n) pos1 p)
    (1 + length p + j, w) final.
Proof.
  intros n p j i w final Hj Hi Hstep.
  apply (@sss_step_from_nth _ _ (@mma_sss (S (S n) + 1))
    (@mma_with_output (S n) pos1 p) (length p + j) i w final).
  - rewrite mma_with_output_nth_epilogue by exact Hj. exact Hi.
  - replace (S (length p + j)) with (1 + length p + j) by lia.
    exact Hstep.
Qed.

Lemma mma_epi_clear_positive : forall n p w source control output,
  mma_epi_obs n w source (S control) output ->
  sss_step (@mma_sss (S (S n) + 1))
    (1, @mma_with_output (S n) pos1 p)
    (1 + length p, w)
    (1 + length p,
      vec_change w (@mma_lift_pos (S (S n)) pos1) control) /\
  mma_epi_obs n
    (vec_change w (@mma_lift_pos (S (S n)) pos1) control)
    source control output.
Proof.
  intros n p w source control output Hobs. split.
  - assert (Hraw : sss_step (@mma_sss (S (S n) + 1))
      (1, @mma_with_output (S n) pos1 p)
      (1 + length p + 0, w)
      (1 + length p,
        vec_change w (@mma_lift_pos (S (S n)) pos1) control)).
    { eapply mma_epilogue_step with (j := 0); [lia|reflexivity|].
      apply in_mma_sss_dec_1 with (u := control).
      exact (proj1 (proj2 Hobs)). }
    replace (1 + length p + 0) with (1 + length p) in Hraw by lia.
    exact Hraw.
  - apply mma_epi_change_control with (control := S control). exact Hobs.
Qed.

Lemma mma_epi_clear_zero : forall n p w source output,
  mma_epi_obs n w source 0 output ->
  sss_step (@mma_sss (S (S n) + 1))
    (1, @mma_with_output (S n) pos1 p)
    (1 + length p, w) (1 + length p + 1, w).
Proof.
  intros n p w source output Hobs.
  assert (Hraw : sss_step (@mma_sss (S (S n) + 1))
    (1, @mma_with_output (S n) pos1 p)
    (1 + length p + 0, w) (S (1 + length p + 0), w)).
  { eapply mma_epilogue_step with (j := 0); [lia|reflexivity|].
    apply in_mma_sss_dec_0. exact (proj1 (proj2 Hobs)). }
  replace (1 + length p + 0) with (1 + length p) in Hraw by lia.
  replace (S (1 + length p)) with (1 + length p + 1) in Hraw by lia.
  exact Hraw.
Qed.

Lemma mma_epi_enter_check : forall n p w source output,
  mma_epi_obs n w source 0 output ->
  exists w',
    sss_steps (@mma_sss (S (S n) + 1))
      (1, @mma_with_output (S n) pos1 p) 2
      (1 + length p + 1, w) (1 + length p + 7, w') /\
    mma_epi_obs n w' source 0 output.
Proof.
  intros n p w source output Hobs.
  set (ctrl := @mma_lift_pos (S (S n)) pos1).
  set (w1 := vec_change w ctrl 1).
  set (w2 := vec_change w1 ctrl 0).
  exists w2. split.
  - constructor 2 with (1 + length p + 2, w1).
    + eapply mma_epilogue_step with (j := 1); [lia|reflexivity|].
      replace (1 + length p + 2) with (S (1 + length p + 1)) by lia.
      unfold w1, ctrl.
      replace (vec_change w (@mma_lift_pos (S (S n)) pos1) 1) with
        (vec_change w (@mma_lift_pos (S (S n)) pos1)
          (S (vec_pos w (@mma_lift_pos (S (S n)) pos1)))) by
        (rewrite (proj1 (proj2 Hobs)); reflexivity).
      apply in_mma_sss_inc.
    + constructor 2 with (1 + length p + 7, w2).
      * eapply mma_epilogue_step with (j := 2); [lia|reflexivity|].
        apply in_mma_sss_dec_1 with (u := 0).
        unfold w1, ctrl. apply vec_change_eq. reflexivity.
      * constructor.
  - unfold w2, w1, ctrl.
    apply mma_epi_change_control with (control := 1).
    apply mma_epi_change_control with (control := 0). exact Hobs.
Qed.

Lemma mma_epi_check_zero : forall n p w output,
  mma_epi_obs n w 0 0 output ->
  sss_step (@mma_sss (S (S n) + 1))
    (1, @mma_with_output (S n) pos1 p)
    (1 + length p + 7, w) (1 + length p + 8, w).
Proof.
  intros n p w output Hobs.
  eapply mma_epilogue_step with (j := 7); [lia|reflexivity|].
  replace (1 + length p + 8) with (S (1 + length p + 7)) by lia.
  apply in_mma_sss_dec_0. exact (proj1 Hobs).
Qed.

Lemma mma_epi_check_positive : forall n p w source output,
  mma_epi_obs n w (S source) 0 output ->
  sss_step (@mma_sss (S (S n) + 1))
    (1, @mma_with_output (S n) pos1 p)
    (1 + length p + 7, w)
    (1 + length p + 4,
      vec_change w (@mma_lift_pos (S (S n)) pos0) source) /\
  mma_epi_obs n
    (vec_change w (@mma_lift_pos (S (S n)) pos0) source)
    source 0 output.
Proof.
  intros n p w source output Hobs. split.
  - eapply mma_epilogue_step with (j := 7); [lia|reflexivity|].
    apply in_mma_sss_dec_1 with (u := source). exact (proj1 Hobs).
  - apply mma_epi_change_source with (source := S source). exact Hobs.
Qed.

Lemma mma_epi_increment_output : forall n p w source output,
  mma_epi_obs n w source 0 output ->
  exists w',
    sss_steps (@mma_sss (S (S n) + 1))
      (1, @mma_with_output (S n) pos1 p) 3
      (1 + length p + 4, w) (1 + length p + 7, w') /\
    mma_epi_obs n w' source 0 (S output).
Proof.
  intros n p w source output Hobs.
  set (dst := mma_last_pos (S (S n))).
  set (ctrl := @mma_lift_pos (S (S n)) pos1).
  set (w1 := vec_change w dst (S output)).
  set (w2 := vec_change w1 ctrl 1).
  set (w3 := vec_change w2 ctrl 0).
  assert (Hobs1 : mma_epi_obs n w1 source 0 (S output)).
  { unfold w1, dst. apply mma_epi_change_output with (output := output).
    exact Hobs. }
  assert (Hobs2 : mma_epi_obs n w2 source 1 (S output)).
  { unfold w2, ctrl. apply mma_epi_change_control with (control := 0).
    exact Hobs1. }
  exists w3. split.
  - constructor 2 with (1 + length p + 5, w1).
    + eapply mma_epilogue_step with (j := 4); [lia|reflexivity|].
      replace (1 + length p + 5) with (S (1 + length p + 4)) by lia.
      unfold w1, dst.
      replace (vec_change w (mma_last_pos (S (S n))) (S output)) with
        (vec_change w (mma_last_pos (S (S n)))
          (S (vec_pos w (mma_last_pos (S (S n)))))) by
        (rewrite (proj2 (proj2 Hobs)); reflexivity).
      apply in_mma_sss_inc.
    + constructor 2 with (1 + length p + 6, w2).
      * eapply mma_epilogue_step with (j := 5); [lia|reflexivity|].
        replace (1 + length p + 6) with (S (1 + length p + 5)) by lia.
        unfold w2, ctrl.
        replace (vec_change w1 (@mma_lift_pos (S (S n)) pos1) 1) with
          (vec_change w1 (@mma_lift_pos (S (S n)) pos1)
            (S (vec_pos w1 (@mma_lift_pos (S (S n)) pos1)))) by
          (rewrite (proj1 (proj2 Hobs1)); reflexivity).
        apply in_mma_sss_inc.
      * constructor 2 with (1 + length p + 7, w3).
        -- eapply mma_epilogue_step with (j := 6); [lia|reflexivity|].
           apply in_mma_sss_dec_1 with (u := 0).
           unfold w2, ctrl. apply vec_change_eq. reflexivity.
        -- constructor.
  - unfold w3, w2, w1, ctrl, dst.
    apply mma_epi_change_control with (control := 1).
    apply mma_epi_change_control with (control := 0).
    apply mma_epi_change_output with (output := output). exact Hobs.
Qed.

Lemma mma_epi_clear_run : forall n p w source control output,
  mma_epi_obs n w source control output ->
  exists w',
    sss_compute (@mma_sss (S (S n) + 1))
      (1, @mma_with_output (S n) pos1 p)
      (1 + length p, w) (1 + length p + 1, w') /\
    mma_epi_obs n w' source 0 output.
Proof.
  intros n p w source control. revert w.
  induction control as [|control IH]; intros w output Hobs.
  - exists w. split.
    + exists 1. apply sss_steps_1.
      exact (mma_epi_clear_zero n p w source output Hobs).
    + exact Hobs.
  - destruct (mma_epi_clear_positive n p w source control output Hobs)
      as (Hone & Hnext).
    set (w1 := vec_change w (@mma_lift_pos (S (S n)) pos1) control) in *.
    destruct (IH w1 output Hnext) as (w' & (steps & Hsteps) & Hfinal).
    exists w'. split; [|exact Hfinal].
    exists (S steps). econstructor; eassumption.
Qed.

Lemma mma_epi_copy_run : forall n p source w output,
  mma_epi_obs n w source 0 output ->
  exists w',
    sss_compute (@mma_sss (S (S n) + 1))
      (1, @mma_with_output (S n) pos1 p)
      (1 + length p + 7, w) (1 + length p + 8, w') /\
    mma_epi_obs n w' 0 0 (output + source).
Proof.
  intros n p source. induction source as [|source IH]; intros w output Hobs.
  - exists w. split.
    + exists 1. apply sss_steps_1.
      exact (mma_epi_check_zero n p w output Hobs).
    + replace (output + 0) with output by lia. exact Hobs.
  - destruct (mma_epi_check_positive n p w source output Hobs)
      as (Hdec & Hdecobs).
    set (wdec := vec_change w (@mma_lift_pos (S (S n)) pos0) source) in *.
    destruct (mma_epi_increment_output n p wdec source output Hdecobs)
      as (winc & Hthree & Hincobs).
    destruct (IH winc (S output) Hincobs)
      as (w' & (tail & Htail) & Hfinal).
    exists w'. split.
    + exists (1 + 3 + tail).
      constructor 2 with (1 + length p + 4, wdec).
      * exact Hdec.
      * replace (S (S (S tail))) with (3 + tail) by lia.
        eapply sss_steps_trans; [exact Hthree|exact Htail].
    + replace (output + S source) with (S output + source) by lia.
      exact Hfinal.
Qed.

Theorem mma_output_epilogue_run : forall n p w source control output,
  mma_epi_obs n w source control output ->
  exists w',
    sss_compute (@mma_sss (S (S n) + 1))
      (1, @mma_with_output (S n) pos1 p)
      (1 + length p, w) (1 + length p + 8, w') /\
    mma_epi_obs n w' 0 0 (output + source).
Proof.
  intros n p w source control output Hobs.
  destruct (mma_epi_clear_run n p w source control output Hobs)
    as (w0 & (clear_steps & Hclear) & Hobs0).
  destruct (mma_epi_enter_check n p w0 source output Hobs0)
    as (wcheck & Henter & Hcheckobs).
  destruct (mma_epi_copy_run n p source wcheck output Hcheckobs)
    as (wfinal & (copy_steps & Hcopy) & Hfinal).
  exists wfinal. split; [|exact Hfinal].
  pose proof (sss_steps_trans Hclear Henter) as Hclear_enter.
  pose proof (sss_steps_trans Hclear_enter Hcopy) as Hall.
  exists (clear_steps + 2 + copy_steps).
  exact Hall.
Qed.

Lemma sss_step_fetch : forall (X : Set) data
    (step : X -> (nat * data) -> (nat * data) -> Prop)
    p pc d final,
  sss_step step (1, p) (pc, d) final ->
  exists a i, pc = S a /\ nth_error p a = Some i /\ step i (pc, d) final.
Proof.
  intros X data step p pc d final
    (k & left & i & right & d0 & Hcode & Hstate & Hstep).
  inversion Hcode; subst k. inversion Hstate; subst pc d0.
  exists (length left), i. split; [lia|]. split; [|exact Hstep].
  rewrite nth_error_app2 by lia.
  replace (length left - length left) with 0 by lia. reflexivity.
Qed.

Lemma mma_with_output_main_step : forall n (control : Fin.t (S n))
    p pc v final out,
  sss_step (@mma_sss (S n)) (1, p) (pc, v) final ->
  sss_step (@mma_sss (S n + 1)) (1, mma_with_output control p)
    (pc, mma_extend_vec v out)
    (mma_exit_link (length p) (fst final),
      mma_extend_vec (snd final) out).
Proof.
  intros n control p pc v [pc' v'] out Hstep.
  destruct (@sss_step_fetch _ _ (@mma_sss (S n)) p pc v (pc', v') Hstep)
    as (a & i & -> & Hi & Hinstr).
  apply (@sss_step_from_nth _ _ (@mma_sss (S n + 1))
    (mma_with_output control p) a (mma_lift_instr (length p) i)).
  - apply mma_with_output_nth_main. exact Hi.
  - eapply mma_lift_instr_step; [|exact Hinstr].
    assert (a < length p) as Ha.
    { apply nth_error_Some. rewrite Hi. discriminate. }
    lia.
Qed.

Lemma mma_with_output_main_steps : forall n (control : Fin.t (S n))
    p steps s final out,
  sss_steps (@mma_sss (S n)) (1, p) steps s final ->
  sss_steps (@mma_sss (S n + 1)) (1, mma_with_output control p) steps
    (mma_exit_link (length p) (fst s), mma_extend_vec (snd s) out)
    (mma_exit_link (length p) (fst final), mma_extend_vec (snd final) out).
Proof.
  intros n control p steps s final out Hsteps.
  induction Hsteps as [s|steps s mid final Hone Hrest IH].
  - constructor.
  - destruct s as [cur sv], mid as [next mv], final as [last fv].
    destruct (@sss_step_fetch _ _ (@mma_sss (S n)) p cur sv (next, mv) Hone)
      as (a & i & Hcur & Hi & Hinstr). subst cur.
    assert (Hinside : 1 <= S a < 1 + length p).
    { assert (a < length p) by
        (apply nth_error_Some; rewrite Hi; discriminate). lia. }
    rewrite mma_exit_link_inside by exact Hinside.
    econstructor.
    + apply mma_with_output_main_step. exact Hone.
    + exact IH.
Qed.

Lemma mma_with_output_main_compute : forall n (control : Fin.t (S n))
    p pc v pc' v' out,
  sss_compute (@mma_sss (S n)) (1, p) (pc, v) (pc', v') ->
  sss_compute (@mma_sss (S n + 1)) (1, mma_with_output control p)
    (mma_exit_link (length p) pc, mma_extend_vec v out)
    (mma_exit_link (length p) pc', mma_extend_vec v' out).
Proof.
  intros n control p pc v pc' v' out (steps & Hsteps).
  exists steps.
  exact (@mma_with_output_main_steps n control p steps
    (pc, v) (pc', v') out Hsteps).
Qed.

Theorem mma_with_output_correct : forall n p start pc final,
  sss_output (@mma_sss (S (S n))) (1, p) (1, start) (pc, final) ->
  exists target,
    sss_output (@mma_sss (S (S n) + 1))
      (1, @mma_with_output (S n) pos1 p)
      (1, mma_extend_vec start 0)
      (1 + length (@mma_with_output (S n) pos1 p), target) /\
    vec_pos target (mma_last_pos (S (S n))) = vec_pos final pos0.
Proof.
  intros n p start pc final (Hcompute & Hout).
  pose proof (mma_with_output_main_compute (S n) pos1 p
    1 start pc final 0 Hcompute) as Hmain.
  rewrite mma_exit_link_one in Hmain.
  assert (Hlink : mma_exit_link (length p) pc = 1 + length p).
  { apply mma_exit_link_outside. exact Hout. }
  rewrite Hlink in Hmain.
  assert (Hobs : mma_epi_obs n (mma_extend_vec final 0)
      (vec_pos final pos0) (vec_pos final pos1) 0).
  { unfold mma_epi_obs. rewrite !mma_extend_vec_old, mma_extend_vec_last.
    repeat split; reflexivity. }
  destruct (mma_output_epilogue_run n p (mma_extend_vec final 0)
    (vec_pos final pos0) (vec_pos final pos1) 0 Hobs)
    as (target & Hepi & Htarget).
  assert (Hend : 1 + length p + 8 =
      1 + length (@mma_with_output (S n) pos1 p)).
  { rewrite mma_with_output_length. lia. }
  rewrite Hend in Hepi.
  exists target. split.
  - split.
    + eapply sss_compute_trans; [exact Hmain|exact Hepi].
    + unfold out_code, code_start, code_end. cbn.
      lia.
  - replace (vec_pos final pos0) with (0 + vec_pos final pos0) by lia.
    exact (proj2 (proj2 Htarget)).
Qed.

Print Assumptions mma_with_output_length.
Print Assumptions mma_with_output_correct.
