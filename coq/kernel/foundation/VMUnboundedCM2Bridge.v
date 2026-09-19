(** Exact bridge to the pinned upstream two-counter machine semantics.
    Upstream addresses are one-based. A HALT at guest address zero preserves
    every upstream target, including zero, without any arithmetic remapping. *)
From Coq Require Import Arith Lia List Relations.Relation_Operators.
Import ListNotations.
From Undecidability.MinskyMachines Require Import MM2.
From Kernel Require Import VMState VMUnboundedStep VMUnboundedCM2Interpreter
  VMUnboundedCM2InterpreterProof VMUnboundedCM2Encoding VMUnboundedCM2Correctness.

Definition mm2_guest_instruction (i : mm2_instr) : CM2InstrU :=
  match i with
  | mm2_inc_a => CM2_Inc0
  | mm2_inc_b => CM2_Inc1
  | mm2_dec_a target => CM2_DecJump0 target
  | mm2_dec_b target => CM2_DecJump1 target
  end.

Definition mm2_guest_program (p : list mm2_instr) : list CM2InstrU :=
  CM2_Halt :: map mm2_guest_instruction p.

Definition mm2_guest_config (s : nat * (nat * nat)) : CM2ConfigU :=
  {| cc_pc := fst s; cc_c0 := fst (snd s); cc_c1 := snd (snd s) |}.

Definition cm2_library_config (c : CM2ConfigU) : nat * (nat * nat) :=
  (c.(cc_pc), (c.(cc_c0), c.(cc_c1))).

Lemma mm2_config_roundtrip : forall s, cm2_library_config (mm2_guest_config s) = s.
Proof. intros [pc [a b]]. reflexivity. Qed.
Lemma cm2_config_roundtrip : forall c, mm2_guest_config (cm2_library_config c) = c.
Proof. intros [pc a b]. reflexivity. Qed.

Lemma mm2_instruction_readback : forall p i pc,
  mm2_instr_at i pc p ->
  nth_error (mm2_guest_program p) pc = Some (mm2_guest_instruction i).
Proof.
  intros p i pc (left & right & -> & <-).
  change (nth_error (map mm2_guest_instruction (left ++ i :: right))
    (length left) = Some (mm2_guest_instruction i)).
  rewrite map_app.
  rewrite nth_error_app2 by (rewrite map_length; lia).
  rewrite map_length, Nat.sub_diag. reflexivity.
Qed.

Lemma mm2_atom_guest_step : forall i s s',
  mm2_atom i s s' ->
  cm2_step_instr (mm2_guest_instruction i) (mm2_guest_config s) =
    Some (mm2_guest_config s').
Proof. intros i s s' H. destruct H; reflexivity. Qed.

Lemma cm2_step_library_atom : forall i c c',
  cm2_step_instr (mm2_guest_instruction i) c = Some c' ->
  mm2_atom i (cm2_library_config c) (cm2_library_config c').
Proof.
  intros i [pc a b] [pc' a' b'] H. destruct i;
    cbn [mm2_guest_instruction cm2_step_instr cc_pc cc_c0 cc_c1] in H;
    unfold cm2_library_config; cbn [cc_pc cc_c0 cc_c1].
  - inversion H; subst. constructor.
  - inversion H; subst. constructor.
  - destruct a; cbn in H; inversion H; subst; constructor.
  - destruct b; cbn in H; inversion H; subst; constructor.
Qed.

Lemma cm2_live_instruction_origin : forall p pc i c c',
  nth_error (mm2_guest_program p) pc = Some i ->
  cm2_step_instr i c = Some c' ->
  exists original, i = mm2_guest_instruction original /\ mm2_instr_at original pc p.
Proof.
  intros p [|pc] i c c' Hnth Hstep.
  - cbn [mm2_guest_program nth_error] in Hnth. inversion Hnth; subst i.
    discriminate Hstep.
  - cbn [mm2_guest_program nth_error] in Hnth. rewrite nth_error_map in Hnth.
    destruct (nth_error p pc) as [original|] eqn:Horig; [|discriminate].
    inversion Hnth; subst i. exists original. split; [reflexivity|].
    apply nth_error_split in Horig. destruct Horig as (left & right & Hp & Hlen).
    exists left, right. split; [exact Hp|lia].
Qed.

Lemma mm2_step_guest_step : forall p s s',
  mm2_step p s s' ->
  exists i, nth_error (mm2_guest_program p) (fst s) = Some i /\
    cm2_step_instr i (mm2_guest_config s) = Some (mm2_guest_config s').
Proof.
  intros p s s' (i & Hat & Hatom). exists (mm2_guest_instruction i). split.
  - apply mm2_instruction_readback. exact Hat.
  - apply mm2_atom_guest_step. exact Hatom.
Qed.

Lemma cm2_step_library_step : forall p c i c',
  nth_error (mm2_guest_program p) c.(cc_pc) = Some i ->
  cm2_step_instr i c = Some c' ->
  mm2_step p (cm2_library_config c) (cm2_library_config c').
Proof.
  intros p c i c' Hnth Hstep.
  destruct (cm2_live_instruction_origin _ _ _ _ _ Hnth Hstep) as (original & -> & Hat).
  exists original. split; [exact Hat|]. apply cm2_step_library_atom. exact Hstep.
Qed.

Lemma cm2_run_transitive : forall p c1 c2 c3,
  cm2_run p c1 c2 -> cm2_run p c2 c3 -> cm2_run p c1 c3.
Proof.
  intros p c1 c2 c3 H12 H23. induction H12; [exact H23|].
  econstructor; eauto.
Qed.

Lemma mm2_reach_guest_run : forall p s s',
  clos_refl_trans _ (mm2_step p) s s' ->
  cm2_run (mm2_guest_program p) (mm2_guest_config s) (mm2_guest_config s').
Proof.
  intros p s s' H. induction H.
  - destruct (mm2_step_guest_step _ _ _ H) as (i & Hnth & Hstep).
    econstructor; [exact Hnth|exact Hstep|constructor].
  - constructor.
  - eapply cm2_run_transitive; eauto.
Qed.

Lemma cm2_run_library_reach : forall p c c',
  cm2_run (mm2_guest_program p) c c' ->
  clos_refl_trans _ (mm2_step p) (cm2_library_config c) (cm2_library_config c').
Proof.
  intros p c c' H. induction H.
  - apply rt_refl.
  - eapply rt_trans; [apply rt_step; eapply cm2_step_library_step; eauto|exact IHcm2_run].
Qed.

Lemma mm2_stop_guest_halt : forall p c,
  mm2_stop p (cm2_library_config c) <->
  (nth_error (mm2_guest_program p) c.(cc_pc) = Some CM2_Halt \/
   nth_error (mm2_guest_program p) c.(cc_pc) = None).
Proof.
  intros p c. split.
  - intro Hstop. destruct (nth_error (mm2_guest_program p) c.(cc_pc)) as [i|] eqn:Hi;
      [|right; reflexivity]. destruct i; try (left; reflexivity);
      exfalso; assert (Hex : exists next, cm2_step_instr
        ltac:(match type of Hi with _ = Some ?i => exact i end) c = Some next) by
        (cbn [cm2_step_instr]; try (eexists; reflexivity);
         destruct Nat.eqb; eexists; reflexivity);
      destruct Hex as [next Hnext]; apply (Hstop (cm2_library_config next));
      eapply cm2_step_library_step; eauto.
  - intros [Hhalt|Hnone] final (i & Hat & Hatom);
      pose proof (mm2_instruction_readback _ _ _ Hat) as Hread;
      cbn [cm2_library_config fst] in Hread.
    + rewrite Hhalt in Hread. destruct i; discriminate.
    + rewrite Hnone in Hread. discriminate.
Qed.

Theorem mm2_termination_guest_iff : forall p s,
  mm2_terminates p s <->
  exists final, cm2_halts (mm2_guest_program p) (mm2_guest_config s) final.
Proof.
  intros p s. split.
  - intros (final & Hreach & Hstop). exists (mm2_guest_config final).
    pose proof (mm2_reach_guest_run _ _ _ Hreach) as Hr.
    assert (Hs : mm2_stop p (cm2_library_config (mm2_guest_config final))).
    { rewrite mm2_config_roundtrip. exact Hstop. }
    apply mm2_stop_guest_halt in Hs. destruct Hs as [He|He].
    + apply cm2_halts_explicit; assumption.
    + apply cm2_halts_falloff; assumption.
  - intros (final & Hhalt). exists (cm2_library_config final).
    inversion Hhalt as [f Hr He|f Hr He]; subst f; split.
    + pose proof (cm2_run_library_reach _ _ _ Hr) as Hreach.
      rewrite mm2_config_roundtrip in Hreach. exact Hreach.
    + apply mm2_stop_guest_halt. left. exact He.
    + pose proof (cm2_run_library_reach _ _ _ Hr) as Hreach.
      rewrite mm2_config_roundtrip in Hreach. exact Hreach.
    + apply mm2_stop_guest_halt. right. exact He.
Qed.

Definition mm2_host_input (ambient : VMState) (problem : MM2_PROBLEM) : VMState :=
  let '(p, a, b) := problem in
  cm2_total_config_encoding ambient (mm2_guest_program p)
    (mm2_guest_config (1, (a, b))).

Definition cm2_host_halts (s : VMState) : Prop :=
  exists fuel, cm2_halted (run_vm_u fuel cm2_interpreter_program s).

Theorem mm2_halting_host_iff : forall ambient problem,
  MM2_HALTING problem <-> cm2_host_halts (mm2_host_input ambient problem).
Proof.
  intros ambient [[p a] b]. unfold MM2_HALTING, mm2_host_input.
  rewrite mm2_termination_guest_iff. split.
  - intros (final & Hhalt).
    apply (proj1 (cm2_uniform_interpreter_raw_correct_total ambient _ _ final)) in Hhalt.
    destruct Hhalt as (fuel & Hobs & Hresult). exists fuel. exact Hobs.
  - intros (fuel & Hobs).
    exists (cm2_result (run_vm_u fuel cm2_interpreter_program
      (cm2_total_config_encoding ambient (mm2_guest_program p)
        (mm2_guest_config (1, (a,b)))))).
    apply (proj2 (cm2_uniform_interpreter_raw_correct_total ambient _ _ _)).
    exists fuel. split; [exact Hobs|reflexivity].
Qed.
