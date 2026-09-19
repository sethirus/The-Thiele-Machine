(** Effective specialization of MM2's first input, with its actual PC-1
    entry and exact two-direction terminal-result/host contracts. The prefix
    preserves the PC-0 halt sentinel by jumping over it, rather than starting
    execution at that sentinel. See SPECIALIZATION_REPAIR.md. *)

From Coq Require Import Arith Lia List.
Import ListNotations.
From Undecidability.MinskyMachines Require Import MM2.
From Kernel Require Import VMState VMUnboundedStep.
From Kernel Require Import VMUnboundedCM2Interpreter.
From Kernel Require Import VMUnboundedCM2Encoding.
From Kernel Require Import VMUnboundedCM2Correctness.
From Kernel Require Import VMUnboundedCM2Bridge.

Lemma cm2_run_trans : forall p c1 c2 c3,
  cm2_run p c1 c2 -> cm2_run p c2 c3 -> cm2_run p c1 c3.
Proof.
  intros p c1 c2 c3 H12. induction H12 as [|c i c1' c2' Hnth Hstep Htail IH]; intros H23.
  - exact H23.
  - eapply cm2_run_step; eauto.
Qed.

(** Relocate a program's own internal absolute jump targets by [base],
    leaving every other instruction unchanged.  Used only to rewrite the
    embedded targets; physical relocation within a bigger array comes from
    ordinary list concatenation, not from this map. *)
Definition shift_cm2_instr (base : nat) (i : CM2InstrU) : CM2InstrU :=
  match i with
  | CM2_Halt => CM2_Halt
  | CM2_Inc0 => CM2_Inc0
  | CM2_Inc1 => CM2_Inc1
  | CM2_DecJump0 t => CM2_DecJump0 (t + base)
  | CM2_DecJump1 t => CM2_DecJump1 (t + base)
  end.

Definition shift_cm2_program (base : nat) (p : list CM2InstrU) : list CM2InstrU :=
  map (shift_cm2_instr base) p.

Definition shift_config (base : nat) (c : CM2ConfigU) : CM2ConfigU :=
  {| cc_pc := base + c.(cc_pc); cc_c0 := c.(cc_c0); cc_c1 := c.(cc_c1) |}.

Lemma cm2_step_instr_shift : forall base i c c',
  cm2_step_instr i c = Some c' ->
  cm2_step_instr (shift_cm2_instr base i) (shift_config base c) = Some (shift_config base c').
Proof.
  intros base i [pc c0 c1] c' H. unfold shift_config, shift_cm2_instr.
  destruct i as [| | |t|t]; cbn [cm2_step_instr cc_pc cc_c0 cc_c1] in H.
  - discriminate.
  - inversion H; subst. cbn [cm2_step_instr cc_pc cc_c0 cc_c1].
    rewrite (Nat.add_succ_r base pc). reflexivity.
  - inversion H; subst. cbn [cm2_step_instr cc_pc cc_c0 cc_c1].
    rewrite (Nat.add_succ_r base pc). reflexivity.
  - assert (Hc : (c0 = 0 /\ c' = {| cc_pc := S pc; cc_c0 := 0; cc_c1 := c1 |}) \/
                 (c0 <> 0 /\ c' = {| cc_pc := t; cc_c0 := Nat.pred c0; cc_c1 := c1 |})).
    { destruct (Nat.eqb c0 0) eqn:Hz.
      - left. split; [apply Nat.eqb_eq; exact Hz|]. inversion H; reflexivity.
      - right. split; [apply Nat.eqb_neq; exact Hz|]. inversion H; reflexivity. }
    destruct Hc as [[Hc0 Hc']|[Hc0 Hc']]; subst.
    + cbn [cm2_step_instr cc_pc cc_c0 cc_c1]. rewrite (Nat.add_succ_r base pc).
      reflexivity.
    + apply Nat.eqb_neq in Hc0. cbn [cm2_step_instr cc_pc cc_c0 cc_c1]. rewrite Hc0.
      rewrite (Nat.add_comm t base). reflexivity.
  - assert (Hc : (c1 = 0 /\ c' = {| cc_pc := S pc; cc_c0 := c0; cc_c1 := 0 |}) \/
                 (c1 <> 0 /\ c' = {| cc_pc := t; cc_c0 := c0; cc_c1 := Nat.pred c1 |})).
    { destruct (Nat.eqb c1 0) eqn:Hz.
      - left. split; [apply Nat.eqb_eq; exact Hz|]. inversion H; reflexivity.
      - right. split; [apply Nat.eqb_neq; exact Hz|]. inversion H; reflexivity. }
    destruct Hc as [[Hc1 Hc']|[Hc1 Hc']]; subst.
    + cbn [cm2_step_instr cc_pc cc_c0 cc_c1]. rewrite (Nat.add_succ_r base pc).
      reflexivity.
    + apply Nat.eqb_neq in Hc1. cbn [cm2_step_instr cc_pc cc_c0 cc_c1]. rewrite Hc1.
      rewrite (Nat.add_comm t base). reflexivity.
Qed.

(** Every run of [p] embeds, shifted, into any array [P] that carries
    [shift_cm2_instr base]-rewritten [p] at absolute offset [base]. *)
Lemma cm2_run_embed : forall base P p c c',
  (forall j, nth_error P (base + j) = option_map (shift_cm2_instr base) (nth_error p j)) ->
  cm2_run p c c' ->
  cm2_run P (shift_config base c) (shift_config base c').
Proof.
  intros base P p c c' Hembed Hrun.
  induction Hrun as [c|c i c1 c2 Hnth Hstep Htail IH].
  - apply cm2_run_refl.
  - assert (HnthP : nth_error P (base + c.(cc_pc)) = Some (shift_cm2_instr base i)).
    { rewrite Hembed, Hnth. reflexivity. }
    assert (Hpc : (shift_config base c).(cc_pc) = base + c.(cc_pc)) by reflexivity.
    eapply cm2_run_step.
    + rewrite Hpc. exact HnthP.
    + apply (cm2_step_instr_shift base i c c1 Hstep).
    + exact IH.
Qed.

(** Increment to [S a], then decrement and jump to relocated PC 1.
    This restores counter 0 to [a], preserves counter 1, and retains the
    guest's PC-0 halt sentinel for subsequent jumps to zero. *)
Definition specialized_program (p : list mm2_instr) (a : nat) : list CM2InstrU :=
  repeat CM2_Inc0 (S a) ++
  CM2_DecJump0 (a + 3) :: shift_cm2_program (a + 2) (mm2_guest_program p).

Lemma cm2_run_inc0_window : forall p d k c0 c1,
  (forall j, j < d -> nth_error p (k + j) = Some CM2_Inc0) ->
  cm2_run p {| cc_pc := k; cc_c0 := c0; cc_c1 := c1 |}
             {| cc_pc := k + d; cc_c0 := c0 + d; cc_c1 := c1 |}.
Proof.
  intros p d. induction d as [|d IH]; intros k c0 c1 Hwin.
  - replace (k + 0) with k by lia. replace (c0 + 0) with c0 by lia.
    apply cm2_run_refl.
  - assert (Hi : nth_error p k = Some CM2_Inc0).
    { specialize (Hwin 0 ltac:(lia)). rewrite Nat.add_0_r in Hwin. exact Hwin. }
    eapply cm2_run_step.
    + exact Hi.
    + reflexivity.
    + assert (Hwin' : forall j, j < d -> nth_error p (S k + j) = Some CM2_Inc0).
      { intros j Hj. specialize (Hwin (S j) ltac:(lia)).
        replace (k + S j) with (S k + j) in Hwin by lia. exact Hwin. }
      specialize (IH (S k) (S c0) c1 Hwin').
      replace (S k + d) with (k + S d) in IH by lia.
      replace (S c0 + d) with (c0 + S d) in IH by lia.
      exact IH.
Qed.

Lemma specialized_program_embed : forall p a j,
  nth_error (specialized_program p a) ((a + 2) + j) =
  option_map (shift_cm2_instr (a + 2)) (nth_error (mm2_guest_program p) j).
Proof.
  intros p a j. unfold specialized_program.
  rewrite nth_error_app2 by (rewrite repeat_length; lia).
  rewrite repeat_length. replace (a + 2 + j - S a) with (S j) by lia.
  cbn [nth_error]. unfold shift_cm2_program. apply nth_error_map.
Qed.

Lemma specialized_program_preamble : forall p a b,
  cm2_run (specialized_program p a) {| cc_pc := 0; cc_c0 := 0; cc_c1 := b |}
    (shift_config (a + 2) {| cc_pc := 1; cc_c0 := a; cc_c1 := b |}).
Proof.
  intros p a b.
  assert (Hwin : forall j, j < S a ->
    nth_error (specialized_program p a) (0 + j) = Some CM2_Inc0).
  { intros j Hj. unfold specialized_program. rewrite Nat.add_0_l.
    rewrite nth_error_app1 by (rewrite repeat_length; lia).
    apply nth_error_repeat; lia. }
  pose proof (cm2_run_inc0_window (specialized_program p a) (S a) 0 0 b Hwin) as H.
  rewrite Nat.add_0_l in H.
  eapply cm2_run_trans; [exact H|].
  eapply cm2_run_step with (i := CM2_DecJump0 (a + 3)).
  - cbn [cc_pc]. unfold specialized_program.
    rewrite nth_error_app2 by (rewrite repeat_length; lia).
    rewrite repeat_length, Nat.sub_diag. reflexivity.
  - reflexivity.
  - unfold shift_config. cbn [cc_pc cc_c0 cc_c1].
    replace (a + 2 + 1) with (a + 3) by lia. constructor.
Qed.

(** Correctness of the specialization: if the original two-input guest
    program reaches [final] from (a, b), the specialized, single-input-in-
    counter-1 program reaches the corresponding shifted configuration from
    its own true start. *)
Theorem specialized_program_correct : forall p a b final,
  cm2_run (mm2_guest_program p) {| cc_pc := 1; cc_c0 := a; cc_c1 := b |} final ->
  cm2_run (specialized_program p a) {| cc_pc := 0; cc_c0 := 0; cc_c1 := b |}
    (shift_config (a + 2) final).
Proof.
  intros p a b final Hrun. eapply cm2_run_trans.
  - apply specialized_program_preamble.
  - eapply cm2_run_embed; [apply specialized_program_embed|exact Hrun].
Qed.

(** Actual host reachability for the transformed guest supplied as data
    to the same fixed VM interpreter. The remaining input is [b]; no external
    evaluator inspects the guest during the host execution. *)
Theorem specialized_program_host_correct : forall ambient p a b final,
  cm2_run (mm2_guest_program p) {| cc_pc := 1; cc_c0 := a; cc_c1 := b |} final ->
  exists fuel s',
    run_vm_u fuel cm2_interpreter_program
      (cm2_total_input_encoding ambient (specialized_program p a) 0 b) = s' /\
    cm2_rep (encode_cm2_program (cm2_encoding_width (specialized_program p a))
               (specialized_program p a))
            (cm2_encoding_width (specialized_program p a))
      (shift_config (a + 2) final) s'.
Proof.
  intros ambient p a b final Hrun.
  set (sp := specialized_program p a).
  set (width := cm2_encoding_width sp).
  destruct (cm2_uniform_interpreter_run_simulation sp width
      {| cc_pc := 0; cc_c0 := 0; cc_c1 := b |} (shift_config (a + 2) final)
      (cm2_total_input_encoding ambient sp 0 b)
      (cm2_program_fits_encoding_width sp)
      (specialized_program_correct p a b final Hrun)
      (cm2_boundary_is_rep ambient (encode_cm2_program width sp) width
        {| cc_pc := 0; cc_c0 := 0; cc_c1 := b |}))
    as [fuel [s' [Heq Hrep]]].
  exists fuel, s'. split; [exact Heq | exact Hrep].
Qed.

Lemma cm2_step_shift_exact : forall base i c,
  cm2_step_instr (shift_cm2_instr base i) (shift_config base c) =
  option_map (shift_config base) (cm2_step_instr i c).
Proof.
  intros base i c. destruct (cm2_step_instr i c) as [next|] eqn:Hs.
  - cbn. apply cm2_step_instr_shift. exact Hs.
  - destruct i; cbn [cm2_step_instr] in Hs; try discriminate;
      repeat match type of Hs with context [Nat.eqb ?x 0] => destruct (Nat.eqb x 0) end;
      try discriminate. reflexivity.
Qed.

Lemma shift_config_injective : forall base c d,
  shift_config base c = shift_config base d -> c = d.
Proof.
  intros base [pc x y] [pc' x' y'] H.
  inversion H. assert (pc = pc') by lia. subst. reflexivity.
Qed.

Lemma cm2_run_unembed : forall base P p start final,
  (forall j, nth_error P (base + j) = option_map (shift_cm2_instr base) (nth_error p j)) ->
  cm2_run P (shift_config base start) final ->
  exists original, final = shift_config base original /\ cm2_run p start original.
Proof.
  intros base P p start final Hembed Hr.
  remember (shift_config base start) as initial eqn:Heq.
  revert start Heq. induction Hr as [c|c i c1 c2 Hnth Hstep Htail IH]; intros start Heq.
  - exists start. split; [exact Heq|constructor].
  - subst c. cbn [shift_config cc_pc] in Hnth. rewrite Hembed in Hnth.
    destruct (nth_error p (cc_pc start)) as [oi|] eqn:Ho; [|discriminate].
    cbn in Hnth. inversion Hnth; subst i.
    rewrite cm2_step_shift_exact in Hstep.
    destruct (cm2_step_instr oi start) as [next|] eqn:Hnext; [|discriminate].
    cbn in Hstep. inversion Hstep; subst c1.
    destruct (IH next eq_refl) as [original [Hf Hr]].
    exists original. split; [exact Hf|]. eapply cm2_run_step; eauto.
Qed.

Lemma cm2_runs_comparable : forall p c left right,
  cm2_run p c left -> cm2_run p c right ->
  cm2_run p left right \/ cm2_run p right left.
Proof.
  intros p c left right Hl. revert right.
  induction Hl as [c|c i c1 c2 Hnth Hstep Htail IH]; intros right Hr.
  - left. exact Hr.
  - inversion Hr as [|d j d1 d2 Hnth' Hstep' Htail']; subst.
    + right. eapply cm2_run_step; eauto.
    + rewrite Hnth in Hnth'. inversion Hnth'; subst j.
      rewrite Hstep in Hstep'. inversion Hstep'; subst d1.
      apply IH. exact Htail'.
Qed.

Definition cm2_terminal (p : list CM2InstrU) (c : CM2ConfigU) : Prop :=
  nth_error p (cc_pc c) = Some CM2_Halt \/ nth_error p (cc_pc c) = None.

Lemma cm2_terminal_run : forall p c d,
  cm2_terminal p c -> cm2_run p c d -> c = d.
Proof.
  intros p c d Ht Hr. inversion Hr; subst; [reflexivity|].
  destruct Ht as [Ht|Ht]; rewrite Ht in H; inversion H; subst.
  discriminate.
Qed.

Lemma cm2_halts_parts : forall p c f,
  cm2_halts p c f <-> cm2_run p c f /\ cm2_terminal p f.
Proof.
  intros. split.
  - intro H. destruct H; split; auto; unfold cm2_terminal; auto.
  - intros [Hr [Ht|Ht]].
    + eapply cm2_halts_explicit; eauto.
    + eapply cm2_halts_falloff; eauto.
Qed.

Lemma specialized_terminal_shift : forall p a f,
  cm2_terminal (specialized_program p a) (shift_config (a + 2) f) <->
  cm2_terminal (mm2_guest_program p) f.
Proof.
  intros p a f. unfold cm2_terminal. cbn [shift_config cc_pc].
  rewrite specialized_program_embed.
  destruct (nth_error (mm2_guest_program p) (cc_pc f)) as [i|];
    [destruct i|]; cbn [option_map shift_cm2_instr]; intuition discriminate.
Qed.

Theorem specialized_program_halts_complete : forall p a b final,
  cm2_halts (specialized_program p a) {| cc_pc := 0; cc_c0 := 0; cc_c1 := b |} final ->
  exists original,
    final = shift_config (a + 2) original /\
    cm2_halts (mm2_guest_program p) {| cc_pc := 1; cc_c0 := a; cc_c1 := b |} original.
Proof.
  intros p a b final Hh. apply cm2_halts_parts in Hh. destruct Hh as [Hr Ht].
  pose proof (specialized_program_preamble p a b) as Hp.
  destruct (cm2_runs_comparable _ _ _ _ Hp Hr) as [Hafter|Hbefore].
  - destruct (cm2_run_unembed _ _ _ _ _ (specialized_program_embed p a) Hafter)
      as [original [Hf Horig]].
    exists original. split; [exact Hf|]. apply cm2_halts_parts.
    split; [exact Horig|]. apply (proj1 (specialized_terminal_shift p a _)). rewrite <- Hf. exact Ht.
  - pose proof (cm2_terminal_run _ _ _ Ht Hbefore) as Hf.
    exists {| cc_pc := 1; cc_c0 := a; cc_c1 := b |}.
    split; [exact Hf|]. apply cm2_halts_parts. split; [constructor|].
    apply (proj1 (specialized_terminal_shift p a _)). rewrite <- Hf. exact Ht.
Qed.

Theorem specialized_program_halts_iff : forall p a b final,
  cm2_halts (mm2_guest_program p) {| cc_pc := 1; cc_c0 := a; cc_c1 := b |} final <->
  cm2_halts (specialized_program p a) {| cc_pc := 0; cc_c0 := 0; cc_c1 := b |}
    (shift_config (a + 2) final).
Proof.
  intros p a b final. split.
  - rewrite !cm2_halts_parts. intros [Hr Ht]. split.
    + apply specialized_program_correct. exact Hr.
    + apply (proj2 (specialized_terminal_shift p a _)). exact Ht.
  - intro H. destruct (specialized_program_halts_complete _ _ _ _ H)
      as [original [He Hr]]. apply shift_config_injective in He. subst. exact Hr.
Qed.

Theorem specialized_program_host_iff : forall ambient p a b final,
  interpreter_raw_produces ambient (mm2_guest_program p)
    {| cc_pc := 1; cc_c0 := a; cc_c1 := b |} final <->
  interpreter_raw_produces ambient (specialized_program p a)
    {| cc_pc := 0; cc_c0 := 0; cc_c1 := b |} (shift_config (a + 2) final).
Proof.
  intros. rewrite <- !cm2_uniform_interpreter_raw_correct_total.
  apply specialized_program_halts_iff.
Qed.

Theorem specialized_program_host_complete : forall ambient p a b actual,
  interpreter_raw_produces ambient (specialized_program p a)
    {| cc_pc := 0; cc_c0 := 0; cc_c1 := b |} actual ->
  exists original, actual = shift_config (a + 2) original /\
    interpreter_raw_produces ambient (mm2_guest_program p)
      {| cc_pc := 1; cc_c0 := a; cc_c1 := b |} original.
Proof.
  intros ambient p a b actual H.
  apply (proj2 (cm2_uniform_interpreter_raw_correct_total _ _ _ _)) in H.
  destruct (specialized_program_halts_complete _ _ _ _ H) as [original [He Hh]].
  exists original. split; [exact He|].
  apply cm2_uniform_interpreter_raw_correct_total. exact Hh.
Qed.

Example specialization_executes_guest_increment : forall a b,
  cm2_halts (specialized_program [mm2_inc_a] a)
    {| cc_pc := 0; cc_c0 := 0; cc_c1 := b |}
    (shift_config (a + 2) {| cc_pc := 2; cc_c0 := S a; cc_c1 := b |}).
Proof.
  intros a b. apply specialized_program_halts_iff.
  eapply cm2_halts_falloff; [|reflexivity].
  eapply cm2_run_step; [reflexivity|reflexivity|constructor].
Qed.

Example specialization_preserves_jump_to_zero : forall a b,
  cm2_halts (specialized_program [mm2_dec_a 0] (S a))
    {| cc_pc := 0; cc_c0 := 0; cc_c1 := b |}
    (shift_config (S a + 2) {| cc_pc := 0; cc_c0 := a; cc_c1 := b |}).
Proof.
  intros a b. apply specialized_program_halts_iff.
  eapply cm2_halts_explicit; [|reflexivity].
  eapply cm2_run_step; [reflexivity|reflexivity|constructor].
Qed.

Example specialization_preserves_out_of_range_jump : forall a b,
  cm2_halts (specialized_program [mm2_dec_a 100] (S a))
    {| cc_pc := 0; cc_c0 := 0; cc_c1 := b |}
    (shift_config (S a + 2) {| cc_pc := 100; cc_c0 := a; cc_c1 := b |}).
Proof.
  intros a b. apply specialized_program_halts_iff.
  eapply cm2_halts_falloff; [|reflexivity].
  eapply cm2_run_step; [reflexivity|reflexivity|constructor].
Qed.

Example specialization_zero_falls_through : forall b,
  cm2_halts (specialized_program [mm2_dec_a 0] 0)
    {| cc_pc := 0; cc_c0 := 0; cc_c1 := b |}
    (shift_config 2 {| cc_pc := 2; cc_c0 := 0; cc_c1 := b |}).
Proof.
  intro b. apply specialized_program_halts_iff.
  eapply cm2_halts_falloff; [|reflexivity].
  eapply cm2_run_step; [reflexivity|reflexivity|constructor].
Qed.
