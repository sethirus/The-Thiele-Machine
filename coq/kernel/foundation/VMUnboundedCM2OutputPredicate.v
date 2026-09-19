(** B4: a genuine output-value fact about actual host VM execution, not
    just raw halting -- one direction of a reduction toward "an explicitly
    named nontrivial extensional predicate" is undecidable, per B4's
    contract.

    [zero_out_program p] is a real, executable CM2 program built from an
    MM2 guest [p]: it runs [p] exactly as [mm2_guest_program p] would, but
    wherever [p] would stop -- either by MM2's own "address 0" halt
    convention, or by jumping to any address beyond the program, which is
    equally a stop under [cm2_halts_falloff] -- it instead falls into one
    trailing instruction that drains counter 0 to exactly 0 and then halts
    by falling off the array.

    This file proves the forward direction: if the MM2 instance (p,a,b)
    halts, the real host execution of [zero_out_program p] from (a,b)
    reaches a state with counter 0 = 0. The converse (a host halt with
    counter 0 = 0 implies the MM2 instance halts) is NOT proved here --
    it needs an embedding argument in the other direction, or an appeal to
    excluded middle on MM2_HALTING that this file deliberately avoids
    introducing as a new axiom dependency for this gate. Consequently this
    file does NOT yet establish undecidability of "halts with counter 0 =
    0" by reduction; it is real, checked, partial progress toward that,
    not the full result. Do not cite this file as closing that gate. *)

From Coq Require Import Arith Lia List.
Import ListNotations.
From Undecidability.Synthetic Require Import Undecidability.
From Undecidability.MinskyMachines Require Import MM2 MM2_undec.
Unset Implicit Arguments.
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

(** Send MM2's implicit halt target (0) AND every out-of-range target
    (anything beyond the real body, [len]) to [len] itself -- the position
    of the trailing drain instruction. Every genuine body target (1..len)
    shifts down by one to account for dropping the leading [CM2_Halt]
    marker [mm2_guest_program] uses. *)
Definition mm2_remap_target (len t : nat) : nat :=
  if orb (Nat.eqb t 0) (Nat.ltb len t) then len else Nat.pred t.

Definition mm2_remap_instr (len : nat) (i : CM2InstrU) : CM2InstrU :=
  match i with
  | CM2_Halt => CM2_Halt
  | CM2_Inc0 => CM2_Inc0
  | CM2_Inc1 => CM2_Inc1
  | CM2_DecJump0 t => CM2_DecJump0 (mm2_remap_target len t)
  | CM2_DecJump1 t => CM2_DecJump1 (mm2_remap_target len t)
  end.

Definition reindex_config (len : nat) (c : CM2ConfigU) : CM2ConfigU :=
  {| cc_pc := mm2_remap_target len c.(cc_pc); cc_c0 := c.(cc_c0); cc_c1 := c.(cc_c1) |}.

Definition zero_out_body (p : list mm2_instr) : list CM2InstrU :=
  map (mm2_remap_instr (length p)) (map mm2_guest_instruction p).

Definition zero_out_program (p : list mm2_instr) : list CM2InstrU :=
  zero_out_body p ++ [CM2_DecJump0 (length p)].

Lemma zero_out_body_length : forall p, length (zero_out_body p) = length p.
Proof. intro p. unfold zero_out_body. now rewrite !map_length. Qed.

(** Position [S k] of [mm2_guest_program p] (its real body) matches
    position [k] of [zero_out_program p], instruction-for-instruction
    under the remap, for every [k] within the body. *)
Lemma zero_out_program_embed : forall p k,
  k < length p ->
  nth_error (zero_out_program p) k =
  option_map (mm2_remap_instr (length p)) (nth_error (mm2_guest_program p) (S k)).
Proof.
  intros p k Hk. unfold zero_out_program, mm2_guest_program.
  rewrite nth_error_app1 by (rewrite zero_out_body_length; exact Hk).
  unfold zero_out_body. cbn [nth_error].
  apply nth_error_map.
Qed.

Lemma mm2_guest_instruction_not_halt : forall i, mm2_guest_instruction i <> CM2_Halt.
Proof. intros [| |t|t]; discriminate. Qed.

Lemma mm2_guest_program_halt_only_zero : forall p k,
  nth_error (mm2_guest_program p) k = Some CM2_Halt -> k = 0.
Proof.
  intros p [|k'] Hnth; [reflexivity|].
  unfold mm2_guest_program in Hnth. cbn [nth_error] in Hnth.
  rewrite nth_error_map in Hnth.
  destruct (nth_error p k') as [x|] eqn:Hx; cbn in Hnth; [|discriminate].
  inversion Hnth as [Heq]. exfalso. exact (@mm2_guest_instruction_not_halt x Heq).
Qed.

Lemma mm2_guest_program_body_pos : forall p j i,
  nth_error (mm2_guest_program p) j = Some i -> i <> CM2_Halt -> 1 <= j <= length p.
Proof.
  intros p j i Hnth Hi. unfold mm2_guest_program in Hnth.
  destruct j as [|j].
  - cbn [nth_error] in Hnth. inversion Hnth; subst. contradiction.
  - cbn [nth_error] in Hnth. split; [lia|].
    assert (Hb : j < length p).
    { apply nth_error_Some. rewrite nth_error_map in Hnth.
      destruct (nth_error p j); [discriminate|cbn in Hnth; discriminate]. }
    lia.
Qed.

(** The key arithmetic identity making the reindexing commute with
    ordinary (non-jump) pc advancement, for every live body position. *)
Lemma mm2_remap_target_succ : forall len k,
  1 <= k <= len -> S (mm2_remap_target len k) = mm2_remap_target len (S k).
Proof.
  intros len k [Hlo Hhi]. unfold mm2_remap_target.
  destruct (Nat.eqb k 0) eqn:Hz0.
  - apply Nat.eqb_eq in Hz0. lia.
  - destruct (Nat.ltb len k) eqn:Hlt.
    + apply Nat.ltb_lt in Hlt. lia.
    + cbn [orb].
      destruct (Nat.eqb (S k) 0) eqn:HzS.
      * apply Nat.eqb_eq in HzS. discriminate.
      * destruct (Nat.ltb len (S k)) eqn:HltS; cbn [orb].
        -- apply Nat.ltb_lt in HltS.
           assert (k = len) by lia. subst k. lia.
        -- apply Nat.ltb_ge in HltS.
           assert (k < len) by lia. lia.
Qed.

(** Every live run of [mm2_guest_program p] reindexes into a run of
    [zero_out_program p]. *)
Lemma cm2_run_remap : forall p c c',
  cm2_run (mm2_guest_program p) c c' ->
  cm2_run (zero_out_program p) (reindex_config (length p) c) (reindex_config (length p) c').
Proof.
  intros p c c' Hrun. induction Hrun as [c|c i c1 c2 Hnth Hstep Htail IH].
  - apply cm2_run_refl.
  - assert (Hi : i <> CM2_Halt).
    { intro Heq. subst i. cbn [cm2_step_instr] in Hstep. discriminate. }
    destruct (mm2_guest_program_body_pos p c.(cc_pc) i Hnth Hi) as [Hlo Hhi].
    set (len := length p).
    assert (Hsucc : S (mm2_remap_target len c.(cc_pc)) =
                    mm2_remap_target len (S c.(cc_pc))).
    { apply mm2_remap_target_succ. split; assumption. }
    destruct c.(cc_pc) as [|j] eqn:Hpc; [lia|].
    assert (Hk : j < length p) by lia.
    assert (Hemb : nth_error (zero_out_program p) j =
                   Some (mm2_remap_instr len i)).
    { rewrite (zero_out_program_embed p j Hk). rewrite Hnth. reflexivity. }
    assert (Hpc_re : (reindex_config len c).(cc_pc) = j).
    { unfold reindex_config. rewrite Hpc. unfold mm2_remap_target.
      cbn [Nat.eqb]. destruct (Nat.ltb len (S j)) eqn:HltSj; cbn [orb].
      - exfalso. apply Nat.ltb_lt in HltSj. lia.
      - reflexivity. }
    assert (Hstep' : cm2_step_instr (mm2_remap_instr len i)
                        (reindex_config len c) =
                      Some (reindex_config len c1)).
    { destruct c as [pc c0 c1']. cbn [cc_pc] in Hpc. subst pc.
      destruct i as [| | |t|t];
        cbn [cm2_step_instr mm2_remap_instr cc_pc cc_c0 cc_c1] in Hstep |- *.
      - discriminate.
      - inversion Hstep; subst. unfold reindex_config. cbn [cc_pc cc_c0 cc_c1].
        rewrite Hsucc. reflexivity.
      - inversion Hstep; subst. unfold reindex_config. cbn [cc_pc cc_c0 cc_c1].
        rewrite Hsucc. reflexivity.
      - destruct (Nat.eqb c0 0) eqn:Hz.
        + inversion Hstep; subst. unfold reindex_config. cbn [cc_pc cc_c0 cc_c1].
          rewrite Hz, Hsucc. reflexivity.
        + inversion Hstep; subst. unfold reindex_config. cbn [cc_pc cc_c0 cc_c1].
          rewrite Hz. reflexivity.
      - destruct (Nat.eqb c1' 0) eqn:Hz.
        + inversion Hstep; subst. unfold reindex_config. cbn [cc_pc cc_c0 cc_c1].
          rewrite Hz, Hsucc. reflexivity.
        + inversion Hstep; subst. unfold reindex_config. cbn [cc_pc cc_c0 cc_c1].
          rewrite Hz. reflexivity.
    }
    eapply cm2_run_step.
    + rewrite Hpc_re. exact Hemb.
    + exact Hstep'.
    + exact IH.
Qed.

(** The trailing instruction drains counter 0 to 0 and then halts by
    falling off the array, from any starting counter value. *)
Lemma zero_out_program_drains : forall p c0 c1,
  cm2_run (zero_out_program p) {| cc_pc := length p; cc_c0 := c0; cc_c1 := c1 |}
    {| cc_pc := S (length p); cc_c0 := 0; cc_c1 := c1 |}.
Proof.
  intros p c0. induction c0 as [|c0 IH]; intro c1.
  - eapply cm2_run_step.
    + unfold zero_out_program. cbn [cc_pc].
      rewrite nth_error_app2 by (rewrite zero_out_body_length; lia).
      rewrite zero_out_body_length, Nat.sub_diag. reflexivity.
    + reflexivity.
    + apply cm2_run_refl.
  - eapply cm2_run_step.
    + unfold zero_out_program. cbn [cc_pc].
      rewrite nth_error_app2 by (rewrite zero_out_body_length; lia).
      rewrite zero_out_body_length, Nat.sub_diag. reflexivity.
    + reflexivity.
    + apply IH.
Qed.

(** Any way [mm2_guest_program p] can stop -- explicit halt marker, or
    falling off the end at any out-of-range address -- reindexes to
    exactly the drain position. *)
Lemma cm2_halts_remap_pc : forall p start final,
  cm2_halts (mm2_guest_program p) start final ->
  mm2_remap_target (length p) final.(cc_pc) = length p.
Proof.
  intros p start final Hhalts. unfold mm2_remap_target.
  destruct Hhalts as [f Hr Hh|f Hr Hh]; cbn [cc_pc] in Hh |- *.
  - apply mm2_guest_program_halt_only_zero in Hh. rewrite Hh. reflexivity.
  - apply nth_error_None in Hh. unfold mm2_guest_program in Hh.
    cbn [length] in Hh. rewrite map_length in Hh.
    destruct (Nat.eqb f.(cc_pc) 0) eqn:Hz0; [reflexivity|].
    destruct (Nat.ltb (length p) f.(cc_pc)) eqn:Hlt; [reflexivity|].
    exfalso. apply Nat.ltb_ge in Hlt. lia.
Qed.

(** Forward direction: if the MM2 instance halts, the real host execution
    of [zero_out_program p] from (a,b) reaches a state with counter 0 = 0.
    (The converse is open; see the file header.) *)
Theorem zero_out_program_reaches_zero : forall p a b,
  (exists final, cm2_halts (mm2_guest_program p)
     {| cc_pc := 1; cc_c0 := a; cc_c1 := b |} final) ->
  exists c1, cm2_run (zero_out_program p) {| cc_pc := 0; cc_c0 := a; cc_c1 := b |}
    {| cc_pc := S (length p); cc_c0 := 0; cc_c1 := c1 |}.
Proof.
  intros p a b [final Hhalts].
  assert (Hrun : cm2_run (mm2_guest_program p) {| cc_pc := 1; cc_c0 := a; cc_c1 := b |} final).
  { destruct Hhalts as [f Hr _|f Hr _]; exact Hr. }
  pose proof (cm2_run_remap p _ _ Hrun) as Hre.
  pose proof (cm2_halts_remap_pc p _ final Hhalts) as Hpc.
  unfold reindex_config in Hre. cbn [cc_pc cc_c0 cc_c1] in Hre.
  rewrite Hpc in Hre.
  assert (Hstart : mm2_remap_target (length p) 1 = 0).
  { unfold mm2_remap_target. cbn [Nat.eqb].
    destruct (Nat.ltb (length p) 1) eqn:Hlt.
    - apply Nat.ltb_lt in Hlt. assert (Hlp : length p = 0) by lia.
      rewrite Hlp. reflexivity.
    - reflexivity. }
  rewrite Hstart in Hre.
  exists final.(cc_c1).
  eapply cm2_run_trans.
  - exact Hre.
  - apply zero_out_program_drains.
Qed.

Lemma mm2_remap_target_le : forall len t, mm2_remap_target len t <= len.
Proof.
  intros len t. unfold mm2_remap_target.
  destruct (Nat.eqb t 0) eqn:E1; cbn [orb]; [lia|].
  destruct (Nat.ltb len t) eqn:E2; cbn [orb]; [lia|].
  apply Nat.ltb_ge in E2. lia.
Qed.

Lemma mm2_remap_target_eq_len : forall len rpc,
  mm2_remap_target len rpc = len -> rpc = 0 \/ len < rpc.
Proof.
  intros len rpc Heq. unfold mm2_remap_target in Heq.
  destruct (Nat.eqb rpc 0) eqn:Hz0.
  - left. apply Nat.eqb_eq in Hz0. exact Hz0.
  - destruct (Nat.ltb len rpc) eqn:Hlt; cbn [orb] in Heq.
    + right. apply Nat.ltb_lt in Hlt. exact Hlt.
    + apply Nat.eqb_neq in Hz0. apply Nat.ltb_ge in Hlt. lia.
Qed.

Lemma mm2_remap_target_inj_lt : forall len rpc v,
  mm2_remap_target len rpc = v -> v < len -> rpc = S v.
Proof.
  intros len rpc v Heq Hv. unfold mm2_remap_target in Heq.
  destruct (Nat.eqb rpc 0) eqn:Hz0; cbn [orb] in Heq.
  - apply Nat.eqb_eq in Hz0. lia.
  - destruct (Nat.ltb len rpc) eqn:Hlt; cbn [orb] in Heq.
    + lia.
    + apply Nat.eqb_neq in Hz0. lia.
Qed.

Lemma mm2_remap_target_SS : forall len k, k < len -> mm2_remap_target len (S (S k)) = S k.
Proof.
  intros len k Hk. unfold mm2_remap_target.
  destruct (Nat.eqb (S (S k)) 0) eqn:E1.
  - apply Nat.eqb_eq in E1. discriminate.
  - destruct (Nat.ltb len (S (S k))) eqn:E2; cbn [orb].
    + apply Nat.ltb_lt in E2. lia.
    + apply Nat.ltb_ge in E2. lia.
Qed.

(** Converse direction, single step: inverting one real [zero_out_program]
    step at a live position back to the (unique) [mm2_guest_program] step
    it came from. *)
Lemma cm2_step_unremap : forall p k i c0 c1 c_z1,
  k < length p ->
  nth_error (zero_out_program p) k = Some i ->
  cm2_step_instr i {| cc_pc := k; cc_c0 := c0; cc_c1 := c1 |} = Some c_z1 ->
  exists i_orig r_orig,
    nth_error (mm2_guest_program p) (S k) = Some i_orig /\
    cm2_step_instr i_orig {| cc_pc := S k; cc_c0 := c0; cc_c1 := c1 |} = Some r_orig /\
    reindex_config (length p) r_orig = c_z1.
Proof.
  intros p k i c0 c1 c_z1 Hk Hnth Hstep.
  pose proof (zero_out_program_embed p k Hk) as Hemb.
  rewrite Hnth in Hemb.
  destruct (nth_error (mm2_guest_program p) (S k)) as [i_orig|] eqn:Ho; cbn in Hemb;
    [|discriminate].
  inversion Hemb as [Hii]; subst i.
  set (len := length p).
  destruct i_orig as [| | |t|t];
    cbn [mm2_remap_instr cm2_step_instr cc_pc cc_c0 cc_c1] in Hstep |- *.
  - discriminate.
  - assert (Hcz1 : c_z1 = {| cc_pc := S k; cc_c0 := S c0; cc_c1 := c1 |}).
    { inversion Hstep. reflexivity. }
    exists CM2_Inc0, {| cc_pc := S (S k); cc_c0 := S c0; cc_c1 := c1 |}.
    split; [reflexivity|]. split; [reflexivity|].
    rewrite Hcz1. unfold reindex_config. cbn [cc_pc cc_c0 cc_c1].
    rewrite (mm2_remap_target_SS len k Hk). reflexivity.
  - assert (Hcz1 : c_z1 = {| cc_pc := S k; cc_c0 := c0; cc_c1 := S c1 |}).
    { inversion Hstep. reflexivity. }
    exists CM2_Inc1, {| cc_pc := S (S k); cc_c0 := c0; cc_c1 := S c1 |}.
    split; [reflexivity|]. split; [reflexivity|].
    rewrite Hcz1. unfold reindex_config. cbn [cc_pc cc_c0 cc_c1].
    rewrite (mm2_remap_target_SS len k Hk). reflexivity.
  - destruct (Nat.eqb c0 0) eqn:Hz.
    + assert (Hcz1 : c_z1 = {| cc_pc := S k; cc_c0 := 0; cc_c1 := c1 |}).
      { inversion Hstep. reflexivity. }
      exists (CM2_DecJump0 t), {| cc_pc := S (S k); cc_c0 := 0; cc_c1 := c1 |}.
      split; [reflexivity|]. split; [cbn [cm2_step_instr cc_pc cc_c0 cc_c1]; rewrite Hz; reflexivity|].
      rewrite Hcz1. unfold reindex_config. cbn [cc_pc cc_c0 cc_c1].
      rewrite (mm2_remap_target_SS len k Hk). reflexivity.
    + assert (Hcz1 : c_z1 = {| cc_pc := mm2_remap_target len t;
                                cc_c0 := Nat.pred c0; cc_c1 := c1 |}).
      { inversion Hstep. reflexivity. }
      exists (CM2_DecJump0 t), {| cc_pc := t; cc_c0 := Nat.pred c0; cc_c1 := c1 |}.
      split; [reflexivity|]. split; [cbn [cm2_step_instr cc_pc cc_c0 cc_c1]; rewrite Hz; reflexivity|].
      rewrite Hcz1. unfold reindex_config. reflexivity.
  - destruct (Nat.eqb c1 0) eqn:Hz.
    + assert (Hcz1 : c_z1 = {| cc_pc := S k; cc_c0 := c0; cc_c1 := 0 |}).
      { inversion Hstep. reflexivity. }
      exists (CM2_DecJump1 t), {| cc_pc := S (S k); cc_c0 := c0; cc_c1 := 0 |}.
      split; [reflexivity|]. split; [cbn [cm2_step_instr cc_pc cc_c0 cc_c1]; rewrite Hz; reflexivity|].
      rewrite Hcz1. unfold reindex_config. cbn [cc_pc cc_c0 cc_c1].
      rewrite (mm2_remap_target_SS len k Hk). reflexivity.
    + assert (Hcz1 : c_z1 = {| cc_pc := mm2_remap_target len t;
                                cc_c0 := c0; cc_c1 := Nat.pred c1 |}).
      { inversion Hstep. reflexivity. }
      exists (CM2_DecJump1 t), {| cc_pc := t; cc_c0 := c0; cc_c1 := Nat.pred c1 |}.
      split; [reflexivity|]. split; [cbn [cm2_step_instr cc_pc cc_c0 cc_c1]; rewrite Hz; reflexivity|].
      rewrite Hcz1. unfold reindex_config. reflexivity.
Qed.

(** Converse: any real [zero_out_program] run that starts live and reaches
    at or past the drain position corresponds to a genuine
    [mm2_guest_program] halt at the matching (unshifted) position, with
    the remainder of the run being exactly the drain. *)
Lemma cm2_run_unremap : forall p c_z c_z',
  cm2_run (zero_out_program p) c_z c_z' ->
  c_z.(cc_pc) < length p ->
  length p <= c_z'.(cc_pc) ->
  exists final_orig,
    cm2_halts (mm2_guest_program p)
      {| cc_pc := S c_z.(cc_pc); cc_c0 := c_z.(cc_c0); cc_c1 := c_z.(cc_c1) |}
      final_orig /\
    cm2_run (zero_out_program p)
      {| cc_pc := length p; cc_c0 := final_orig.(cc_c0); cc_c1 := final_orig.(cc_c1) |}
      c_z'.
Proof.
  intros p c_z c_z' Hrun. induction Hrun as [c_z|c_z i c_z1 c_z2 Hnth Hstep Htail IH];
    intros Hlive Hcross.
  - lia.
  - destruct (cm2_step_unremap p c_z.(cc_pc) i c_z.(cc_c0) c_z.(cc_c1) c_z1 Hlive)
      as (i_orig & r_orig & Horig & Hstep_orig & Hre);
      [ destruct c_z as [pc c0 c1']; exact Hnth
      | destruct c_z as [pc c0 c1']; exact Hstep | ].
    destruct c_z as [pc c0 c1'] eqn:Hcz. cbn [cc_pc cc_c0 cc_c1] in *.
    destruct (Nat.ltb c_z1.(cc_pc) (length p)) eqn:Hlt1.
    + apply Nat.ltb_lt in Hlt1.
      destruct (IH Hlt1 Hcross) as (final_orig & Hhalts_orig & Hdrain).
      exists final_orig. split; [|exact Hdrain].
      assert (Hr1 : r_orig = {| cc_pc := S c_z1.(cc_pc); cc_c0 := c_z1.(cc_c0);
                                 cc_c1 := c_z1.(cc_c1) |}).
      { destruct r_orig as [rpc rc0 rc1]. destruct c_z1 as [z1pc z1c0 z1c1].
        unfold reindex_config in Hre. cbn [cc_pc cc_c0 cc_c1] in Hre |- *.
        injection Hre as Hrpc Hrc0 Hrc1.
        pose proof (mm2_remap_target_inj_lt (length p) rpc z1pc Hrpc Hlt1) as Hrpc'.
        f_equal; lia. }
      destruct Hhalts_orig as [f Hro Hh|f Hro Hh].
      * apply cm2_halts_explicit with (final := f); [|exact Hh].
        eapply cm2_run_step; [exact Horig|exact Hstep_orig|rewrite Hr1; exact Hro].
      * apply cm2_halts_falloff with (final := f); [|exact Hh].
        eapply cm2_run_step; [exact Horig|exact Hstep_orig|rewrite Hr1; exact Hro].
    + apply Nat.ltb_ge in Hlt1.
      destruct c_z1 as [z1pc z1c0 z1c1]. destruct r_orig as [rpc rc0 rc1].
      unfold reindex_config in Hre. cbn [cc_pc cc_c0 cc_c1] in Hre, Hlt1 |- *.
      injection Hre as Hrpc Hrc0 Hrc1.
      assert (Hle : z1pc <= length p).
      { rewrite <- Hrpc. apply mm2_remap_target_le. }
      assert (Hpc1 : z1pc = length p) by lia.
      exists {| cc_pc := rpc; cc_c0 := rc0; cc_c1 := rc1 |}. split.
      * assert (Hrpc' : rpc = 0 \/ length p < rpc).
        { apply mm2_remap_target_eq_len. rewrite Hrpc. exact Hpc1. }
        destruct Hrpc' as [Hz0|Hgt].
        -- apply cm2_halts_explicit with (final := {| cc_pc := rpc; cc_c0 := rc0; cc_c1 := rc1 |}).
           ++ eapply cm2_run_step; [exact Horig|exact Hstep_orig|apply cm2_run_refl].
           ++ cbn [cc_pc]. rewrite Hz0. reflexivity.
        -- apply cm2_halts_falloff with (final := {| cc_pc := rpc; cc_c0 := rc0; cc_c1 := rc1 |}).
           ++ eapply cm2_run_step; [exact Horig|exact Hstep_orig|apply cm2_run_refl].
           ++ cbn [cc_pc]. apply nth_error_None.
              unfold mm2_guest_program. cbn [length]. rewrite map_length. lia.
      * cbn [cc_pc cc_c0 cc_c1]. rewrite Hrc0, Hrc1, <- Hpc1. exact Htail.
Qed.

(** Full reduction: the MM2 instance halts iff the real host execution of
    [zero_out_program p] from (a,b) reaches a state with counter 0 = 0. *)
Theorem zero_out_program_full_iff : forall p a b,
  MM2_HALTING (p, a, b) <->
  exists c1, cm2_run (zero_out_program p) {| cc_pc := 0; cc_c0 := a; cc_c1 := b |}
    {| cc_pc := S (length p); cc_c0 := 0; cc_c1 := c1 |}.
Proof.
  intros p a b. unfold MM2_HALTING.
  rewrite (mm2_termination_guest_iff p (1, (a, b))).
  unfold mm2_guest_config. cbn [fst snd].
  split.
  - apply zero_out_program_reaches_zero.
  - intros [c1 Hrun]. destruct (length p) as [|n] eqn:Hlen.
    + exists {| cc_pc := 1; cc_c0 := a; cc_c1 := b |}.
      apply cm2_halts_falloff with (final := {| cc_pc := 1; cc_c0 := a; cc_c1 := b |}).
      * apply cm2_run_refl.
      * cbn [cc_pc]. apply nth_error_None.
        unfold mm2_guest_program. cbn [length]. rewrite map_length, Hlen. lia.
    + assert (Hlive : (0 : nat) < length p) by lia.
      assert (Hcross : length p <= S (S n)) by lia.
      destruct (cm2_run_unremap p _ _ Hrun Hlive Hcross) as (final_orig & Hhalts & _).
      exists final_orig. exact Hhalts.
Qed.

(** The predicate "the guest halts with counter 0 = 0" -- a genuine
    output-value fact, not a restatement of raw halting -- is therefore
    undecidable on real host executions, by many-one reduction from the
    pinned MM2 halting problem. *)
Definition cm2_host_outputs_zero (p : list mm2_instr) (ab : nat * nat) : Prop :=
  exists c1, cm2_run (zero_out_program p)
    {| cc_pc := 0; cc_c0 := fst ab; cc_c1 := snd ab |}
    {| cc_pc := S (length p); cc_c0 := 0; cc_c1 := c1 |}.

Theorem mm2_to_cm2_host_outputs_zero : forall p a b,
  MM2_HALTING (p, a, b) <-> cm2_host_outputs_zero p (a, b).
Proof. intros p a b. exact (zero_out_program_full_iff p a b). Qed.

Theorem cm2_host_outputs_zero_undecidable :
  undecidable (fun pab : list mm2_instr * (nat * nat) =>
    cm2_host_outputs_zero (fst pab) (snd pab)).
Proof.
  apply (undecidability_from_reducibility MM2_HALTING_undec).
  exists (fun P : MM2_PROBLEM => let '(p, a, b) := P in (p, (a, b))).
  intros [[p a] b]. exact (zero_out_program_full_iff p a b).
Qed.
