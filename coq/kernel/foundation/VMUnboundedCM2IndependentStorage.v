(** B2c: independently usable storage and control, under unchanged ISA
    semantics, sufficient for the chosen universal simulation (CM2/MM2).

    The B3 interpreter files already show, instruction by instruction, that
    an Inc0/DecJump0 host execution leaves counter 1's represented value
    syntactically untouched, and dually for counter 1.  What is missing
    from those files is a statement that this pair of registers is not
    merely non-interfering at a single step, but supplies unbounded,
    jointly independent storage: any pair (n, m) of natural numbers is
    reachable, with each coordinate driven solely by its own instruction
    count, in one real proven host execution.  This file supplies that
    statement, built from the existing CM2 program/run semantics and the
    existing interpreter simulation theorem; it adds no new VM semantics. *)

From Coq Require Import Arith Lia List.
Import ListNotations.
From Kernel Require Import VMState VMUnboundedStep.
From Kernel Require Import VMUnboundedCM2Interpreter.
From Kernel Require Import VMUnboundedCM2Encoding.
From Kernel Require Import VMUnboundedCM2Correctness.

(** Single-step non-interference, read directly off [cm2_step_instr]. *)

Theorem cm2_inc0_step_preserves_c1 : forall c c',
  cm2_step_instr CM2_Inc0 c = Some c' -> c'.(cc_c1) = c.(cc_c1).
Proof. intros [pc c0 c1] c' H. cbn in H. inversion H. reflexivity. Qed.

Theorem cm2_inc1_step_preserves_c0 : forall c c',
  cm2_step_instr CM2_Inc1 c = Some c' -> c'.(cc_c0) = c.(cc_c0).
Proof. intros [pc c0 c1] c' H. cbn in H. inversion H. reflexivity. Qed.

Theorem cm2_decjump0_step_preserves_c1 : forall target c c',
  cm2_step_instr (CM2_DecJump0 target) c = Some c' -> c'.(cc_c1) = c.(cc_c1).
Proof.
  intros target [pc c0 c1] c' H. cbn in H.
  destruct (Nat.eqb c0 0); inversion H; reflexivity.
Qed.

Theorem cm2_decjump1_step_preserves_c0 : forall target c c',
  cm2_step_instr (CM2_DecJump1 target) c = Some c' -> c'.(cc_c0) = c.(cc_c0).
Proof.
  intros target [pc c0 c1] c' H. cbn in H.
  destruct (Nat.eqb c1 0); inversion H; reflexivity.
Qed.

(** Transitivity of the abstract CM2 run relation for one fixed program;
    proved locally so this file stays independent of the MM2 vendor bridge. *)
Lemma cm2_run_trans : forall p c1 c2 c3,
  cm2_run p c1 c2 -> cm2_run p c2 c3 -> cm2_run p c1 c3.
Proof.
  intros p c1 c2 c3 H12. induction H12 as [|c i c1' c2' Hnth Hstep Htail IH]; intros H23.
  - exact H23.
  - eapply cm2_run_step; eauto.
Qed.

(** A block of [d] consecutive Inc0 instructions found at positions
    [k .. k+d-1] of [p] drives [cc_c0] up by exactly [d] and leaves
    [cc_c1] untouched, regardless of what precedes or follows the block. *)
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

(** The dual block for Inc1: drives [cc_c1] up by [d], leaves [cc_c0]
    untouched. *)
Lemma cm2_run_inc1_window : forall p d k c0 c1,
  (forall j, j < d -> nth_error p (k + j) = Some CM2_Inc1) ->
  cm2_run p {| cc_pc := k; cc_c0 := c0; cc_c1 := c1 |}
             {| cc_pc := k + d; cc_c0 := c0; cc_c1 := c1 + d |}.
Proof.
  intros p d. induction d as [|d IH]; intros k c0 c1 Hwin.
  - replace (k + 0) with k by lia. replace (c1 + 0) with c1 by lia.
    apply cm2_run_refl.
  - assert (Hi : nth_error p k = Some CM2_Inc1).
    { specialize (Hwin 0 ltac:(lia)). rewrite Nat.add_0_r in Hwin. exact Hwin. }
    eapply cm2_run_step.
    + exact Hi.
    + reflexivity.
    + assert (Hwin' : forall j, j < d -> nth_error p (S k + j) = Some CM2_Inc1).
      { intros j Hj. specialize (Hwin (S j) ltac:(lia)).
        replace (k + S j) with (S k + j) in Hwin by lia. exact Hwin. }
      specialize (IH (S k) c0 (S c1) Hwin').
      replace (S k + d) with (k + S d) in IH by lia.
      replace (S c1 + d) with (c1 + S d) in IH by lia.
      exact IH.
Qed.

(** Abstract independence and full range: for every pair (n, m) of natural
    numbers, one fixed CM2 program (n Inc0's followed by m Inc1's) drives
    the two counters to exactly (n, m), each coordinate controlled only by
    its own instruction count. *)
Theorem cm2_run_reach_pair : forall n m,
  cm2_run (repeat CM2_Inc0 n ++ repeat CM2_Inc1 m)
    {| cc_pc := 0; cc_c0 := 0; cc_c1 := 0 |}
    {| cc_pc := n + m; cc_c0 := n; cc_c1 := m |}.
Proof.
  intros n m. set (p := repeat CM2_Inc0 n ++ repeat CM2_Inc1 m).
  eapply cm2_run_trans.
  - assert (Hwin0 : forall j, j < n -> nth_error p (0 + j) = Some CM2_Inc0).
    { intros j Hj. unfold p. rewrite Nat.add_0_l.
      rewrite nth_error_app1 by (rewrite repeat_length; lia).
      apply nth_error_repeat; lia. }
    pose proof (cm2_run_inc0_window p n 0 0 0 Hwin0) as H.
    rewrite Nat.add_0_l in H. exact H.
  - assert (Hwin1 : forall j, j < m -> nth_error p (n + j) = Some CM2_Inc1).
    { intros j Hj. unfold p.
      rewrite nth_error_app2 by (rewrite repeat_length; lia).
      rewrite repeat_length. replace (n + j - n) with j by lia.
      apply nth_error_repeat; lia. }
    exact (cm2_run_inc1_window p m n n 0 Hwin1).
Qed.

(** The chosen program above fits the encoding it will be packed under. *)
Lemma cm2_reach_pair_fits : forall n m,
  cm2_program_fits (cm2_encoding_width (repeat CM2_Inc0 n ++ repeat CM2_Inc1 m))
    (repeat CM2_Inc0 n ++ repeat CM2_Inc1 m).
Proof. intros n m. apply cm2_program_fits_encoding_width. Qed.

(** B2c closure on the real machine: starting from the canonical initial
    boundary state for this program, there is a real, finite, actually
    proven host execution (via [run_vm_u] of the fixed [cm2_interpreter_program])
    after which the register file represents exactly the independently
    chosen pair (n, m) -- for every n, m, not merely a fixed example. Each
    counter's final value is controlled solely by its own instruction
    count, under the unchanged ISA and the unchanged fixed interpreter. *)
Theorem vm_storage_reaches_arbitrary_independent_pair :
  forall ambient n m,
  let p := repeat CM2_Inc0 n ++ repeat CM2_Inc1 m in
  let width := cm2_encoding_width p in
  exists fuel s',
    run_vm_u fuel cm2_interpreter_program
      (cm2_total_input_encoding ambient p 0 0) = s' /\
    cm2_rep (encode_cm2_program width p) width
      {| cc_pc := n + m; cc_c0 := n; cc_c1 := m |} s'.
Proof.
  intros ambient n m p width.
  apply (cm2_uniform_interpreter_run_simulation p width
    {| cc_pc := 0; cc_c0 := 0; cc_c1 := 0 |}
    {| cc_pc := n + m; cc_c0 := n; cc_c1 := m |}
    (cm2_total_input_encoding ambient p 0 0)).
  - apply cm2_reach_pair_fits.
  - apply cm2_run_reach_pair.
  - apply cm2_boundary_is_rep.
Qed.
