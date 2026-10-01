(** Verified numeric dispatch and semantic s-m-n for the self-interpreted
    guest fragment. *)

From Coq Require Import Arith List Bool Lia.
Import ListNotations.
From Kernel Require Import VMState VMUnboundedStep VMInstructionEncoding.
From Kernel Require Import VMSelfGuest VMSelfRun VMSelfRice.
From Kernel Require Import VMRecursionTarget VMDynamicEvalTarget.

Lemma g_reify_denote : forall i,
  g_reify_instruction (g_denote i) = Some i.
Proof. intro i; destruct i; reflexivity. Qed.

Lemma g_reify_guest_program : forall p,
  g_reify_program (g_program p) = Some p.
Proof.
  induction p as [|i p IH]; [reflexivity|].
  change
    (match g_reify_instruction (g_denote i),
           g_reify_program (g_program p) with
     | Some gi, Some gp => Some (gi :: gp)
     | _, _ => None
     end = Some (i :: p)).
  rewrite g_reify_denote, IH. reflexivity.
Qed.

Theorem g_decode_guest_code_roundtrip : forall p,
  g_decode_program (guest_program_code p) = Some p.
Proof.
  intro p. unfold g_decode_program, guest_program_code.
  rewrite nat_to_program_program_to_nat.
  apply g_reify_guest_program.
Qed.

Theorem g_eval_guest_code : forall fuel p x,
  g_eval fuel (guest_program_code p) x =
  Some (g_run fuel p (g_input x)).
Proof.
  intros fuel p x. unfold g_eval. rewrite g_decode_guest_code_roundtrip.
  reflexivity.
Qed.

Theorem g_eval_is_actual_vm_execution : forall fuel p x amb tl,
  g_wf_program p ->
  match g_eval fuel (guest_program_code p) x with
  | Some c =>
      run_vm_u fuel (g_program p) (gc_state amb tl (g_input x)) =
      gc_state amb tl c
  | None => False
  end.
Proof.
  intros fuel p x amb tl Hwf.
  rewrite g_eval_guest_code.
  apply g_run_is_run_vm_u. exact Hwf.
Qed.

Lemma g_specialize_wf : forall p x,
  g_wf_program p -> g_wf_program (g_specialize p x).
Proof.
  intros p x Hwf. unfold g_specialize, g_wf_program.
  constructor.
  - unfold g_wf; cbn [g_dst g_rs1 g_rs2 g_cost]. lia.
  - apply reloc_wf. exact Hwf.
Qed.

Lemma g_specialize_embeds : forall p x,
  embeds (g_specialize p x) 1 p.
Proof.
  intros p x i Hi. unfold embeds, g_specialize.
  replace (1 + i) with (S i) by lia. cbn [nth_error]. reflexivity.
Qed.

Lemma g_specialize_length : forall p x,
  length (g_specialize p x) = 1 + length p.
Proof.
  intros p x. unfold g_specialize. cbn [length]. rewrite reloc_length. lia.
Qed.

Lemma g_specialize_prefix : forall p x y,
  g_run 1 (g_specialize p x) (g_input y) =
  rconf 1 (length p) (g_input x).
Proof.
  intros [|i p] x y;
    reflexivity.
Qed.

(** Generalized tail lemma: the prefix may replace the external input before
    entering the relocated tail. *)
Lemma tail_beh_from : forall P K w outer inner N0 g mu,
  embeds P K w -> length P = K + length w ->
  g_run N0 P (g_input outer) = rconf K (length w) (g_input inner) ->
  g_beh P outer g mu <-> g_beh w inner g mu.
Proof.
  intros P K w outer inner N0 g mu Hemb Hlen HN0.
  set (T := fun n => g_terminal w (g_run n w (g_input inner))).
  assert (Tdec : forall n, {T n} + {~ T n})
    by (intro n; apply g_terminal_dec).
  split.
  - intros (N & HtN & Hg & Hmu).
    set (N' := Nat.max N N0).
    assert (HN' : g_run N' P (g_input outer) = g_run N P (g_input outer))
      by (apply g_run_terminal_after; [exact HtN|lia]).
    replace N' with (N0 + (N' - N0)) in HN' by lia.
    rewrite g_run_add, HN0 in HN'.
    destruct (bounded_search T Tdec (N' - N0)) as [(k & Hk & Tk)|Hno].
    + destruct (least_index T Tdec k Tk) as (j & Hj & Tj & Hmin).
      pose proof (reloc_run P K w j (g_input inner) Hemb Hmin) as Hr.
      exists j. split; [exact Tj|].
      assert (HPj : g_run (N' - N0) P (rconf K (length w) (g_input inner)) =
                    g_run j P (rconf K (length w) (g_input inner))).
      { apply g_run_terminal_after; [|lia].
        rewrite Hr. unfold g_terminal, rconf, rpc; cbn [gc_pc].
        unfold T, g_terminal in Tj. rewrite Hlen.
        destruct (gc_pc (g_run j w (g_input inner)) <? length w) eqn:E;
          [apply Nat.ltb_lt in E; lia|lia]. }
      rewrite HPj, Hr in HN'. unfold rconf in HN'.
      rewrite <- HN' in Hg, Hmu. cbn in Hg, Hmu. split; assumption.
    + exfalso.
      assert (Hlive : forall m, m < N' - N0 ->
        ~ g_terminal w (g_run m w (g_input inner)))
        by (intros m Hm; apply (Hno m); lia).
      pose proof (reloc_run P K w (N' - N0) (g_input inner) Hemb Hlive) as Hr.
      rewrite Hr in HN'. unfold g_terminal in HtN. rewrite <- HN' in HtN.
      unfold rconf, rpc in HtN; cbn [gc_pc] in HtN.
      pose proof (Hno (N' - N0) ltac:(lia)) as Hnt.
      unfold T, g_terminal in Hnt.
      destruct (gc_pc (g_run (N' - N0) w (g_input inner)) <? length w) eqn:E.
      * apply Nat.ltb_lt in E. lia.
      * apply Nat.ltb_ge in E. lia.
  - intros (n & Htn & Hg & Hmu).
    destruct (least_index T Tdec n Htn) as (j & Hj & Tj & Hmin).
    assert (Hsame : g_run j w (g_input inner) = g_run n w (g_input inner))
      by (symmetry; apply g_run_terminal_after; [exact Tj|lia]).
    pose proof (reloc_run P K w j (g_input inner) Hemb Hmin) as Hr.
    exists (N0 + j). rewrite g_run_add, HN0, Hr.
    unfold T, g_terminal in Tj.
    unfold g_terminal, rconf, rpc; cbn [gc_pc gc_g gc_mu].
    rewrite Hsame in *. split; [|split; assumption].
    rewrite Hlen.
    destruct (gc_pc (g_run n w (g_input inner)) <? length w) eqn:E;
      [apply Nat.ltb_lt in E; lia|lia].
Qed.

Theorem g_smn : forall p x y g mu,
  g_beh (g_specialize p x) y g mu <-> g_beh p x g mu.
Proof.
  intros p x y g mu.
  eapply tail_beh_from with (K := 1) (N0 := 1).
  - apply g_specialize_embeds.
  - apply g_specialize_length.
  - apply g_specialize_prefix.
Qed.

Print Assumptions g_decode_guest_code_roundtrip.
Print Assumptions g_eval_guest_code.
Print Assumptions g_eval_is_actual_vm_execution.
Print Assumptions g_smn.
