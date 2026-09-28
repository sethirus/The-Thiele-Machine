(** ADD for all pairs of 32-bit operands at a loaded reset boundary.
    The instruction is fixed: ADD r3,r1,r2 with charge 5. Arithmetic is the
    actual hardware [wplus], including wraparound. Other registers start at
    zero. This does not assume that arbitrary CPU states satisfy the guards. *)
Require Import Kami.Kami Kami.Semantics.
From KamiHW Require Import DispatchObservation DispatchContracts DispatchExecution ThieleTypes.
From Coq Require Import String List.
Import ListNotations.
Open Scope string_scope.
Definition dispatch_add_family_registers (x y : word 32) : type (Vector (Bit 32) 4) :=
  fun idx => if weq idx (natToWord 4 1) then x
    else if weq idx (natToWord 4 2) then y else natToWord 32 0.
Definition dispatch_add_family_state (x y : word 32) : RegsT :=
  M.add "regs" (existT (fullType type) (SyntaxKind (Vector (Bit 32) 4)) (dispatch_add_family_registers x y))
    (dispatch_loaded_reset dispatch_add_instruction).
Definition dispatch_add_family_result (x y : word 32) : type (Vector (Bit 32) 4) :=
  fun idx => if weq idx (natToWord 4 3) then wplus x y else dispatch_add_family_registers x y idx.
Lemma dispatch_add_family_enabled : forall x y,
  (match eval_dispatch (dispatch_add_family_state x y) with Some _ => true | None => false end) = true.
Proof. intros. vm_compute. reflexivity. Qed.
Lemma dispatch_add_family_regs_projection : forall x y,
  observe_dispatch_write (dispatch_add_family_state x y) "regs" =
  Some (existT (fullType type) (SyntaxKind (Vector (Bit 32) 4)) (dispatch_add_family_result x y)).
Proof.
  intros x y. vm_compute. clear_concrete_word_casts. cbn.
  apply f_equal with (f := @Some _).
  apply f_equal with (f := fun v : type (Vector (Bit 32) 4) =>
    existT (fullType type) (SyntaxKind (Vector (Bit 32) 4)) v).
  apply word4_function_extensionality.
  intros b0 b1 b2 b3; destruct b0, b1, b2, b3; vm_compute; reflexivity.
Qed.

Lemma dispatch_add_family_pc_projection : forall x y,
  observe_dispatch_write (dispatch_add_family_state x y) "pc" =
    Some (existT (fullType type) (SyntaxKind (Bit 32)) (natToWord 32 1)).
Proof. intros. vm_compute. clear_concrete_word_casts. reflexivity. Qed.

Lemma dispatch_add_family_mu_projection : forall x y,
  observe_dispatch_write (dispatch_add_family_state x y) "mu" =
    Some (existT (fullType type) (SyntaxKind (Bit 32)) (natToWord 32 5)).
Proof. intros. vm_compute. clear_concrete_word_casts. reflexivity. Qed.

Lemma dispatch_add_family_err_projection : forall x y,
  observe_dispatch_write (dispatch_add_family_state x y) "err" =
    Some (existT (fullType type) (SyntaxKind Bool) false).
Proof. intros. vm_compute. clear_concrete_word_casts. reflexivity. Qed.

Definition dispatch_add_family_post (x y : word 32) (final : RegsT) : Prop :=
  M.find "pc" final = Some (existT (fullType type) (SyntaxKind (Bit 32)) (natToWord 32 1)) /\
  M.find "mu" final = Some (existT (fullType type) (SyntaxKind (Bit 32)) (natToWord 32 5)) /\
  M.find "err" final = Some (existT (fullType type) (SyntaxKind Bool) false) /\
  M.find "regs" final = Some (existT (fullType type)
    (SyntaxKind (Vector (Bit 32) 4)) (dispatch_add_family_result x y)).

Theorem dispatch_add_family_actual_post : forall x y u,
  eval_dispatch (dispatch_add_family_state x y) = Some u ->
  dispatch_add_family_post x y (M.union u (dispatch_add_family_state x y)).
Proof.
  intros x y u He. unfold dispatch_add_family_post.
  repeat split; rewrite M.find_union;
    rewrite <- (observe_dispatch_write_correct _ _ _ He).
  - rewrite dispatch_add_family_pc_projection. reflexivity.
  - rewrite dispatch_add_family_mu_projection. reflexivity.
  - rewrite dispatch_add_family_err_projection. reflexivity.
  - rewrite dispatch_add_family_regs_projection. reflexivity.
Qed.

Theorem dispatch_add_family_actual_execution : forall x y, exists u,
  SemAction (dispatch_add_family_state x y) (attrType dispatch_rule type) u (M.empty _) WO /\
  Multistep ThieleCPUCore.thieleCore (dispatch_add_family_state x y)
    (M.union u (dispatch_add_family_state x y)) [NormalizationExecution.normalization_label "step"] /\
  dispatch_add_family_post x y (M.union u (dispatch_add_family_state x y)).
Proof.
  intros x y. pose proof (dispatch_add_family_enabled x y) as H.
  destruct (eval_dispatch (dispatch_add_family_state x y)) as [u|] eqn:He; [|discriminate].
  exists u. split.
  - apply dispatch_actual_action_iff. exact He.
  - split.
    + apply dispatch_actual_execution. exact He.
    + apply dispatch_add_family_actual_post. exact He.
Qed.
