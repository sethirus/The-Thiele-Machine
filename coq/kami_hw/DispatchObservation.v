(** Observation of the real dispatch rule without constructing its update map. *)
Require Import Kami.Kami Kami.Semantics.
From KamiHW Require Import ActionEvaluator ActionObservation DispatchExecution
  DispatchContracts ThieleTypes.
From Coq Require Import String NArith List FunctionalExtensionality Eqdep_dec Arith.PeanoNat.
Import ListNotations.
Open Scope string_scope.

Definition observe_dispatch_write (old : RegsT) (key : string) :=
  observe_action_write old key (attrType dispatch_rule type).

Theorem observe_dispatch_write_correct : forall old u key,
  eval_dispatch old = Some u ->
  observe_dispatch_write old key = M.find key u.
Proof.
  intros. apply observe_action_write_correct with (calls := M.empty _) (ret := WO).
  - exact dispatch_rule_linear.
  - apply dispatch_actual_action_iff. assumption.
Qed.

Definition dispatch_add_instruction : word 128 :=
  NToWord 128 (N.lor (N.shiftl 2 120)
    (N.lor (N.shiftl 19 24) (N.lor (N.shiftl 3 16)
      (N.lor (N.shiftl 18 8) 5)))).
Definition dispatch_add_registers : type (Vector (Bit WordSz) RegIdxSz) :=
  fun idx => if weq idx (natToWord RegIdxSz 1) then natToWord WordSz 7
    else if weq idx (natToWord RegIdxSz 2) then natToWord WordSz 9
    else natToWord WordSz 0.
Definition dispatch_add_state : RegsT :=
  M.add "regs" (existT (fullType type)
    (SyntaxKind (Vector (Bit WordSz) RegIdxSz)) dispatch_add_registers)
    (dispatch_loaded_reset dispatch_add_instruction).

(** Kami's zero-extension/truncation uses [abstract lia] equality proofs.
    These remain opaque during VM reduction. For concrete widths, decidable
    equality of naturals identifies each proof with reflexivity, allowing its
    dependent cast to reduce. This uses UIP for nat, not proof irrelevance. *)
Ltac clear_concrete_word_casts :=
  repeat match goal with
  | |- context [@evalZeroExtendTrunc_subproof0 ?n ?m ?p] =>
      replace (@evalZeroExtendTrunc_subproof0 n m p) with (@eq_refl nat n)
        by (apply Eqdep_dec.UIP_dec; exact Nat.eq_dec)
  | |- context [@evalZeroExtendTrunc_subproof ?n ?m ?p] =>
      replace (@evalZeroExtendTrunc_subproof n m p) with (@eq_refl nat m)
        by (apply Eqdep_dec.UIP_dec; exact Nat.eq_dec)
  end.

Example dispatch_add_enabled :
  (match eval_dispatch dispatch_add_state with Some _ => true | None => false end) = true.
Proof. vm_compute. clear_concrete_word_casts. reflexivity. Qed.

Example dispatch_add_pc_projection :
  observe_dispatch_write dispatch_add_state "pc" =
    Some (existT (fullType type) (SyntaxKind (Bit 32)) (natToWord 32 1)).
Proof. vm_compute. clear_concrete_word_casts. reflexivity. Qed.

Definition dispatch_add_result : type (Vector (Bit WordSz) RegIdxSz) :=
  fun idx => if weq idx (natToWord RegIdxSz 3) then natToWord WordSz 16
    else dispatch_add_registers idx.

Lemma word4_function_extensionality : forall (f g : word 4 -> word 32),
  (forall b0 b1 b2 b3, f (WS b0 (WS b1 (WS b2 (WS b3 WO)))) =
    g (WS b0 (WS b1 (WS b2 (WS b3 WO))))) -> f = g.
Proof.
  intros f g H. apply functional_extensionality. intro idx.
  shatter_word idx. apply H.
Qed.


Example dispatch_add_regs_projection :
  observe_dispatch_write dispatch_add_state "regs" =
    Some (existT (fullType type) (SyntaxKind (Vector (Bit WordSz) RegIdxSz))
      dispatch_add_result).
Proof.
  vm_compute. clear_concrete_word_casts. cbn.
  apply f_equal with (f := @Some _).
  apply f_equal with (f := fun v : type (Vector (Bit WordSz) RegIdxSz) =>
    existT (fullType type) (SyntaxKind (Vector (Bit WordSz) RegIdxSz)) v).
  apply word4_function_extensionality.
  intros b0 b1 b2 b3; destruct b0, b1, b2, b3; vm_compute; reflexivity.
Qed.

Example dispatch_add_mu_projection :
  observe_dispatch_write dispatch_add_state "mu" =
    Some (existT (fullType type) (SyntaxKind (Bit 32)) (natToWord 32 5)).
Proof. vm_compute. clear_concrete_word_casts. reflexivity. Qed.

Example dispatch_add_err_projection :
  observe_dispatch_write dispatch_add_state "err" =
    Some (existT (fullType type) (SyntaxKind Bool) false).
Proof. vm_compute. clear_concrete_word_casts. reflexivity. Qed.

Definition dispatch_add_post (final : RegsT) : Prop :=
  M.find "pc" final = Some (existT (fullType type) (SyntaxKind (Bit 32)) (natToWord 32 1)) /\
  M.find "mu" final = Some (existT (fullType type) (SyntaxKind (Bit 32)) (natToWord 32 5)) /\
  M.find "err" final = Some (existT (fullType type) (SyntaxKind Bool) false) /\
  M.find "regs" final = Some (existT (fullType type)
    (SyntaxKind (Vector (Bit WordSz) RegIdxSz)) dispatch_add_result).

Theorem dispatch_add_actual_post : forall u,
  eval_dispatch dispatch_add_state = Some u ->
  dispatch_add_post (M.union u dispatch_add_state).
Proof.
  intros u He. unfold dispatch_add_post.
  repeat split; rewrite M.find_union;
    rewrite <- (observe_dispatch_write_correct _ _ _ He).
  - rewrite dispatch_add_pc_projection. reflexivity.
  - rewrite dispatch_add_mu_projection. reflexivity.
  - rewrite dispatch_add_err_projection. reflexivity.
  - rewrite dispatch_add_regs_projection. reflexivity.
Qed.

Theorem dispatch_add_actual_execution : exists u,
  SemAction dispatch_add_state (attrType dispatch_rule type) u (M.empty _) WO /\
  Multistep ThieleCPUCore.thieleCore dispatch_add_state
    (M.union u dispatch_add_state) [NormalizationExecution.normalization_label "step"] /\
  dispatch_add_post (M.union u dispatch_add_state).
Proof.
  pose proof dispatch_add_enabled as H.
  destruct (eval_dispatch dispatch_add_state) as [u|] eqn:He; [|discriminate].
  exists u. split.
  - apply dispatch_actual_action_iff. exact He.
  - split.
    + apply dispatch_actual_execution. exact He.
    + apply dispatch_add_actual_post. exact He.
Qed.
