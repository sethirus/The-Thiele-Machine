(** Executable, exact semantics of the actual CPU dispatch rule. *)
Require Import Kami.Kami Kami.Semantics.
From KamiHW Require Import ThieleTypes ThieleCPUCore NormalizationSteps
  NormalizationExecution ActionEvaluator.
From Coq Require Import List String Lia.
Import ListNotations.
Open Scope string_scope.

Definition dispatch_rule := normalization_rule 0.

Lemma dispatch_rule_name : attrName dispatch_rule = "step".
Proof. reflexivity. Qed.

Lemma dispatch_rule_in : In dispatch_rule (getRules thieleCore).
Proof.
  unfold dispatch_rule, normalization_rule. apply nth_In.
  change (0 < 12)%nat. lia.
Qed.

Lemma dispatch_rule_linear : linear_action (attrType dispatch_rule type).
Proof.
  unfold dispatch_rule, normalization_rule. cbn [nth getRules attrType].
  repeat (cbn [linear_action]; intro).
  exact I.
Qed.

Definition eval_dispatch (old : RegsT) : option UpdatesT :=
  match eval_linear_action old (attrType dispatch_rule type) with
  | Some (u, _) => Some u
  | None => None
  end.

Theorem dispatch_actual_action_iff : forall old u,
  eval_dispatch old = Some u <->
  SemAction old (attrType dispatch_rule type) u (M.empty _) WO.
Proof.
  intros old u. unfold eval_dispatch. split.
  - destruct (eval_linear_action old (attrType dispatch_rule type))
      as [[updates value]|] eqn:He; try discriminate.
    intro H. inversion H; subst updates.
    assert (value = WO) by (apply word0; reflexivity). subst value.
    eapply eval_linear_action_sound; eauto.
  - intro H. destruct (eval_linear_action_complete _ _ _ _ _ _ dispatch_rule_linear H)
      as [He _]. rewrite He. reflexivity.
Qed.

Theorem dispatch_actual_substep : forall old u,
  eval_dispatch old = Some u ->
  Substep thieleCore old u (Rle (Some "step")) (M.empty _).
Proof.
  intros old u He. eapply SingleRule with (a := attrType dispatch_rule).
  - exact dispatch_rule_in.
  - apply dispatch_actual_action_iff. exact He.
Qed.

Theorem dispatch_actual_execution : forall old u,
  eval_dispatch old = Some u ->
  Multistep thieleCore old (M.union u old) [normalization_label "step"].
Proof.
  intros. apply normalization_substep_execution.
  apply dispatch_actual_substep. assumption.
Qed.

Theorem dispatch_actual_action_unique : forall old u calls ret,
  SemAction old (attrType dispatch_rule type) u calls ret ->
  eval_dispatch old = Some u /\ calls = M.empty _ /\ ret = WO.
Proof.
  intros old u calls ret H.
  destruct (eval_linear_action_complete _ _ _ _ _ _ dispatch_rule_linear H) as [He Hc].
  split; [unfold eval_dispatch; rewrite He; reflexivity|].
  split; [exact Hc|]. apply word0.
Qed.

Definition dispatch_reset_state : RegsT := initRegs (getRegInits thieleCore).

Example dispatch_reset_enabled :
  (match eval_dispatch dispatch_reset_state with Some _ => true | None => false end) = true.
Proof. vm_compute. reflexivity. Qed.

Theorem dispatch_disabled_iff : forall old,
  eval_dispatch old = None <->
  forall u calls ret, ~ SemAction old (attrType dispatch_rule type) u calls ret.
Proof.
  intro old. split.
  - intros He u calls ret Hs.
    destruct (dispatch_actual_action_unique _ _ _ _ Hs) as [Hr _].
    rewrite He in Hr. discriminate.
  - intro Hnone. destruct (eval_dispatch old) as [u|] eqn:He; [|reflexivity].
    exfalso. apply (Hnone u (M.empty _) WO).
    apply dispatch_actual_action_iff. exact He.
Qed.

Theorem dispatch_reset_has_execution : exists u,
  Multistep thieleCore dispatch_reset_state (M.union u dispatch_reset_state)
    [normalization_label "step"].
Proof.
  pose proof dispatch_reset_enabled as H.
  destruct (eval_dispatch dispatch_reset_state) as [u|] eqn:He; [|discriminate].
  exists u. apply dispatch_actual_execution. exact He.
Qed.
