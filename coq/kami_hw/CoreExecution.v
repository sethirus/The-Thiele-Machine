(** Executable selection and finite traces over the actual CPU rules. *)
Require Import Kami.Kami Kami.Semantics.
From KamiHW Require Import ThieleTypes ThieleCPUCore ActionEvaluator
  NormalizationExecution NormalizationRetirement CoreRules DispatchExecution.
From Coq Require Import List String Lia.
Import ListNotations.
Open Scope list_scope.

Definition eval_cpu_rule (old : RegsT) (r : cpu_rule) : option UpdatesT :=
  match eval_linear_action old (attrType r type) with
  | Some (u, _) => Some u
  | None => None
  end.

Fixpoint select_cpu_rule (old : RegsT) (rules : list cpu_rule)
  : option (string * UpdatesT) :=
  match rules with
  | nil => None
  | cons r rest =>
      match eval_cpu_rule old r with
      | Some u => Some (attrName r, u)
      | None => select_cpu_rule old rest
      end
  end.

Lemma selected_cpu_rule : forall rules old name u,
  select_cpu_rule old rules = Some (name, u) ->
  exists r, In r rules /\ attrName r = name /\ eval_cpu_rule old r = Some u.
Proof.
  induction rules as [|r rest IH]; intros old name u H; [discriminate|].
  cbn [select_cpu_rule] in H.
  destruct (eval_cpu_rule old r) as [updates|] eqn:He.
  - inversion H; subst. exists r. split; [left; reflexivity|].
    split; [reflexivity|exact He].
  - destruct (IH _ _ _ H) as [chosen [Hin [Hname Hrun]]].
    exists chosen. split; [right; exact Hin|]. split; assumption.
Qed.

Lemma no_cpu_rule_selected : forall rules old,
  select_cpu_rule old rules = None <->
  forall r, In r rules -> eval_cpu_rule old r = None.
Proof.
  induction rules as [|r rest IH]; intro old; cbn [select_cpu_rule].
  - split; [intros _ r H; inversion H|reflexivity].
  - destruct (eval_cpu_rule old r) as [u|] eqn:He.
    + split; [discriminate|intro H; specialize (H r (or_introl eq_refl)); congruence].
    + rewrite IH. split.
      * intros H chosen [Hr|Hin]; [subst; exact He|apply H; exact Hin].
      * intros H chosen Hin. apply H. right. exact Hin.
Qed.

Theorem selected_cpu_rule_actual : forall old name u,
  select_cpu_rule old (getRules thieleCore) = Some (name, u) ->
  Substep thieleCore old u (Rle (Some name)) (M.empty _).
Proof.
  intros old name u H.
  destruct (selected_cpu_rule _ _ _ _ H) as [r [Hin [Hname He]]].
  subst name. eapply SingleRule with (a := attrType r).
  - destruct r. exact Hin.
  -
  unfold eval_cpu_rule in He.
  destruct (eval_linear_action old (attrType r type)) as [[updates ret]|] eqn:Hr;
    [|discriminate].
  inversion He; subst updates.
  assert (ret = WO) by apply word0. subst ret.
  apply eval_linear_action_sound. exact Hr.
Qed.

Theorem cpu_selection_none_iff : forall old,
  select_cpu_rule old (getRules thieleCore) = None <->
  forall r u calls ret, In r (getRules thieleCore) ->
    ~ SemAction old (attrType r type) u calls ret.
Proof.
  intro old. rewrite no_cpu_rule_selected. split.
  - intros H r u calls ret Hin Hsem.
    pose proof (proj1 (Forall_forall _ _) cpu_rules_linear r Hin) as Hl.
    destruct (eval_linear_action_complete _ _ _ _ _ _ Hl Hsem) as [He _].
    specialize (H r Hin). unfold eval_cpu_rule in H. rewrite He in H. discriminate.
  - intros H r Hin. unfold eval_cpu_rule.
    destruct (eval_linear_action old (attrType r type)) as [[u ret]|] eqn:He;
      [|reflexivity].
    exfalso. eapply (H r u (M.empty _) ret Hin).
    apply eval_linear_action_sound. exact He.
Qed.

Fixpoint run_cpu_rules (fuel : nat) (old : RegsT) : RegsT * list LabelT :=
  match fuel with
  | 0 => (old, nil)
  | S n =>
      match select_cpu_rule old (getRules thieleCore) with
      | None => (old, nil)
      | Some (name, u) =>
          let '(final, labels) := run_cpu_rules n (M.union u old) in
          (final, List.app labels (cons (normalization_label name) nil))
      end
  end.

Theorem run_cpu_rules_actual : forall fuel old,
  Multistep thieleCore old (fst (run_cpu_rules fuel old))
    (snd (run_cpu_rules fuel old)).
Proof.
  induction fuel as [|fuel IH]; intro old; cbn [run_cpu_rules].
  - constructor. reflexivity.
  - destruct (select_cpu_rule old (getRules thieleCore)) as [[name u]|] eqn:He.
    + specialize (IH (M.union u old)).
      destruct (run_cpu_rules fuel (M.union u old)) as [final labels].
      cbn [fst snd] in *.
      eapply normalization_multistep_trans.
      * apply normalization_substep_execution. apply selected_cpu_rule_actual. exact He.
      * exact IH.
    + constructor. reflexivity.
Qed.

Theorem run_cpu_rules_firing_bound : forall fuel old,
  (List.length (snd (run_cpu_rules fuel old)) <= fuel)%nat.
Proof.
  induction fuel as [|fuel IH]; intro old; cbn [run_cpu_rules].
  - cbn. lia.
  - destruct (select_cpu_rule old (getRules thieleCore)) as [[name u]|] eqn:He.
    + specialize (IH (M.union u old)).
      destruct (run_cpu_rules fuel (M.union u old)) as [final labels].
      cbn [snd] in *. rewrite app_length. cbn. lia.
    + cbn. lia.
Qed.

Theorem run_cpu_rules_short_trace_disabled : forall fuel old,
  (List.length (snd (run_cpu_rules fuel old)) < fuel)%nat ->
  select_cpu_rule (fst (run_cpu_rules fuel old)) (getRules thieleCore) = None.
Proof.
  induction fuel as [|fuel IH]; intros old H; [cbn in H; lia|].
  cbn [run_cpu_rules] in *.
  destruct (select_cpu_rule old (getRules thieleCore)) as [[name u]|] eqn:He.
  - specialize (IH (M.union u old)).
    destruct (run_cpu_rules fuel (M.union u old)) as [final labels].
    cbn [fst snd] in *. apply IH. rewrite app_length in H. cbn in H. lia.
  - exact He.
Qed.

Theorem cpu_reset_has_selected_rule : exists name u,
  select_cpu_rule dispatch_reset_state (getRules thieleCore) = Some (name, u).
Proof.
  destruct (select_cpu_rule dispatch_reset_state (getRules thieleCore))
    as [[name u]|] eqn:Hs.
  - exists name, u. reflexivity.
  - pose proof (proj1 (cpu_selection_none_iff _) Hs) as Hnone.
    pose proof dispatch_reset_enabled as Henabled.
    destruct (eval_dispatch dispatch_reset_state) as [u|] eqn:He;
      [|discriminate].
    exfalso. eapply (Hnone dispatch_rule u (M.empty _) WO dispatch_rule_in).
    apply dispatch_actual_action_iff. exact He.
Qed.
