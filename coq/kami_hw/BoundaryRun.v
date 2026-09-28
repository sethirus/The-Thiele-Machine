(** The actual priority scheduler on typed hardware boundaries.  Selection
    evaluates the same rules in the same order as [run_cpu_rules]; the next
    boundary is obtained from the selected rule's observed writes. *)
Require Import Kami.Kami Kami.Semantics.
From Coq Require Import List String Lia.
From KamiHW Require Import ThieleCPUCore HWBoundary CoreRules CoreExecution
  RuleStep NormalizationExecution.
Import ListNotations.
Open Scope list_scope.

Fixpoint select_boundary_rule (b : HWB) (rules : list cpu_rule)
    : option (string * HWB) :=
  match rules with
  | nil => None
  | cons r rest =>
      match eval_cpu_rule (hwb_regs b) r with
      | Some _ => Some (attrName r, rule_next r b)
      | None => select_boundary_rule b rest
      end
  end.

Lemma select_boundary_rule_correct : forall rules b,
  (forall r, In r rules -> In r (getRules thieleCore)) ->
  option_map (fun '(name, next) => (name, hwb_regs next))
    (select_boundary_rule b rules) =
  option_map (fun '(name, u) => (name, M.union u (hwb_regs b)))
    (select_cpu_rule (hwb_regs b) rules).
Proof.
  induction rules as [|r rest IH]; intros b Hin; [reflexivity|].
  cbn [select_boundary_rule select_cpu_rule].
  destruct (eval_cpu_rule (hwb_regs b) r) as [u|] eqn:He.
  - cbn [option_map]. rewrite (rule_next_correct r b u (Hin r (or_introl eq_refl)) He).
    reflexivity.
  - apply IH. intros s Hs. apply Hin. right. exact Hs.
Qed.

Lemma select_boundary_unique : forall rules b chosen u,
  In chosen rules -> eval_cpu_rule (hwb_regs b) chosen = Some u ->
  (forall r, In r rules -> eval_cpu_rule (hwb_regs b) r <> None -> r = chosen) ->
  select_boundary_rule b rules = Some (attrName chosen, rule_next chosen b).
Proof.
  induction rules as [|r rest IH]; intros b chosen u Hin He Honly;
    [contradiction|].
  cbn [select_boundary_rule].
  destruct (eval_cpu_rule (hwb_regs b) r) as [updates|] eqn:Hr.
  - assert (r = chosen) by (apply Honly; [left; reflexivity|congruence]).
    subst r. reflexivity.
  - apply (IH b chosen u).
    + destruct Hin as [E|Hin]; [subst r; congruence|exact Hin].
    + exact He.
    + intros s Hs. apply Honly. right. exact Hs.
Qed.

Fixpoint run_boundary_rules (fuel : nat) (b : HWB) : HWB * list LabelT :=
  match fuel with
  | 0 => (b, nil)
  | S n =>
      match select_boundary_rule b (getRules thieleCore) with
      | None => (b, nil)
      | Some (name, next) =>
          let '(final, labels) := run_boundary_rules n next in
          (final, labels ++ [normalization_label name])
      end
  end.

Theorem run_boundary_rules_correct : forall fuel b,
  (hwb_regs (fst (run_boundary_rules fuel b)), snd (run_boundary_rules fuel b)) =
  run_cpu_rules fuel (hwb_regs b).
Proof.
  induction fuel as [|fuel IH]; intro b; [reflexivity|].
  pose proof (select_boundary_rule_correct (getRules thieleCore) b
    (fun r H => H)) as Hselect.
  cbn [run_boundary_rules run_cpu_rules].
  destruct (select_boundary_rule b (getRules thieleCore)) as [[name next]|];
    destruct (select_cpu_rule (hwb_regs b) (getRules thieleCore)) as [[name' u]|];
    cbn [option_map] in Hselect; try discriminate; [|reflexivity].
  inversion Hselect as [[Hname Hnext]]. subst name'.
  rewrite <- (IH next).
  destruct (run_boundary_rules fuel next) as [final labels]. reflexivity.
Qed.

Theorem run_boundary_rules_actual : forall fuel b,
  Multistep thieleCore (hwb_regs b)
    (hwb_regs (fst (run_boundary_rules fuel b)))
    (snd (run_boundary_rules fuel b)).
Proof.
  intros fuel b. pose proof (run_cpu_rules_actual fuel (hwb_regs b)) as H.
  rewrite <- run_boundary_rules_correct in H. exact H.
Qed.

Theorem run_boundary_rules_firing_bound : forall fuel b,
  (List.length (snd (run_boundary_rules fuel b)) <= fuel)%nat.
Proof.
  intros fuel b. pose proof (run_cpu_rules_firing_bound fuel (hwb_regs b)) as H.
  rewrite <- run_boundary_rules_correct in H. exact H.
Qed.

Theorem run_boundary_rules_short_trace_disabled : forall fuel b,
  (List.length (snd (run_boundary_rules fuel b)) < fuel)%nat ->
  select_boundary_rule (fst (run_boundary_rules fuel b)) (getRules thieleCore) = None.
Proof.
  intros fuel b Hlen.
  pose proof (run_cpu_rules_short_trace_disabled fuel (hwb_regs b)) as H.
  rewrite <- run_boundary_rules_correct in H. specialize (H Hlen).
  pose proof (select_boundary_rule_correct (getRules thieleCore)
    (fst (run_boundary_rules fuel b)) (fun r H => H)) as Hselect.
  cbn [fst snd] in H. rewrite H in Hselect.
  destruct (select_boundary_rule (fst (run_boundary_rules fuel b))
    (getRules thieleCore)) as [[name next]|]; [discriminate|reflexivity].
Qed.
