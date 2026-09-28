(** Every actual CPU rule firing as a total Gallina function on the typed
    boundary. [rule_next r b] is defined by observing the rule's own writes;
    [rule_next_correct] proves that a successful evaluation of the rule updates
    [hwb_regs b] to exactly [hwb_regs (rule_next r b)]. The step rule also has a
    decoded form over the fetched instruction word. No opcode, reachability or
    arithmetic premise is used. *)
Require Import Kami.Kami Kami.Semantics.
From Coq Require Import String List.
From KamiHW Require Import ThieleTypes ThieleCPUCore HWBoundary ActionEvaluator
  ActionObservation CoreRules CoreTyping CoreExecution RuleNext DispatchExecution
  DispatchObservation DispatchFetch BoundaryDecoded.
Import ListNotations.
Open Scope string_scope.

Definition rule_next (r : cpu_rule) (b : HWB) : HWB :=
  hwb_after b (fun key => observe_action_write (hwb_regs b) key (attrType r type)).

Theorem rule_next_correct : forall r b u,
  In r (getRules thieleCore) ->
  eval_cpu_rule (hwb_regs b) r = Some u ->
  M.union u (hwb_regs b) = hwb_regs (rule_next r b).
Proof.
  intros r b u Hin He. unfold eval_cpu_rule in He.
  destruct (eval_linear_action (hwb_regs b) (attrType r type)) as [[u' ret]|] eqn:Hr;
    [|discriminate].
  inversion He; subst u'.
  pose proof (proj1 (Forall_forall _ _) cpu_writes_declared r Hin) as Hd.
  pose proof (proj1 (Forall_forall _ _) cpu_rules_linear r Hin) as Hl.
  rewrite (hwb_after_union b u (evaluated_updates_match _ _ _ _ _ _ Hd Hr)).
  unfold rule_next. f_equal. apply hwb_after_ext. intro key.
  symmetry. eapply observe_action_write_correct; [exact Hl|].
  apply eval_linear_action_sound. exact Hr.
Qed.

Lemma dispatch_with_own_imem : forall b,
  dispatch_with_imem b (hw_imem b) = hwb_regs b.
Proof.
  intro b. M.ext name. unfold dispatch_with_imem.
  destruct (string_dec name "imem") as [E|N].
  - subst name. rewrite M.find_add_1. reflexivity.
  - rewrite M.find_add_2 by exact N. reflexivity.
Qed.

(** The step rule after its fetch: every write is an observation of the
    decoded action applied to the fetched word. *)
Definition step_fetched (b : HWB) : word InstrSz :=
  hw_imem b (dispatch_fetch_address b).

Definition step_next (b : HWB) : HWB :=
  hwb_after b (fun key =>
    observe_action_write (M.empty _) key (hwb_decoded b (step_fetched b))).

Lemma step_rule_next : forall b, rule_next dispatch_rule b = step_next b.
Proof.
  intro b. unfold rule_next, step_next. apply hwb_after_ext. intro key.
  change (observe_dispatch_write (hwb_regs b) key =
    observe_action_write (M.empty _) key (hwb_decoded b (step_fetched b))).
  rewrite <- dispatch_with_own_imem at 1.
  apply dispatch_boundary_decoded_observer.
Qed.

Lemma eval_cpu_rule_dispatch : forall old,
  eval_cpu_rule old dispatch_rule = eval_dispatch old.
Proof. intro old. unfold eval_cpu_rule, eval_dispatch. reflexivity. Qed.

Theorem step_next_correct : forall b u,
  eval_dispatch (hwb_regs b) = Some u ->
  M.union u (hwb_regs b) = hwb_regs (step_next b).
Proof.
  intros b u He. rewrite <- step_rule_next.
  apply rule_next_correct; [exact dispatch_rule_in|].
  rewrite eval_cpu_rule_dispatch. exact He.
Qed.

(** The step rule's next state depends on the instruction memory only through
    the fetched word. *)
Lemma step_next_fetched : forall b w,
  step_fetched b = w ->
  step_next b = hwb_after b (fun key =>
    observe_action_write (M.empty _) key (hwb_decoded b w)).
Proof. intros b w H. unfold step_next. rewrite H. reflexivity. Qed.
