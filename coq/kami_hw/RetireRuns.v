(** RetireRuns.v: executions chosen by the actual priority scheduler.

    [Runs c d n]: from boundary [c], [n] successive firings of the rule that
    [select_boundary_rule] picks reach [d]. Every such run is the concrete
    runner's result ([runs_runner]) and an actual Kami execution
    ([runs_multistep]). Selection lemmas cover the step rule at a live
    boundary and the LASSERT and CHSH FSM phases; the coupling FSM phases are
    in [CouplingSchedule]. [runs_loop_inner] and [runs_loop_outer] turn a
    per-iteration selection fact into a run of an iterator. *)
Require Import Kami.Kami Kami.Semantics.
From Coq Require Import List String Bool Lia Arith.
From KamiHW Require Import ThieleTypes ThieleCPUCore HWBoundary CoreRules CoreExecution
  RuleStep RuleEnabled BoundaryRun FsmDecoded ChshDecoded DispatchExecution NormalizationSteps
  NormalizationExecution CouplingSchedule.
Import ListNotations.
Local Open Scope nat_scope.

Inductive Runs : HWB -> HWB -> nat -> Prop :=
| runs_done : forall c, Runs c c 0
| runs_fire : forall c name c' d n,
    select_boundary_rule c (getRules thieleCore) = Some (name, c') ->
    Runs c' d n -> Runs c d (S n).

Theorem runs_runner : forall c d n, Runs c d n ->
  forall j, fst (run_boundary_rules (n + j) c) = fst (run_boundary_rules j d).
Proof.
  induction 1 as [c|c name c' d n Hsel Hr IH]; intro j; [reflexivity|].
  cbn [Nat.add run_boundary_rules]. rewrite Hsel.
  specialize (IH j). destruct (run_boundary_rules (n + j) c') as [f l]. exact IH.
Qed.

Corollary runs_runner_exact : forall c d n, Runs c d n -> fst (run_boundary_rules n c) = d.
Proof. intros c d n H. rewrite <- (Nat.add_0_r n). exact (runs_runner c d n H 0). Qed.

Theorem runs_trans : forall a b n, Runs a b n -> forall c m, Runs b c m -> Runs a c (n + m).
Proof.
  induction 1 as [a|a name a' b n Hsel Hr IH]; intros c m H; [exact H|].
  cbn [Nat.add]. exact (runs_fire a name a' c (n + m) Hsel (IH c m H)).
Qed.

Theorem runs_multistep : forall c d n, Runs c d n ->
  exists l, Multistep thieleCore (hwb_regs c) (hwb_regs d) l.
Proof.
  intros c d n H. exists (snd (run_boundary_rules n c)).
  rewrite <- (runs_runner_exact c d n H). apply run_boundary_rules_actual.
Qed.

Lemma runs_one : forall c name c', select_boundary_rule c (getRules thieleCore) = Some (name, c') ->
  Runs c c' 1.
Proof. intros c name c' H. exact (runs_fire c name c' c' 0 H (runs_done c')). Qed.

(** * Busy runs

    A boundary is idle when all three FSM phases are zero, and busy
    otherwise. [Busy_runs c d n] is a [Runs] whose every firing starts at a
    busy boundary: the FSM part of one instruction. Its idle end is unique. *)

Definition hw_idle (c : HWB) : Prop :=
  hw_lassert_phase c = natToWord 3 0 /\ hw_chsh_phase c = natToWord 5 0 /\ hw_mc_phase c = natToWord 4 0.

Inductive Busy_runs : HWB -> HWB -> nat -> Prop :=
| busy_done : forall c, Busy_runs c c 0
| busy_fire : forall c name c' d n, ~ hw_idle c ->
    select_boundary_rule c (getRules thieleCore) = Some (name, c') ->
    Busy_runs c' d n -> Busy_runs c d (S n).

Lemma busy_runs_runs : forall c d n, Busy_runs c d n -> Runs c d n.
Proof. induction 1; [apply runs_done|eapply runs_fire; eassumption]. Qed.

Theorem busy_runs_trans : forall a b n, Busy_runs a b n -> forall c m, Busy_runs b c m -> Busy_runs a c (n + m).
Proof.
  induction 1 as [a|a name a' b n Hb Hsel Hr IH]; intros c m H; [exact H|].
  cbn [Nat.add]. exact (busy_fire a name a' c (n + m) Hb Hsel (IH c m H)).
Qed.

Theorem busy_runs_unique : forall c d n, Busy_runs c d n -> hw_idle d ->
  forall d' n', Busy_runs c d' n' -> hw_idle d' -> d = d' /\ n = n'.
Proof.
  induction 1 as [c|c name c' d n Hb Hsel Hr IH]; intros Hd d' n' H' Hd'.
  - inversion H' as [|c0 name0 c0' d0 n0 Hb0]; subst; [split; reflexivity|contradiction].
  - inversion H' as [|c0 name0 c0' d0 n0 Hb0 Hsel0 Hr0]; subst; [contradiction|].
    rewrite Hsel in Hsel0. injection Hsel0 as _ E. subst c0'.
    destruct (IH Hd d' n0 Hr0 Hd') as [E1 E2]. subst. split; reflexivity.
Qed.

Lemma busy_one : forall c name c', ~ hw_idle c ->
  select_boundary_rule c (getRules thieleCore) = Some (name, c') -> Busy_runs c c' 1.
Proof. intros c name c' Hb H. exact (busy_fire c name c' c' 0 Hb H (busy_done c')). Qed.

Ltac word_neq := let E := fresh "E" in intro E; apply (f_equal (@wordToNat _)) in E; vm_compute in E; discriminate E.

Lemma busy_mc : forall c k, hw_mc_phase c = natToWord 4 k -> natToWord 4 k <> natToWord 4 0 -> ~ hw_idle c.
Proof. intros c k H N [_ [_ M]]. rewrite H in M. exact (N M). Qed.

Lemma busy_lassert : forall c k, hw_lassert_phase c = natToWord 3 k -> natToWord 3 k <> natToWord 3 0 -> ~ hw_idle c.
Proof. intros c k H N [L _]. rewrite H in L. exact (N L). Qed.

Lemma busy_chsh : forall c, hw_chsh_phase c <> natToWord 5 0 -> ~ hw_idle c.
Proof. intros c H [_ [C _]]. exact (H C). Qed.

(** * Iterators *)

Lemma runs_loop_inner : forall (f : HWB -> HWB) (iter : nat -> HWB -> HWB) name,
  (forall c, iter 0 c = c) -> (forall n c, iter (S n) c = iter n (f c)) ->
  forall n c, (forall m, m < n -> ~ hw_idle (iter m c) /\
                select_boundary_rule (iter m c) (getRules thieleCore) = Some (name, f (iter m c))) ->
  Busy_runs c (iter n c) n.
Proof.
  intros f iter name H0 HS. induction n as [|n IH]; intros c H.
  - rewrite H0. apply busy_done.
  - rewrite HS. destruct (H 0 ltac:(lia)) as [B E]. rewrite H0 in B, E.
    apply (busy_fire c name (f c) _ _ B E).
    apply IH. intros m Hm. pose proof (H (S m) ltac:(lia)) as E'. rewrite HS in E'. exact E'.
Qed.

Lemma runs_loop_outer : forall (f : HWB -> HWB) (iter : nat -> HWB -> HWB) name,
  (forall c, iter 0 c = c) -> (forall n c, iter (S n) c = f (iter n c)) ->
  forall n c, (forall m, m < n -> ~ hw_idle (iter m c) /\
                select_boundary_rule (iter m c) (getRules thieleCore) = Some (name, f (iter m c))) ->
  Busy_runs c (iter n c) n.
Proof.
  intros f iter name H0 HS. induction n as [|n IH]; intros c H.
  - rewrite H0. apply busy_done.
  - destruct (H n ltac:(lia)) as [B E].
    assert (R : Busy_runs (iter n c) (iter (S n) c) 1) by (rewrite HS; exact (busy_one _ name _ B E)).
    pose proof (busy_runs_trans c (iter n c) n (IH c (fun m Hm => H m ltac:(lia))) (iter (S n) c) 1 R) as T.
    rewrite Nat.add_1_r in T. exact T.
Qed.

(** * Selection *)

Theorem live_step_selected : forall b, hw_live b ->
  select_boundary_rule b (getRules thieleCore) = Some ("step", step_next b).
Proof.
  intros b Hlive. pose proof Hlive as [Hh [He [Hl [Hm Hc]]]].
  destruct (step_rule_enabled b Hh He Hl Hm Hc) as [u Hu].
  rewrite <- dispatch_rule_name, <- step_rule_next.
  eapply select_boundary_unique with (u := u).
  - rewrite cpu_rules_listed. apply in_map. cbn [In]. auto.
  - rewrite eval_cpu_rule_dispatch. exact Hu.
  - intros r Hin Hr. exact (live_only_step_enabled b r Hlive Hin Hr).
Qed.

Lemma phase_disables_step : forall b,
  hw_lassert_phase b <> natToWord 3 0 \/ hw_chsh_phase b <> natToWord 5 0 ->
  eval_cpu_rule (hwb_regs b) dispatch_rule = None.
Proof.
  intros b H. rewrite eval_cpu_rule_dispatch. apply step_rule_disabled.
  unfold step_guards.
  destruct H as [H|H].
  - destruct (weq (hw_lassert_phase b) (natToWord 3 0)); [contradiction|].
    cbn [andb]. rewrite !andb_false_r. reflexivity.
  - destruct (weq (hw_chsh_phase b) (natToWord 5 0)); [contradiction|].
    rewrite !andb_false_r. reflexivity.
Qed.

Ltac only_rule Hin Hr :=
  rewrite cpu_rules_listed in Hin; apply in_map_iff in Hin;
  let n := fresh "n" in let Hrn := fresh "Hrn" in let Hn := fresh "Hn" in
  destruct Hin as [n [Hrn Hn]]; subst; cbn [In] in Hn;
  repeat destruct Hn as [Hn|Hn]; try contradiction; subst n;
    try reflexivity; exfalso; apply Hr.

Theorem lhdr_phase_selected : forall b,
  hw_lassert_phase b = natToWord 3 1 -> hw_chsh_phase b = natToWord 5 0 -> hw_mc_phase b = natToWord 4 0 ->
  select_boundary_rule b (getRules thieleCore) = Some (attrName (normalization_rule 1), lhdr_next b).
Proof.
  intros b Hl Hc Hm. rewrite <- lhdr_rule_next.
  destruct (lhdr_enabled b ltac:(cbn [evalExpr evalConstT]; rewrite Hl; reflexivity)) as [u [Hu _]].
  eapply select_boundary_unique with (u := u); [rewrite cpu_rules_listed; apply in_map; cbn [In]; auto 13|exact Hu|].
  intros r Hin Hr. only_rule Hin Hr.
  - change (normalization_rule 0) with dispatch_rule. apply phase_disables_step. left. rewrite Hl. discriminate.
  - apply lassert_fsm_scan_disabled. rewrite Hl. discriminate.
  - apply mc_morph_header_disabled. rewrite Hm. discriminate.
  - apply mc_morph_loop_disabled. rewrite Hm. discriminate.
  - apply mc_copy_loop_disabled. rewrite Hm. discriminate.
  - apply mc_join_loop_disabled. rewrite Hm. discriminate.
  - apply mc_normalize_start_disabled. rewrite Hm. discriminate.
  - apply mc_normalize_scan_disabled. rewrite Hm. discriminate.
  - apply mc_normalize_emit_disabled. rewrite Hm. discriminate.
  - apply mc_commit_disabled. rewrite Hm. discriminate.
  - apply chsh_lassert_fsm_disabled. exact Hc.
Qed.

Theorem lscan_phase_selected : forall b,
  hw_lassert_phase b = natToWord 3 2 -> hw_chsh_phase b = natToWord 5 0 -> hw_mc_phase b = natToWord 4 0 ->
  select_boundary_rule b (getRules thieleCore) = Some (attrName (normalization_rule 2), lscan_next b).
Proof.
  intros b Hl Hc Hm. rewrite <- lscan_rule_next.
  destruct (lscan_enabled b ltac:(cbn [evalExpr evalConstT]; rewrite Hl; reflexivity)) as [u [Hu _]].
  eapply select_boundary_unique with (u := u); [rewrite cpu_rules_listed; apply in_map; cbn [In]; auto 13|exact Hu|].
  intros r Hin Hr. only_rule Hin Hr.
  - change (normalization_rule 0) with dispatch_rule. apply phase_disables_step. left. rewrite Hl. discriminate.
  - apply lassert_fsm_header_disabled. rewrite Hl. discriminate.
  - apply mc_morph_header_disabled. rewrite Hm. discriminate.
  - apply mc_morph_loop_disabled. rewrite Hm. discriminate.
  - apply mc_copy_loop_disabled. rewrite Hm. discriminate.
  - apply mc_join_loop_disabled. rewrite Hm. discriminate.
  - apply mc_normalize_start_disabled. rewrite Hm. discriminate.
  - apply mc_normalize_scan_disabled. rewrite Hm. discriminate.
  - apply mc_normalize_emit_disabled. rewrite Hm. discriminate.
  - apply mc_commit_disabled. rewrite Hm. discriminate.
  - apply chsh_lassert_fsm_disabled. exact Hc.
Qed.

Theorem chsh_phase_selected : forall b,
  hw_chsh_phase b <> natToWord 5 0 -> hw_lassert_phase b = natToWord 3 0 -> hw_mc_phase b = natToWord 4 0 ->
  select_boundary_rule b (getRules thieleCore) = Some (attrName chsh_rule, chsh_next b).
Proof.
  intros b Hc Hl Hm. rewrite <- chsh_rule_next.
  destruct (chsh_rule_enabled b Hc) as [u [Hu _]].
  eapply select_boundary_unique with (u := u); [unfold chsh_rule; rewrite cpu_rules_listed; apply in_map; cbn [In]; auto 13|exact Hu|].
  intros r Hin Hr. unfold chsh_rule. only_rule Hin Hr.
  - change (normalization_rule 0) with dispatch_rule. apply phase_disables_step. right. exact Hc.
  - apply lassert_fsm_header_disabled. rewrite Hl. discriminate.
  - apply lassert_fsm_scan_disabled. rewrite Hl. discriminate.
  - apply mc_morph_header_disabled. rewrite Hm. discriminate.
  - apply mc_morph_loop_disabled. rewrite Hm. discriminate.
  - apply mc_copy_loop_disabled. rewrite Hm. discriminate.
  - apply mc_join_loop_disabled. rewrite Hm. discriminate.
  - apply mc_normalize_start_disabled. rewrite Hm. discriminate.
  - apply mc_normalize_scan_disabled. rewrite Hm. discriminate.
  - apply mc_normalize_emit_disabled. rewrite Hm. discriminate.
  - apply mc_commit_disabled. rewrite Hm. discriminate.
Qed.

(** At a boundary with every phase idle and err or halted set, no rule is
    enabled: the runner stops. *)
Theorem stopped_boundary_idle : forall b,
  hw_lassert_phase b = natToWord 3 0 -> hw_chsh_phase b = natToWord 5 0 -> hw_mc_phase b = natToWord 4 0 ->
  hw_halted b = true \/ hw_err b = true ->
  select_boundary_rule b (getRules thieleCore) = None.
Proof.
  intros b Hl Hc Hm Hstop.
  assert (All : forall r, In r (getRules thieleCore) -> eval_cpu_rule (hwb_regs b) r = None).
  { intros r Hin. rewrite cpu_rules_listed in Hin. apply in_map_iff in Hin.
    destruct Hin as [n [Hrn Hn]]. subst r. cbn [In] in Hn.
    repeat destruct Hn as [Hn|Hn]; try contradiction; subst n.
    - change (normalization_rule 0) with dispatch_rule. rewrite eval_cpu_rule_dispatch.
      apply step_rule_disabled. unfold step_guards.
      destruct Hstop as [H|H]; rewrite H; cbn [negb andb]; [reflexivity|].
      destruct (hw_halted b); reflexivity.
    - apply lassert_fsm_header_disabled. rewrite Hl. discriminate.
    - apply lassert_fsm_scan_disabled. rewrite Hl. discriminate.
    - apply mc_morph_header_disabled. rewrite Hm. discriminate.
    - apply mc_morph_loop_disabled. rewrite Hm. discriminate.
    - apply mc_copy_loop_disabled. rewrite Hm. discriminate.
    - apply mc_join_loop_disabled. rewrite Hm. discriminate.
    - apply mc_normalize_start_disabled. rewrite Hm. discriminate.
    - apply mc_normalize_scan_disabled. rewrite Hm. discriminate.
    - apply mc_normalize_emit_disabled. rewrite Hm. discriminate.
    - apply mc_commit_disabled. rewrite Hm. discriminate.
    - apply chsh_lassert_fsm_disabled. exact Hc. }
  generalize (getRules thieleCore) All. intro rules. induction rules as [|r rest IH]; intro H; [reflexivity|].
  cbn [select_boundary_rule]. rewrite (H r (or_introl eq_refl)). apply IH.
  intros s Hs. apply H. right. exact Hs.
Qed.
