(** Exclusivity and enabledness for every coupling FSM phase, at arbitrary
    typed boundaries whose other FSMs are idle. *)
Require Import Kami.Kami Kami.Semantics.
From Coq Require Import List String Bool Lia.
From KamiHW Require Import ThieleCPUCore HWBoundary CoreRules CoreExecution
  RuleStep RuleEnabled BoundaryRun FsmDecoded DispatchExecution NormalizationSteps
  NormalizationExecution.
Import ListNotations.

Lemma coupling_disables_step : forall b,
  hw_mc_phase b <> natToWord 4 0 ->
  eval_cpu_rule (hwb_regs b) dispatch_rule = None.
Proof.
  intros b H. rewrite eval_cpu_rule_dispatch. apply step_rule_disabled.
  unfold step_guards. destruct (weq (hw_mc_phase b) (natToWord 4 0));
    [contradiction|]. cbn [andb]. rewrite !andb_false_r. reflexivity.
Qed.

Theorem mchdr_only_rule_enabled : forall b r,
  hw_lassert_phase b = natToWord 3 0 ->
  hw_chsh_phase b = natToWord 5 0 ->
  hw_mc_phase b = natToWord 4 1 ->
  In r (getRules thieleCore) ->
  eval_cpu_rule (hwb_regs b) r <> None -> r = normalization_rule 3.
Proof.
  intros b r Hl Hc Hp Hin Hr.
  rewrite cpu_rules_listed in Hin. apply in_map_iff in Hin.
  destruct Hin as [n [Hrn Hn]]. subst r. cbn [In] in Hn.
  repeat destruct Hn as [Hn|Hn]; try contradiction; subst n;
    try reflexivity; exfalso; apply Hr.
  - change (normalization_rule 0) with dispatch_rule.
    apply coupling_disables_step. rewrite Hp. discriminate.
  - apply lassert_fsm_header_disabled. rewrite Hl. discriminate.
  - apply lassert_fsm_scan_disabled. rewrite Hl. discriminate.
  - apply mc_morph_loop_disabled. rewrite Hp. discriminate.
  - apply mc_copy_loop_disabled. rewrite Hp. discriminate.
  - apply mc_join_loop_disabled. rewrite Hp. discriminate.
  - apply mc_normalize_start_disabled. rewrite Hp. discriminate.
  - apply mc_normalize_scan_disabled. rewrite Hp. discriminate.
  - apply mc_normalize_emit_disabled. rewrite Hp. discriminate.
  - apply mc_commit_disabled. rewrite Hp. discriminate.
  - apply chsh_lassert_fsm_disabled. exact Hc.
Qed.

Theorem mchdr_phase_enabled : forall b,
  hw_mc_phase b = natToWord 4 1 ->
  exists u, eval_cpu_rule (hwb_regs b) (normalization_rule 3) = Some u /\
    M.union u (hwb_regs b) = hwb_regs (mchdr_next b).
Proof.
  intros b Hp. apply mchdr_enabled.
  cbn [evalExpr evalConstT evalUniBool]. rewrite Hp.
  reflexivity.
Qed.

Theorem mcload_only_rule_enabled : forall b r,
  hw_lassert_phase b = natToWord 3 0 ->
  hw_chsh_phase b = natToWord 5 0 ->
  hw_mc_phase b = natToWord 4 2 ->
  In r (getRules thieleCore) ->
  eval_cpu_rule (hwb_regs b) r <> None -> r = normalization_rule 4.
Proof.
  intros b r Hl Hc Hp Hin Hr.
  rewrite cpu_rules_listed in Hin. apply in_map_iff in Hin.
  destruct Hin as [n [Hrn Hn]]. subst r. cbn [In] in Hn.
  repeat destruct Hn as [Hn|Hn]; try contradiction; subst n;
    try reflexivity; exfalso; apply Hr.
  - change (normalization_rule 0) with dispatch_rule.
    apply coupling_disables_step. rewrite Hp. discriminate.
  - apply lassert_fsm_header_disabled. rewrite Hl. discriminate.
  - apply lassert_fsm_scan_disabled. rewrite Hl. discriminate.
  - apply mc_morph_header_disabled. rewrite Hp. discriminate.
  - apply mc_copy_loop_disabled. rewrite Hp. discriminate.
  - apply mc_join_loop_disabled. rewrite Hp. discriminate.
  - apply mc_normalize_start_disabled. rewrite Hp. discriminate.
  - apply mc_normalize_scan_disabled. rewrite Hp. discriminate.
  - apply mc_normalize_emit_disabled. rewrite Hp. discriminate.
  - apply mc_commit_disabled. rewrite Hp. discriminate.
  - apply chsh_lassert_fsm_disabled. exact Hc.
Qed.

Theorem mcload_phase_enabled : forall b,
  hw_mc_phase b = natToWord 4 2 ->
  exists u, eval_cpu_rule (hwb_regs b) (normalization_rule 4) = Some u /\
    M.union u (hwb_regs b) = hwb_regs (mcload_next b).
Proof.
  intros b Hp. apply mcload_enabled.
  cbn [evalExpr evalConstT evalUniBool]. rewrite Hp.
  reflexivity.
Qed.

Theorem mccopy_only_rule_enabled : forall b r,
  hw_lassert_phase b = natToWord 3 0 ->
  hw_chsh_phase b = natToWord 5 0 ->
  hw_mc_phase b = natToWord 4 4 ->
  In r (getRules thieleCore) ->
  eval_cpu_rule (hwb_regs b) r <> None -> r = normalization_rule 5.
Proof.
  intros b r Hl Hc Hp Hin Hr.
  rewrite cpu_rules_listed in Hin. apply in_map_iff in Hin.
  destruct Hin as [n [Hrn Hn]]. subst r. cbn [In] in Hn.
  repeat destruct Hn as [Hn|Hn]; try contradiction; subst n;
    try reflexivity; exfalso; apply Hr.
  - change (normalization_rule 0) with dispatch_rule.
    apply coupling_disables_step. rewrite Hp. discriminate.
  - apply lassert_fsm_header_disabled. rewrite Hl. discriminate.
  - apply lassert_fsm_scan_disabled. rewrite Hl. discriminate.
  - apply mc_morph_header_disabled. rewrite Hp. discriminate.
  - apply mc_morph_loop_disabled. rewrite Hp. discriminate.
  - apply mc_join_loop_disabled. rewrite Hp. discriminate.
  - apply mc_normalize_start_disabled. rewrite Hp. discriminate.
  - apply mc_normalize_scan_disabled. rewrite Hp. discriminate.
  - apply mc_normalize_emit_disabled. rewrite Hp. discriminate.
  - apply mc_commit_disabled. rewrite Hp. discriminate.
  - apply chsh_lassert_fsm_disabled. exact Hc.
Qed.

Theorem mccopy_phase_enabled : forall b,
  hw_mc_phase b = natToWord 4 4 ->
  exists u, eval_cpu_rule (hwb_regs b) (normalization_rule 5) = Some u /\
    M.union u (hwb_regs b) = hwb_regs (mccopy_next b).
Proof.
  intros b Hp. apply mccopy_enabled.
  cbn [evalExpr evalConstT evalUniBool]. rewrite Hp.
  reflexivity.
Qed.

Theorem mcjoin_only_rule_enabled : forall b r,
  hw_lassert_phase b = natToWord 3 0 ->
  hw_chsh_phase b = natToWord 5 0 ->
  hw_mc_phase b = natToWord 4 7 ->
  In r (getRules thieleCore) ->
  eval_cpu_rule (hwb_regs b) r <> None -> r = normalization_rule 6.
Proof.
  intros b r Hl Hc Hp Hin Hr.
  rewrite cpu_rules_listed in Hin. apply in_map_iff in Hin.
  destruct Hin as [n [Hrn Hn]]. subst r. cbn [In] in Hn.
  repeat destruct Hn as [Hn|Hn]; try contradiction; subst n;
    try reflexivity; exfalso; apply Hr.
  - change (normalization_rule 0) with dispatch_rule.
    apply coupling_disables_step. rewrite Hp. discriminate.
  - apply lassert_fsm_header_disabled. rewrite Hl. discriminate.
  - apply lassert_fsm_scan_disabled. rewrite Hl. discriminate.
  - apply mc_morph_header_disabled. rewrite Hp. discriminate.
  - apply mc_morph_loop_disabled. rewrite Hp. discriminate.
  - apply mc_copy_loop_disabled. rewrite Hp. discriminate.
  - apply mc_normalize_start_disabled. rewrite Hp. discriminate.
  - apply mc_normalize_scan_disabled. rewrite Hp. discriminate.
  - apply mc_normalize_emit_disabled. rewrite Hp. discriminate.
  - apply mc_commit_disabled. rewrite Hp. discriminate.
  - apply chsh_lassert_fsm_disabled. exact Hc.
Qed.

Theorem mcjoin_phase_enabled : forall b,
  hw_mc_phase b = natToWord 4 7 ->
  exists u, eval_cpu_rule (hwb_regs b) (normalization_rule 6) = Some u /\
    M.union u (hwb_regs b) = hwb_regs (mcjoin_next b).
Proof.
  intros b Hp. apply mcjoin_enabled.
  cbn [evalExpr evalConstT evalUniBool]. rewrite Hp.
  reflexivity.
Qed.

Theorem mcnstart_only_rule_enabled : forall b r,
  hw_lassert_phase b = natToWord 3 0 ->
  hw_chsh_phase b = natToWord 5 0 ->
  hw_mc_phase b = natToWord 4 5 ->
  In r (getRules thieleCore) ->
  eval_cpu_rule (hwb_regs b) r <> None -> r = normalization_rule 7.
Proof.
  intros b r Hl Hc Hp Hin Hr.
  rewrite cpu_rules_listed in Hin. apply in_map_iff in Hin.
  destruct Hin as [n [Hrn Hn]]. subst r. cbn [In] in Hn.
  repeat destruct Hn as [Hn|Hn]; try contradiction; subst n;
    try reflexivity; exfalso; apply Hr.
  - change (normalization_rule 0) with dispatch_rule.
    apply coupling_disables_step. rewrite Hp. discriminate.
  - apply lassert_fsm_header_disabled. rewrite Hl. discriminate.
  - apply lassert_fsm_scan_disabled. rewrite Hl. discriminate.
  - apply mc_morph_header_disabled. rewrite Hp. discriminate.
  - apply mc_morph_loop_disabled. rewrite Hp. discriminate.
  - apply mc_copy_loop_disabled. rewrite Hp. discriminate.
  - apply mc_join_loop_disabled. rewrite Hp. discriminate.
  - apply mc_normalize_scan_disabled. rewrite Hp. discriminate.
  - apply mc_normalize_emit_disabled. rewrite Hp. discriminate.
  - apply mc_commit_disabled. rewrite Hp. discriminate.
  - apply chsh_lassert_fsm_disabled. exact Hc.
Qed.

Theorem mcnstart_phase_enabled : forall b,
  hw_mc_phase b = natToWord 4 5 ->
  exists u, eval_cpu_rule (hwb_regs b) (normalization_rule 7) = Some u /\
    M.union u (hwb_regs b) = hwb_regs (mcnstart_next b).
Proof.
  intros b Hp. apply mcnstart_enabled.
  cbn [evalExpr evalConstT evalUniBool]. rewrite Hp.
  reflexivity.
Qed.

Theorem mcnscan_only_rule_enabled : forall b r,
  hw_lassert_phase b = natToWord 3 0 ->
  hw_chsh_phase b = natToWord 5 0 ->
  hw_mc_phase b = natToWord 4 8 ->
  In r (getRules thieleCore) ->
  eval_cpu_rule (hwb_regs b) r <> None -> r = normalization_rule 8.
Proof.
  intros b r Hl Hc Hp Hin Hr.
  rewrite cpu_rules_listed in Hin. apply in_map_iff in Hin.
  destruct Hin as [n [Hrn Hn]]. subst r. cbn [In] in Hn.
  repeat destruct Hn as [Hn|Hn]; try contradiction; subst n;
    try reflexivity; exfalso; apply Hr.
  - change (normalization_rule 0) with dispatch_rule.
    apply coupling_disables_step. rewrite Hp. discriminate.
  - apply lassert_fsm_header_disabled. rewrite Hl. discriminate.
  - apply lassert_fsm_scan_disabled. rewrite Hl. discriminate.
  - apply mc_morph_header_disabled. rewrite Hp. discriminate.
  - apply mc_morph_loop_disabled. rewrite Hp. discriminate.
  - apply mc_copy_loop_disabled. rewrite Hp. discriminate.
  - apply mc_join_loop_disabled. rewrite Hp. discriminate.
  - apply mc_normalize_start_disabled. rewrite Hp. discriminate.
  - apply mc_normalize_emit_disabled. rewrite Hp. discriminate.
  - apply mc_commit_disabled. rewrite Hp. discriminate.
  - apply chsh_lassert_fsm_disabled. exact Hc.
Qed.

Theorem mcnscan_phase_enabled : forall b,
  hw_mc_phase b = natToWord 4 8 ->
  exists u, eval_cpu_rule (hwb_regs b) (normalization_rule 8) = Some u /\
    M.union u (hwb_regs b) = hwb_regs (mcnscan_next b).
Proof.
  intros b Hp. apply mcnscan_enabled.
  cbn [evalExpr evalConstT evalUniBool]. rewrite Hp.
  reflexivity.
Qed.

Theorem mcnemit_only_rule_enabled : forall b r,
  hw_lassert_phase b = natToWord 3 0 ->
  hw_chsh_phase b = natToWord 5 0 ->
  hw_mc_phase b = natToWord 4 9 ->
  In r (getRules thieleCore) ->
  eval_cpu_rule (hwb_regs b) r <> None -> r = normalization_rule 9.
Proof.
  intros b r Hl Hc Hp Hin Hr.
  rewrite cpu_rules_listed in Hin. apply in_map_iff in Hin.
  destruct Hin as [n [Hrn Hn]]. subst r. cbn [In] in Hn.
  repeat destruct Hn as [Hn|Hn]; try contradiction; subst n;
    try reflexivity; exfalso; apply Hr.
  - change (normalization_rule 0) with dispatch_rule.
    apply coupling_disables_step. rewrite Hp. discriminate.
  - apply lassert_fsm_header_disabled. rewrite Hl. discriminate.
  - apply lassert_fsm_scan_disabled. rewrite Hl. discriminate.
  - apply mc_morph_header_disabled. rewrite Hp. discriminate.
  - apply mc_morph_loop_disabled. rewrite Hp. discriminate.
  - apply mc_copy_loop_disabled. rewrite Hp. discriminate.
  - apply mc_join_loop_disabled. rewrite Hp. discriminate.
  - apply mc_normalize_start_disabled. rewrite Hp. discriminate.
  - apply mc_normalize_scan_disabled. rewrite Hp. discriminate.
  - apply mc_commit_disabled. rewrite Hp. discriminate.
  - apply chsh_lassert_fsm_disabled. exact Hc.
Qed.

Theorem mcnemit_phase_enabled : forall b,
  hw_mc_phase b = natToWord 4 9 ->
  exists u, eval_cpu_rule (hwb_regs b) (normalization_rule 9) = Some u /\
    M.union u (hwb_regs b) = hwb_regs (mcnemit_next b).
Proof.
  intros b Hp. apply mcnemit_enabled.
  cbn [evalExpr evalConstT evalUniBool]. rewrite Hp.
  reflexivity.
Qed.

Theorem mccommit_only_rule_enabled : forall b r,
  hw_lassert_phase b = natToWord 3 0 ->
  hw_chsh_phase b = natToWord 5 0 ->
  hw_mc_phase b = natToWord 4 11 ->
  In r (getRules thieleCore) ->
  eval_cpu_rule (hwb_regs b) r <> None -> r = normalization_rule 10.
Proof.
  intros b r Hl Hc Hp Hin Hr.
  rewrite cpu_rules_listed in Hin. apply in_map_iff in Hin.
  destruct Hin as [n [Hrn Hn]]. subst r. cbn [In] in Hn.
  repeat destruct Hn as [Hn|Hn]; try contradiction; subst n;
    try reflexivity; exfalso; apply Hr.
  - change (normalization_rule 0) with dispatch_rule.
    apply coupling_disables_step. rewrite Hp. discriminate.
  - apply lassert_fsm_header_disabled. rewrite Hl. discriminate.
  - apply lassert_fsm_scan_disabled. rewrite Hl. discriminate.
  - apply mc_morph_header_disabled. rewrite Hp. discriminate.
  - apply mc_morph_loop_disabled. rewrite Hp. discriminate.
  - apply mc_copy_loop_disabled. rewrite Hp. discriminate.
  - apply mc_join_loop_disabled. rewrite Hp. discriminate.
  - apply mc_normalize_start_disabled. rewrite Hp. discriminate.
  - apply mc_normalize_scan_disabled. rewrite Hp. discriminate.
  - apply mc_normalize_emit_disabled. rewrite Hp. discriminate.
  - apply chsh_lassert_fsm_disabled. exact Hc.
Qed.

Theorem mccommit_phase_enabled : forall b,
  hw_mc_phase b = natToWord 4 11 ->
  exists u, eval_cpu_rule (hwb_regs b) (normalization_rule 10) = Some u /\
    M.union u (hwb_regs b) = hwb_regs (mccommit_next b).
Proof.
  intros b Hp. apply mccommit_enabled.
  cbn [evalExpr evalConstT evalUniBool]. rewrite Hp.
  reflexivity.
Qed.

Theorem mchdr_phase_selected : forall b,
  hw_lassert_phase b = natToWord 3 0 ->
  hw_chsh_phase b = natToWord 5 0 ->
  hw_mc_phase b = natToWord 4 1 ->
  select_boundary_rule b (getRules thieleCore) =
    Some (attrName (normalization_rule 3), mchdr_next b).
Proof.
  intros b Hl Hc Hp. rewrite <- mchdr_rule_next.
  destruct (mchdr_phase_enabled b Hp) as [u [Hu _]].
  eapply select_boundary_unique with (u := u).
  - rewrite cpu_rules_listed. apply in_map. cbn [In]. auto 13.
  - exact Hu.
  - intros r Hin Hr. eapply mchdr_only_rule_enabled; eassumption.
Qed.

Theorem mcload_phase_selected : forall b,
  hw_lassert_phase b = natToWord 3 0 ->
  hw_chsh_phase b = natToWord 5 0 ->
  hw_mc_phase b = natToWord 4 2 ->
  select_boundary_rule b (getRules thieleCore) =
    Some (attrName (normalization_rule 4), mcload_next b).
Proof.
  intros b Hl Hc Hp. rewrite <- mcload_rule_next.
  destruct (mcload_phase_enabled b Hp) as [u [Hu _]].
  eapply select_boundary_unique with (u := u).
  - rewrite cpu_rules_listed. apply in_map. cbn [In]. auto 13.
  - exact Hu.
  - intros r Hin Hr. eapply mcload_only_rule_enabled; eassumption.
Qed.

Theorem mccopy_phase_selected : forall b,
  hw_lassert_phase b = natToWord 3 0 ->
  hw_chsh_phase b = natToWord 5 0 ->
  hw_mc_phase b = natToWord 4 4 ->
  select_boundary_rule b (getRules thieleCore) =
    Some (attrName (normalization_rule 5), mccopy_next b).
Proof.
  intros b Hl Hc Hp. rewrite <- mccopy_rule_next.
  destruct (mccopy_phase_enabled b Hp) as [u [Hu _]].
  eapply select_boundary_unique with (u := u).
  - rewrite cpu_rules_listed. apply in_map. cbn [In]. auto 13.
  - exact Hu.
  - intros r Hin Hr. eapply mccopy_only_rule_enabled; eassumption.
Qed.

Theorem mcjoin_phase_selected : forall b,
  hw_lassert_phase b = natToWord 3 0 ->
  hw_chsh_phase b = natToWord 5 0 ->
  hw_mc_phase b = natToWord 4 7 ->
  select_boundary_rule b (getRules thieleCore) =
    Some (attrName (normalization_rule 6), mcjoin_next b).
Proof.
  intros b Hl Hc Hp. rewrite <- mcjoin_rule_next.
  destruct (mcjoin_phase_enabled b Hp) as [u [Hu _]].
  eapply select_boundary_unique with (u := u).
  - rewrite cpu_rules_listed. apply in_map. cbn [In]. auto 13.
  - exact Hu.
  - intros r Hin Hr. eapply mcjoin_only_rule_enabled; eassumption.
Qed.

Theorem mcnstart_phase_selected : forall b,
  hw_lassert_phase b = natToWord 3 0 ->
  hw_chsh_phase b = natToWord 5 0 ->
  hw_mc_phase b = natToWord 4 5 ->
  select_boundary_rule b (getRules thieleCore) =
    Some (attrName (normalization_rule 7), mcnstart_next b).
Proof.
  intros b Hl Hc Hp. rewrite <- mcnstart_rule_next.
  destruct (mcnstart_phase_enabled b Hp) as [u [Hu _]].
  eapply select_boundary_unique with (u := u).
  - rewrite cpu_rules_listed. apply in_map. cbn [In]. auto 13.
  - exact Hu.
  - intros r Hin Hr. eapply mcnstart_only_rule_enabled; eassumption.
Qed.

Theorem mcnscan_phase_selected : forall b,
  hw_lassert_phase b = natToWord 3 0 ->
  hw_chsh_phase b = natToWord 5 0 ->
  hw_mc_phase b = natToWord 4 8 ->
  select_boundary_rule b (getRules thieleCore) =
    Some (attrName (normalization_rule 8), mcnscan_next b).
Proof.
  intros b Hl Hc Hp. rewrite <- mcnscan_rule_next.
  destruct (mcnscan_phase_enabled b Hp) as [u [Hu _]].
  eapply select_boundary_unique with (u := u).
  - rewrite cpu_rules_listed. apply in_map. cbn [In]. auto 13.
  - exact Hu.
  - intros r Hin Hr. eapply mcnscan_only_rule_enabled; eassumption.
Qed.

Theorem mcnemit_phase_selected : forall b,
  hw_lassert_phase b = natToWord 3 0 ->
  hw_chsh_phase b = natToWord 5 0 ->
  hw_mc_phase b = natToWord 4 9 ->
  select_boundary_rule b (getRules thieleCore) =
    Some (attrName (normalization_rule 9), mcnemit_next b).
Proof.
  intros b Hl Hc Hp. rewrite <- mcnemit_rule_next.
  destruct (mcnemit_phase_enabled b Hp) as [u [Hu _]].
  eapply select_boundary_unique with (u := u).
  - rewrite cpu_rules_listed. apply in_map. cbn [In]. auto 13.
  - exact Hu.
  - intros r Hin Hr. eapply mcnemit_only_rule_enabled; eassumption.
Qed.

Theorem mccommit_phase_selected : forall b,
  hw_lassert_phase b = natToWord 3 0 ->
  hw_chsh_phase b = natToWord 5 0 ->
  hw_mc_phase b = natToWord 4 11 ->
  select_boundary_rule b (getRules thieleCore) =
    Some (attrName (normalization_rule 10), mccommit_next b).
Proof.
  intros b Hl Hc Hp. rewrite <- mccommit_rule_next.
  destruct (mccommit_phase_enabled b Hp) as [u [Hu _]].
  eapply select_boundary_unique with (u := u).
  - rewrite cpu_rules_listed. apply in_map. cbn [In]. auto 13.
  - exact Hu.
  - intros r Hin Hr. eapply mccommit_only_rule_enabled; eassumption.
Qed.

