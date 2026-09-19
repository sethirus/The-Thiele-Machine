(** RetireRunsFsm.v: the FSM runs of the multi-cycle instructions are the
    concrete scheduler's runs.

    Each loop of the LASSERT, CHSH and coupling FSMs, and each composite run
    used by a retirement theorem ([norm_commit_final], [compose_fsm_final],
    [morph_fsm_final]), is a [Busy_runs] from its start boundary: at every
    intermediate boundary the scheduler selects exactly the rule the run
    fires. *)
Require Import Kami.Kami Kami.Semantics Kami.Lib.NatLib.
From Coq Require Import String List Arith Lia Bool.
Import ListNotations.
From KamiHW Require Import ThieleTypes ThieleCPUCore HWBoundary RuleNext RuleStep ActionEvaluator
  CoreRules CoreExecution NormalizationSteps NormalizationExecution NormalizationRetirement
  NormalizationLoop NormalizationPrefix NormalizationScanExecution NormalizationFrame MorphLoading
  MorphCopy MorphJoin RuleEnabled FsmDecoded ChshDecoded ChshRun CouplingFsmEnds CouplingFsmLoad
  CouplingFsmNorm CouplingFsmRun CouplingFsmCopy CouplingFsmJoin CouplingSchedule LassertWord
  CouplingComposeRun CouplingComposeRetire BoundaryRun RetireRuns.
Local Open Scope nat_scope.
Local Open Scope list_scope.

(** * Loops *)

Lemma copy_runs : forall n c,
  hw_lassert_phase c = natToWord 3 0 -> hw_chsh_phase c = natToWord 5 0 ->
  (forall m, m < n -> hw_mc_phase (copy_iter m c) = natToWord 4 4) ->
  Busy_runs c (copy_iter n c) n.
Proof.
  intros n c Hl Hc H. apply (runs_loop_inner mccopy_next copy_iter (attrName (normalization_rule 5)) (fun _ => eq_refl) (fun _ _ => eq_refl)).
  intros m Hm. split; [apply (busy_mc _ 4 (H m Hm)); try word_neq|]. apply mccopy_phase_selected;
    [rewrite copy_iter_keeps_lassert_phase; exact Hl|rewrite copy_iter_keeps_chsh_phase; exact Hc|exact (H m Hm)].
Qed.

Lemma join_runs : forall n c,
  hw_lassert_phase c = natToWord 3 0 -> hw_chsh_phase c = natToWord 5 0 ->
  (forall m, m < n -> hw_mc_phase (join_iter m c) = natToWord 4 7) ->
  Busy_runs c (join_iter n c) n.
Proof.
  intros n c Hl Hc H. apply (runs_loop_inner mcjoin_next join_iter (attrName (normalization_rule 6)) (fun _ => eq_refl) (fun _ _ => eq_refl)).
  intros m Hm. split; [apply (busy_mc _ 7 (H m Hm)); try word_neq|]. apply mcjoin_phase_selected;
    [rewrite join_iter_keeps_lassert_phase; exact Hl|rewrite join_iter_keeps_chsh_phase; exact Hc|exact (H m Hm)].
Qed.

Lemma mload_runs : forall n c,
  hw_lassert_phase c = natToWord 3 0 -> hw_chsh_phase c = natToWord 5 0 ->
  (forall m, m < n -> hw_mc_phase (mload_iter m c) = natToWord 4 2) ->
  Busy_runs c (mload_iter n c) n.
Proof.
  intros n c Hl Hc H. apply (runs_loop_inner mcload_next mload_iter (attrName (normalization_rule 4)) (fun _ => eq_refl) (fun _ _ => eq_refl)).
  intros m Hm. split; [apply (busy_mc _ 2 (H m Hm)); try word_neq|]. apply mcload_phase_selected;
    [rewrite mload_iter_keeps_lassert_phase; exact Hl|rewrite mload_iter_keeps_chsh_phase; exact Hc|exact (H m Hm)].
Qed.

Lemma nscan_runs : forall n c,
  hw_lassert_phase c = natToWord 3 0 -> hw_chsh_phase c = natToWord 5 0 ->
  (forall m, m < n -> hw_mc_phase (nscan_iter m c) = natToWord 4 8) ->
  Busy_runs c (nscan_iter n c) n.
Proof.
  intros n c Hl Hc H. apply (runs_loop_inner mcnscan_next nscan_iter (attrName (normalization_rule 8)) (fun _ => eq_refl) (fun _ _ => eq_refl)).
  intros m Hm. split; [apply (busy_mc _ 8 (H m Hm)); try word_neq|]. apply mcnscan_phase_selected;
    [rewrite nscan_iter_keeps_lassert_phase; exact Hl|rewrite nscan_iter_keeps_chsh_phase; exact Hc|exact (H m Hm)].
Qed.

Lemma lscan_runs : forall n c,
  hw_chsh_phase c = natToWord 5 0 -> hw_mc_phase c = natToWord 4 0 ->
  (forall m, m < n -> hw_lassert_phase (lscan_iter m c) = natToWord 3 2) ->
  Busy_runs c (lscan_iter n c) n.
Proof.
  intros n c Hc Hm H. apply (runs_loop_inner lscan_next lscan_iter (attrName (normalization_rule 2)) (fun _ => eq_refl) (fun _ _ => eq_refl)).
  intros m Hlt. split; [apply (busy_lassert _ 2 (H m Hlt)); try word_neq|]. apply lscan_phase_selected;
    [exact (H m Hlt)|rewrite lscan_iter_keeps_chsh_phase; exact Hc|rewrite lscan_iter_keeps_mc_phase; exact Hm].
Qed.

Lemma chsh_runs : forall n c,
  hw_lassert_phase c = natToWord 3 0 -> hw_mc_phase c = natToWord 4 0 ->
  (forall m, m < n -> hw_chsh_phase (chsh_iter m c) <> natToWord 5 0) ->
  Busy_runs c (chsh_iter n c) n.
Proof.
  intros n c Hl Hm H. apply (runs_loop_outer chsh_next chsh_iter (attrName chsh_rule) (fun _ => eq_refl) (fun _ _ => eq_refl)).
  intros m Hlt. split; [apply (busy_chsh _ (H m Hlt)); try word_neq|]. apply chsh_phase_selected;
    [exact (H m Hlt)|rewrite iter_keeps_lassert_phase; exact Hl|rewrite iter_keeps_mc_phase; exact Hm].
Qed.

(** * Normalization and commit *)

Lemma nouter_step_runs : forall c src dst i out e,
  i < e -> e <= 16 ->
  hw_mc_phase c = natToWord 4 8 -> hw_mc_i c = natToWord 5 i -> hw_mc_j c = natToWord 5 (S i) ->
  hw_mc_write_ptr c = natToWord 5 e -> hw_mc_duplicate c = false -> hw_mc_norm_ptr c = natToWord 5 out ->
  hw_coupling_pair_src_table c = src -> hw_coupling_pair_dst_table c = dst ->
  hw_lassert_phase c = natToWord 3 0 -> hw_chsh_phase c = natToWord 5 0 ->
  Busy_runs c (nouter_step c) (S (e - i)).
Proof.
  intros c src dst i out e Hi He Hp Hic Hj Hw Hd Ho Hs Ht Hl Hc.
  assert (Hn : wordToNat (hw_mc_write_ptr c) - wordToNat (hw_mc_i c) = S (e - S i)).
  { rewrite Hw, Hic, !wordToNat_natToWord_2 by (cbn; lia). lia. }
  unfold nouter_step. rewrite Hn.
  destruct (nscan_run (e - S i) c i (S i) e false src dst ltac:(lia) He ltac:(lia) Hp Hic Hj Hw Hd Hs Ht)
    as [Pm [Pf _]].
  replace (S (e - i)) with (S (e - S i) + 1) by lia.
  apply (busy_runs_trans c (nscan_iter (S (e - S i)) c)).
  - apply nscan_runs; [exact Hl|exact Hc|]. intros m Hm. apply Pm. lia.
  - eapply busy_one; [apply (busy_mc _ 9 Pf); word_neq|]. apply mcnemit_phase_selected;
      [rewrite nscan_iter_keeps_lassert_phase; exact Hl|rewrite nscan_iter_keeps_chsh_phase; exact Hc|exact Pf].
Qed.

Theorem nouter_runs : forall rem c src dst i out e,
  e - i = rem -> i < e -> e <= 16 ->
  hw_mc_phase c = natToWord 4 8 -> hw_mc_i c = natToWord 5 i -> hw_mc_j c = natToWord 5 (S i) ->
  hw_mc_write_ptr c = natToWord 5 e -> hw_mc_duplicate c = false -> hw_mc_norm_ptr c = natToWord 5 out ->
  hw_coupling_pair_src_table c = src -> hw_coupling_pair_dst_table c = dst ->
  hw_lassert_phase c = natToWord 3 0 -> hw_chsh_phase c = natToWord 5 0 ->
  exists k, Busy_runs c (nouter_iter rem c) k.
Proof.
  induction rem as [|n IH]; intros c src dst i out e Hn Hi He Hp Hic Hj Hw Hd Ho Hs Ht Hl Hc; [lia|].
  pose proof (nouter_step_runs c src dst i out e Hi He Hp Hic Hj Hw Hd Ho Hs Ht Hl Hc) as R1.
  destruct (nouter_step_facts c src dst i out e Hi He Hp Hic Hj Hw Hd Ho Hs Ht)
    as [_ [Pp [Pi [Pj [Pw [Pd [Po [Ps Pt]]]]]]]].
  cbv zeta in Pw, Po, Ps, Pt.
  cbn [nouter_iter].
  destruct (Nat.eq_dec (S i) e) as [E|E].
  - assert (n = 0) by lia. subst n. cbn [nouter_iter]. exists (S (e - i)). exact R1.
  - rewrite (proj2 (Nat.eqb_neq _ _) E) in Pp, Pw.
    destruct (IH (nouter_step c) _ _ (S i) _ e ltac:(lia) ltac:(lia) He Pp Pi Pj Pw Pd Po Ps Pt
      ltac:(rewrite nouter_step_keeps_lassert_phase; exact Hl) ltac:(rewrite nouter_step_keeps_chsh_phase; exact Hc))
      as [k Rk].
    exists (S (e - i) + k). exact (busy_runs_trans _ _ _ R1 _ _ Rk).
Qed.

Theorem norm_commit_runs : forall s P count,
  hw_mc_phase s = natToWord 4 5 ->
  hw_mc_write_base s = natToWord 5 P -> hw_mc_write_ptr s = natToWord 5 (P + count) ->
  P + count <= 16 ->
  hw_lassert_phase s = natToWord 3 0 -> hw_chsh_phase s = natToWord 5 0 ->
  exists k, Busy_runs s (norm_commit_final count s) k.
Proof.
  intros s P count Hp Hwb Hwp Hcap Hl Hc.
  set (s3 := mcnstart_next s).
  assert (S3p : hw_mc_phase s3 = natToWord 4 (if Nat.eqb count 0 then 11 else 8)).
  { unfold s3. rewrite mcnstart_phase, Hwb, Hwp, weq_nat5 by lia.
    destruct count as [|n]; [rewrite Nat.add_0_r, Nat.eqb_refl; reflexivity|].
    rewrite (proj2 (Nat.eqb_neq P (P + S n)) ltac:(lia)). reflexivity. }
  assert (S3i : hw_mc_i s3 = natToWord 5 P) by (unfold s3; rewrite mcnstart_i; exact Hwb).
  assert (S3j : hw_mc_j s3 = natToWord 5 (S P)) by (unfold s3; rewrite mcnstart_j, Hwb; apply succ_word5).
  assert (S3o : hw_mc_norm_ptr s3 = natToWord 5 P) by (unfold s3; rewrite mcnstart_norm; exact Hwb).
  assert (S3d : hw_mc_duplicate s3 = false) by (unfold s3; apply mcnstart_dup).
  assert (S3w : hw_mc_write_ptr s3 = natToWord 5 (P + count)) by (unfold s3; rewrite mcnstart_keeps_mc_write_ptr; exact Hwp).
  assert (S3l : hw_lassert_phase s3 = natToWord 3 0) by (unfold s3; rewrite mcnstart_keeps_lassert_phase; exact Hl).
  assert (S3c : hw_chsh_phase s3 = natToWord 5 0) by (unfold s3; rewrite mcnstart_keeps_chsh_phase; exact Hc).
  assert (R3 : Busy_runs s s3 1) by (eapply busy_one; [apply (busy_mc _ 5 Hp); word_neq|apply mcnstart_phase_selected; assumption]).
  set (s4 := nouter_iter count s3).
  assert (N : (exists k, Busy_runs s3 s4 k) /\ hw_mc_phase s4 = natToWord 4 11).
  { destruct count as [|n].
    - unfold s4. cbn [nouter_iter]. split; [exists 0; apply busy_done|exact S3p].
    - pose proof (normalization_prefix_established (hw_coupling_pair_src_table s3) (hw_coupling_pair_dst_table s3)
        P (P + S n) ltac:(lia)) as Inv0.
      destruct (nouter_run (S n) s3 _ _ _ _ P P P (P + S n) ltac:(lia) ltac:(lia) Inv0
        ltac:(rewrite S3p; reflexivity) S3i S3j S3w S3d S3o eq_refl eq_refl)
        as [l [src' [dst' [out' [_ [_ [Fp _]]]]]]].
      split; [|exact Fp].
      exact (nouter_runs (S n) s3 _ _ P P (P + S n) ltac:(lia) ltac:(lia) Hcap
        ltac:(rewrite S3p; reflexivity) S3i S3j S3w S3d S3o eq_refl eq_refl S3l S3c). }
  destruct N as [[k Rk] N4p].
  assert (R5 : Busy_runs s4 (mccommit_next s4) 1).
  { eapply busy_one; [apply (busy_mc _ 11 N4p); word_neq|]. apply mccommit_phase_selected; [| |exact N4p].
    - unfold s4. rewrite nouter_iter_keeps_lassert_phase. exact S3l.
    - unfold s4. rewrite nouter_iter_keeps_chsh_phase. exact S3c. }
  exists (1 + k + 1).
  change (norm_commit_final count s) with (mccommit_next s4).
  exact (busy_runs_trans _ _ _ (busy_runs_trans _ _ _ R3 _ _ Rk) _ _ R5).
Qed.

(** * COMPOSE *)

Theorem compose_copy_runs : forall c P a1 c1 a2 c2,
  hw_mc_phase c = natToWord 4 4 -> hw_mc_i c = natToWord 5 0 -> hw_mc_j c = natToWord 5 0 ->
  hw_mc_src1_count c = natToWord 5 c1 -> hw_mc_src2_count c = natToWord 5 c2 ->
  hw_mc_src1_base c = natToWord 4 a1 -> hw_mc_src2_base c = natToWord 4 a2 ->
  hw_mc_write_base c = natToWord 5 P -> hw_mc_write_ptr c = natToWord 5 P ->
  c1 <= 16 -> c2 <= 16 -> a1 + c1 <= P -> a2 + c2 <= P -> P + (c1 + c2) <= 16 ->
  hw_lassert_phase c = natToWord 3 0 -> hw_chsh_phase c = natToWord 5 0 ->
  exists k, Busy_runs c (compose_copy_final (c1 + c2) c) k.
Proof.
  intros c P a1 c1 a2 c2 Hp Hi Hj Hc1 Hc2 Ha1 Ha2 Hwb Hwp Hb1 Hb2 Hr1 Hr2 Hcap Hl Hc.
  assert (Low : forall t, low_agrees P t t) by (intros t k _; reflexivity).
  destruct (copy_run (c1 + c2) c (hw_coupling_pair_src_table c) (hw_coupling_pair_dst_table c)
    P P 0 0 c1 c2 a1 a2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hr1 Hr2
    (Low _) (Low _) Hp Hi Hj Hc1 Hc2 Ha1 Ha2 Hwp)
    as [Pm [Pp [Pw _]]].
  pose proof (copy_runs (S (c1 + c2)) c Hl Hc (fun m Hm => Pm m ltac:(lia))) as R1.
  destruct (norm_commit_runs (copy_iter (S (c1 + c2)) c) P (c1 + c2) Pp
    ltac:(rewrite copy_iter_keeps_mc_write_base; exact Hwb) Pw Hcap
    ltac:(rewrite copy_iter_keeps_lassert_phase; exact Hl) ltac:(rewrite copy_iter_keeps_chsh_phase; exact Hc))
    as [k Rk].
  exists (S (c1 + c2) + k). exact (busy_runs_trans _ _ _ R1 _ _ Rk).
Qed.

Theorem compose_join_runs : forall c P a1 c1 a2 c2,
  hw_mc_phase c = natToWord 4 7 -> hw_mc_i c = natToWord 5 0 -> hw_mc_j c = natToWord 5 0 ->
  hw_mc_src1_count c = natToWord 5 c1 -> hw_mc_src2_count c = natToWord 5 c2 ->
  hw_mc_src1_base c = natToWord 4 a1 -> hw_mc_src2_base c = natToWord 4 a2 ->
  hw_mc_write_base c = natToWord 5 P -> hw_mc_write_ptr c = natToWord 5 P ->
  c1 <= 16 -> c2 <= 16 -> a1 + c1 <= P -> a2 + c2 <= P ->
  let raw := raw_join (hw_coupling_pair_src_table c) (hw_coupling_pair_dst_table c) a1 c1 a2 c2 in
  P + List.length raw <= 16 ->
  hw_lassert_phase c = natToWord 3 0 -> hw_chsh_phase c = natToWord 5 0 ->
  exists k, Busy_runs c (compose_join_final c1 c2 (List.length raw) c) k.
Proof.
  intros c P a1 c1 a2 c2 Hp Hi Hj Hc1 Hc2 Ha1 Ha2 Hwb Hwp Hb1 Hb2 Hr1 Hr2 raw Hcap Hl Hc.
  unfold compose_join_final, join_firings_hw.
  destruct (orb (Nat.eqb c1 0) (Nat.eqb c2 0)) eqn:E.
  - assert (Hempty : raw = nil).
    { apply raw_join_empty. apply orb_true_iff in E.
      destruct E as [E|E]; apply Nat.eqb_eq in E; [left|right]; exact E. }
    assert (O : cjoin_overflow c = false)
      by (unfold cjoin_overflow, join_overflow; rewrite Hc1, Hc2, join_empty_nat, E by lia; reflexivity).
    assert (Em : cjoin_emits c = false)
      by (unfold cjoin_emits, join_emits; rewrite Hc1, Hc2, join_empty_nat, E by lia; reflexivity).
    pose proof (join_runs 1 c Hl Hc ltac:(intros m Hm; assert (m = 0) by lia; subst m; exact Hp)) as R1.
    destruct (norm_commit_runs (join_iter 1 c) P (List.length raw)
      ltac:(cbn [join_iter]; rewrite mcjoin_phase, O, Hc1, Hc2, join_empty_nat, E by lia; reflexivity)
      ltac:(cbn [join_iter]; rewrite mcjoin_keeps_mc_write_base; exact Hwb)
      ltac:(rewrite Hempty; cbn [join_iter List.length]; rewrite Nat.add_0_r, mcjoin_write_ptr, Em; exact Hwp)
      Hcap
      ltac:(rewrite join_iter_keeps_lassert_phase; exact Hl) ltac:(rewrite join_iter_keeps_chsh_phase; exact Hc))
      as [k Rk].
    exists (1 + k). exact (busy_runs_trans _ _ _ R1 _ _ Rk).
  - apply orb_false_iff in E. destruct E as [E1 E2].
    apply Nat.eqb_neq in E1. apply Nat.eqb_neq in E2.
    assert (Low : forall t, low_agrees P t t) by (intros t k _; reflexivity).
    destruct (join_run _ c _ _ P P 0 0 c1 c2 a1 a2 eq_refl ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(exact Hcap) Hr1 Hr2 (Low _) (Low _) Hp Hi Hj Hc1 Hc2 Ha1 Ha2 Hwp)
      as [Pm [Pp [Pw _]]].
    pose proof (join_runs _ c Hl Hc Pm) as R1.
    destruct (norm_commit_runs _ P (List.length raw) Pp
      ltac:(rewrite join_iter_keeps_mc_write_base; exact Hwb) Pw Hcap
      ltac:(rewrite join_iter_keeps_lassert_phase; exact Hl) ltac:(rewrite join_iter_keeps_chsh_phase; exact Hc))
      as [k Rk].
    eexists. exact (busy_runs_trans _ _ _ R1 _ _ Rk).
Qed.

Theorem compose_fsm_runs : forall s P,
  (hw_mc_phase s = natToWord 4 4 \/ hw_mc_phase s = natToWord 4 7) ->
  hw_mc_i s = natToWord 5 0 -> hw_mc_j s = natToWord 5 0 ->
  hw_mc_write_base s = natToWord 5 P -> hw_mc_write_ptr s = natToWord 5 P ->
  wordToNat (hw_mc_src1_count s) <= 16 -> wordToNat (hw_mc_src2_count s) <= 16 ->
  wordToNat (hw_mc_src1_base s) + wordToNat (hw_mc_src1_count s) <= P ->
  wordToNat (hw_mc_src2_base s) + wordToNat (hw_mc_src2_count s) <= P ->
  P + List.length (compose_raw s) <= 16 ->
  hw_lassert_phase s = natToWord 3 0 -> hw_chsh_phase s = natToWord 5 0 ->
  exists k, Busy_runs s (compose_fsm_final s) k.
Proof.
  intros s P Hph Hi Hj Hwb Hwp Hc1 Hc2 Hr1 Hr2 Hcap Hl Hc.
  unfold compose_fsm_final, compose_raw in *. cbv zeta in *.
  destruct Hph as [Hph|Hph]; rewrite Hph in *.
  - destruct (weq (natToWord 4 4) (natToWord 4 4)) as [_|NE]; [|contradiction].
    assert (Hlen : List.length (table_slice (hw_coupling_pair_src_table s) (hw_coupling_pair_dst_table s)
        (wordToNat (hw_mc_src1_base s)) (wordToNat (hw_mc_src1_count s)) ++
      table_slice (hw_coupling_pair_src_table s) (hw_coupling_pair_dst_table s)
        (wordToNat (hw_mc_src2_base s)) (wordToNat (hw_mc_src2_count s))) =
      wordToNat (hw_mc_src1_count s) + wordToNat (hw_mc_src2_count s))
      by (unfold table_slice; rewrite app_length, !map_length, !seq_length; reflexivity).
    rewrite Hlen in Hcap.
    exact (compose_copy_runs s P _ _ _ _ Hph Hi Hj (eq_sym (natToWord_wordToNat _)) (eq_sym (natToWord_wordToNat _))
      (eq_sym (natToWord_wordToNat _)) (eq_sym (natToWord_wordToNat _)) Hwb Hwp Hc1 Hc2 Hr1 Hr2 Hcap Hl Hc).
  - destruct (weq (natToWord 4 7) (natToWord 4 4)) as [E|_]; [exact (False_ind _ (phase4_ne7 E))|].
    exact (compose_join_runs s P _ _ _ _ Hph Hi Hj (eq_sym (natToWord_wordToNat _)) (eq_sym (natToWord_wordToNat _))
      (eq_sym (natToWord_wordToNat _)) (eq_sym (natToWord_wordToNat _)) Hwb Hwp Hc1 Hc2 Hr1 Hr2 Hcap Hl Hc).
Qed.

(** * MORPH *)

Theorem morph_fsm_runs : forall c0 (base : word 7) P count,
  hw_mc_phase c0 = WO~0~0~0~1 ->
  hw_mc_mem_base c0 = zext base 25 ->
  hw_coupling_pair_next_id c0 = natToWord 5 P ->
  hw_mc_write_base c0 = natToWord 5 P -> hw_mc_write_ptr c0 = natToWord 5 P ->
  hw_mem c0 (split1 7 25 (zext base 25)) = natToWord 32 count ->
  count + P <= 16 -> 2 * count + wordToNat base <= 127 ->
  hw_lassert_phase c0 = natToWord 3 0 -> hw_chsh_phase c0 = natToWord 5 0 ->
  exists k, Busy_runs c0 (morph_fsm_final count c0) k.
Proof.
  intros c0 base P count Hp Hb Hn Hwb Hwp Hm Hc Hs Hl Hch.
  set (s1 := mchdr_next c0).
  assert (Fits : mchdr_mc_fits c0 = true).
  { apply (mchdr_fits_nat c0 base P count Hb Hn ltac:(lia)); [rewrite mchdr_raw_count, Hb; exact Hm|lia|lia]. }
  assert (S1p : hw_mc_phase s1 = if Nat.eqb count 0 then WO~0~1~0~1 else WO~0~0~1~0).
  { unfold s1. rewrite mchdr_phase, Fits, mchdr_raw_count, Hb, Hm, weq_nat32_zero by lia. reflexivity. }
  assert (S1l : hw_lassert_phase s1 = natToWord 3 0) by (unfold s1; rewrite mchdr_keeps_lassert_phase; exact Hl).
  assert (S1c : hw_chsh_phase s1 = natToWord 5 0) by (unfold s1; rewrite mchdr_keeps_chsh_phase; exact Hch).
  assert (R1 : Busy_runs c0 s1 1) by (eapply busy_one; [apply (busy_mc _ 1 Hp); word_neq|apply mchdr_phase_selected; assumption]).
  set (s2 := mload_iter count s1).
  assert (L : Busy_runs s1 s2 count /\ hw_mc_phase s2 = WO~0~1~0~1 /\ hw_mc_write_ptr s2 = natToWord 5 (P + count)).
  { destruct count as [|n].
    - unfold s2. cbn [mload_iter]. split; [apply busy_done|]. unfold s1 in *. rewrite S1p. split; [reflexivity|].
      rewrite mchdr_keeps_mc_write_ptr, Hwp, Nat.add_0_r. reflexivity.
    - destruct (mload_loop (S n) s1 (hw_mc_read_ptr s1) P 0 (S n) (hw_coupling_pair_src_table s1) (hw_coupling_pair_dst_table s1)
        (hw_coupling_pair_valid_table s1) ltac:(lia) ltac:(lia) ltac:(rewrite S1p; reflexivity) eq_refl
        ltac:(unfold s1; rewrite mchdr_keeps_mc_write_ptr; exact Hwp)
        ltac:(unfold s1; apply mchdr_i)
        ltac:(unfold s1; rewrite mchdr_pair_count, mchdr_raw_count, Hb, Hm; apply split1_5_27_small; lia)
        eq_refl eq_refl eq_refl)
        as [A [B [C _]]].
      split; [exact (mload_runs (S n) s1 S1l S1c A)|]. split; [exact B|exact C]. }
  destruct L as [R2 [Lp Lw]].
  assert (S2wb : hw_mc_write_base s2 = natToWord 5 P)
    by (unfold s2, s1; rewrite mload_iter_keeps_mc_write_base, mchdr_keeps_mc_write_base; exact Hwb).
  destruct (norm_commit_runs s2 P count Lp S2wb Lw ltac:(lia)
    ltac:(unfold s2; rewrite mload_iter_keeps_lassert_phase; exact S1l)
    ltac:(unfold s2; rewrite mload_iter_keeps_chsh_phase; exact S1c)) as [k Rk].
  exists (1 + count + k).
  change (morph_fsm_final count c0) with (norm_commit_final count s2).
  exact (busy_runs_trans _ _ _ (busy_runs_trans _ _ _ R1 _ _ R2) _ _ Rk).
Qed.
