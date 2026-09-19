(** CouplingComposeRun.v: the COMPOSE coupling FSM runs at the typed boundary.

    [norm_commit_run]: from phase 5 (raw pairs written between the write base
    and the write pointer), normalization start, the normalization loop and
    the commit are an actual Kami execution; the committed slice is the
    deduplicated raw slice, pairs below the base are untouched, and the
    descriptor tables record the new descriptor. The copy loop (an identity
    side) and the join loop (neither side an identity) reach phase 5 with the
    raw pairs of [copy_run] and [join_run]. *)
Require Import Kami.Kami Kami.Semantics Kami.Lib.NatLib.
From Coq Require Import String List Arith Lia Bool.
Import ListNotations.
From KamiHW Require Import ThieleTypes ThieleCPUCore HWBoundary RuleNext RuleStep ActionEvaluator
  CoreRules CoreExecution NormalizationSteps NormalizationExecution NormalizationRetirement
  NormalizationLoop NormalizationPrefix NormalizationScanExecution NormalizationFrame MorphLoading
  MorphCopy MorphJoin RuleEnabled FsmDecoded ChshRetire CouplingFsmEnds CouplingFsmLoad
  CouplingFsmNorm CouplingFsmRun CouplingFsmCopy CouplingFsmJoin.
Local Open Scope nat_scope.
Local Open Scope list_scope.

Definition norm_commit_final (count : nat) (s : HWB) : HWB :=
  mccommit_next (nouter_iter count (mcnstart_next s)).

Theorem norm_commit_run : forall s P count,
  hw_mc_phase s = natToWord 4 5 ->
  hw_mc_write_base s = natToWord 5 P -> hw_mc_write_ptr s = natToWord 5 (P + count) ->
  P + count <= 16 ->
  let rawsrc := hw_coupling_pair_src_table s in
  let rawdst := hw_coupling_pair_dst_table s in
  exists labels out src' dst',
    Multistep thieleCore (hwb_regs s) (hwb_regs (norm_commit_final count s)) labels /\
    P <= out <= P + count /\
    table_slice src' dst' P (out - P) = nodup coupling_pair_eq_dec (table_slice rawsrc rawdst P count) /\
    (forall k, k < P -> table_pair src' dst' k = table_pair rawsrc rawdst k) /\
    hw_coupling_pair_src_table (norm_commit_final count s) = src' /\
    hw_coupling_pair_dst_table (norm_commit_final count s) = dst' /\
    hw_coupling_pair_valid_table (norm_commit_final count s) = hw_coupling_pair_valid_table s /\
    hw_coupling_pair_next_id (norm_commit_final count s) = natToWord 5 out /\
    hw_mc_phase (norm_commit_final count s) = natToWord 4 0 /\
    hw_coupling_desc_base_table (norm_commit_final count s) =
      put_vector (hw_coupling_desc_base_table s) (split1 4 1 (hw_coupling_desc_next_id s)) (split1 4 1 (natToWord 5 P)) /\
    hw_coupling_desc_count_table (norm_commit_final count s) =
      put_vector (hw_coupling_desc_count_table s) (split1 4 1 (hw_coupling_desc_next_id s))
        (wminus (natToWord 5 out) (natToWord 5 P)) /\
    hw_coupling_desc_valid_table (norm_commit_final count s) =
      put_vector (hw_coupling_desc_valid_table s) (split1 4 1 (hw_coupling_desc_next_id s)) true /\
    hw_coupling_desc_next_id (norm_commit_final count s) = wplus (hw_coupling_desc_next_id s) (natToWord 5 1) /\
    hw_err (norm_commit_final count s) = hw_err s /\
    hw_error_code (norm_commit_final count s) = hw_error_code s.
Proof.
  intros s P count Hp Hwb Hwp Hc rawsrc rawdst.
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
  assert (S3s : hw_coupling_pair_src_table s3 = rawsrc) by (unfold s3; apply mcnstart_keeps_coupling_pair_src_table).
  assert (S3t : hw_coupling_pair_dst_table s3 = rawdst) by (unfold s3; apply mcnstart_keeps_coupling_pair_dst_table).
  set (s4 := nouter_iter count s3).
  assert (N : exists src' dst' out',
    (exists l, Multistep thieleCore (hwb_regs s3) (hwb_regs s4) l) /\
    P <= out' <= P + count /\
    table_slice src' dst' P (out' - P) = nodup coupling_pair_eq_dec (table_slice rawsrc rawdst P count) /\
    (forall k, k < P -> table_pair src' dst' k = table_pair rawsrc rawdst k) /\
    hw_mc_phase s4 = natToWord 4 11 /\ hw_mc_write_ptr s4 = natToWord 5 out' /\
    hw_coupling_pair_src_table s4 = src' /\ hw_coupling_pair_dst_table s4 = dst').
  { destruct count as [|n].
    - exists rawsrc, rawdst, P. unfold s4. cbn [nouter_iter].
      split; [exists nil; constructor; reflexivity|]. split; [lia|].
      rewrite Nat.sub_diag. split; [reflexivity|]. split; [reflexivity|].
      rewrite S3p. split; [reflexivity|]. rewrite S3w, Nat.add_0_r. auto.
    - pose proof (normalization_prefix_established rawsrc rawdst P (P + S n) ltac:(lia)) as Inv0.
      destruct (nouter_run (S n) s3 rawsrc rawdst rawsrc rawdst P P P (P + S n) ltac:(lia) ltac:(lia) Inv0
        ltac:(rewrite S3p; reflexivity) S3i S3j S3w S3d S3o S3s S3t)
        as [l [src' [dst' [out' [Hrun [Inv' [Fp [Fw [Fs Ft]]]]]]]]].
      exists src', dst', out'.
      split; [exists l; exact Hrun|].
      split; [destruct Inv' as [Hbd _]; lia|].
      split; [rewrite (normalization_prefix_terminal_nodup _ _ _ _ _ _ _ Inv'); f_equal; f_equal; lia|].
      split; [intros k Hk; rewrite <- Fs, <- Ft;
              exact (nouter_prefix (S n) s3 rawsrc rawdst rawsrc rawdst P P P (P + S n) ltac:(lia) ltac:(lia) Inv0
                ltac:(rewrite S3p; reflexivity) S3i S3j S3w S3d S3o S3s S3t k Hk)|].
      split; [exact Fp|]. split; [exact Fw|]. split; [exact Fs|exact Ft]. }
  destruct N as [src' [dst' [out [Mn [Hout [Hslice [Hpre [N4p [N4w [N4s N4t]]]]]]]]]].
  assert (S4wb : hw_mc_write_base s4 = natToWord 5 P)
    by (unfold s4, s3; rewrite nouter_iter_keeps_mc_write_base, mcnstart_keeps_mc_write_base; exact Hwb).
  assert (Dn : hw_coupling_desc_next_id s4 = hw_coupling_desc_next_id s)
    by (unfold s4, s3; rewrite nouter_iter_keeps_coupling_desc_next_id, mcnstart_keeps_coupling_desc_next_id; reflexivity).
  assert (M : exists l, Multistep thieleCore (hwb_regs s) (hwb_regs (mccommit_next s4)) l).
  { apply (multi_join _ (hwb_regs s3)).
    { apply (fire_rule 7 s s3 ltac:(lia)). apply mcnstart_enabled. cbn [evalExpr evalConstT]. rewrite Hp. reflexivity. }
    apply (multi_join _ (hwb_regs s4)); [exact Mn|].
    apply (fire_rule 10 s4 (mccommit_next s4) ltac:(lia)). apply mccommit_enabled.
    cbn [evalExpr evalConstT]. rewrite N4p. reflexivity. }
  destruct M as [l Hl].
  change (norm_commit_final count s) with (mccommit_next s4).
  exists l, out, src', dst'.
  split; [exact Hl|]. split; [exact Hout|]. split; [exact Hslice|]. split; [exact Hpre|].
  rewrite mccommit_keeps_coupling_pair_src_table, mccommit_keeps_coupling_pair_dst_table, N4s, N4t.
  split; [reflexivity|]. split; [reflexivity|].
  rewrite mccommit_keeps_coupling_pair_valid_table.
  split; [unfold s4, s3; rewrite nouter_iter_keeps_coupling_pair_valid_table, mcnstart_keeps_coupling_pair_valid_table; reflexivity|].
  rewrite mccommit_pair_next, N4w. split; [reflexivity|].
  split; [apply mccommit_phase|].
  rewrite mccommit_base, mccommit_count, mccommit_valid, mccommit_desc_next, Dn, S4wb, N4w.
  unfold s4, s3.
  rewrite nouter_iter_keeps_coupling_desc_base_table, mcnstart_keeps_coupling_desc_base_table,
    nouter_iter_keeps_coupling_desc_count_table, mcnstart_keeps_coupling_desc_count_table,
    nouter_iter_keeps_coupling_desc_valid_table, mcnstart_keeps_coupling_desc_valid_table.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  rewrite mccommit_keeps_err, mccommit_keeps_error_code, nouter_iter_keeps_err, mcnstart_keeps_err,
    nouter_iter_keeps_error_code, mcnstart_keeps_error_code.
  split; reflexivity.
Qed.

(** * A loop that writes raw pairs, then normalization and commit *)

Lemma front_commit : forall c s P (raw : list coupling_pair),
  (exists l, Multistep thieleCore (hwb_regs c) (hwb_regs s) l) ->
  hw_mc_phase s = natToWord 4 5 -> hw_mc_write_base s = natToWord 5 P ->
  hw_mc_write_ptr s = natToWord 5 (P + List.length raw) -> P + List.length raw <= 16 ->
  hw_coupling_pair_src_table s = store_pairs (hw_coupling_pair_src_table c) P raw true ->
  hw_coupling_pair_dst_table s = store_pairs (hw_coupling_pair_dst_table c) P raw false ->
  hw_coupling_pair_valid_table s = loaded_valid P (List.length raw) (hw_coupling_pair_valid_table c) ->
  hw_coupling_desc_base_table s = hw_coupling_desc_base_table c ->
  hw_coupling_desc_count_table s = hw_coupling_desc_count_table c ->
  hw_coupling_desc_valid_table s = hw_coupling_desc_valid_table c ->
  hw_coupling_desc_next_id s = hw_coupling_desc_next_id c ->
  hw_err s = hw_err c -> hw_error_code s = hw_error_code c ->
  exists labels out src' dst',
    Multistep thieleCore (hwb_regs c) (hwb_regs (norm_commit_final (List.length raw) s)) labels /\
    P <= out <= P + List.length raw /\
    table_slice src' dst' P (out - P) = nodup coupling_pair_eq_dec raw /\
    (forall k, k < P -> table_pair src' dst' k =
       table_pair (hw_coupling_pair_src_table c) (hw_coupling_pair_dst_table c) k) /\
    hw_coupling_pair_src_table (norm_commit_final (List.length raw) s) = src' /\
    hw_coupling_pair_dst_table (norm_commit_final (List.length raw) s) = dst' /\
    hw_coupling_pair_valid_table (norm_commit_final (List.length raw) s) =
      loaded_valid P (List.length raw) (hw_coupling_pair_valid_table c) /\
    hw_coupling_pair_next_id (norm_commit_final (List.length raw) s) = natToWord 5 out /\
    hw_mc_phase (norm_commit_final (List.length raw) s) = natToWord 4 0 /\
    hw_coupling_desc_base_table (norm_commit_final (List.length raw) s) =
      put_vector (hw_coupling_desc_base_table c) (split1 4 1 (hw_coupling_desc_next_id c)) (split1 4 1 (natToWord 5 P)) /\
    hw_coupling_desc_count_table (norm_commit_final (List.length raw) s) =
      put_vector (hw_coupling_desc_count_table c) (split1 4 1 (hw_coupling_desc_next_id c))
        (wminus (natToWord 5 out) (natToWord 5 P)) /\
    hw_coupling_desc_valid_table (norm_commit_final (List.length raw) s) =
      put_vector (hw_coupling_desc_valid_table c) (split1 4 1 (hw_coupling_desc_next_id c)) true /\
    hw_coupling_desc_next_id (norm_commit_final (List.length raw) s) =
      wplus (hw_coupling_desc_next_id c) (natToWord 5 1) /\
    hw_err (norm_commit_final (List.length raw) s) = hw_err c /\
    hw_error_code (norm_commit_final (List.length raw) s) = hw_error_code c.
Proof.
  intros c s P raw Mf Hp Hwb Hwp Hcap Hs Hd Hv HB HC HV HN He Hec.
  destruct (norm_commit_run s P (List.length raw) Hp Hwb Hwp Hcap)
    as [l [out [src' [dst' [Ml [Hout [Hslice [Hpre R]]]]]]]].
  cbv zeta in Hslice, Hpre.
  rewrite Hs, Hd in Hslice, Hpre. rewrite store_pairs_slice in Hslice by exact Hcap.
  destruct Mf as [l0 M0].
  exists (l ++ l0), out, src', dst'.
  split; [exact (normalization_multistep_trans _ _ _ _ _ M0 Ml)|].
  split; [exact Hout|]. split; [exact Hslice|].
  split.
  { intros k Hk. rewrite Hpre by exact Hk. unfold table_pair.
    change (store_pairs (hw_coupling_pair_src_table c) P raw true (pair_index (natToWord 5 k)))
      with (pair_at (store_pairs (hw_coupling_pair_src_table c) P raw true) k).
    change (store_pairs (hw_coupling_pair_dst_table c) P raw false (pair_index (natToWord 5 k)))
      with (pair_at (store_pairs (hw_coupling_pair_dst_table c) P raw false) k).
    rewrite !store_pairs_untouched by (exact Hcap || lia). reflexivity. }
  destruct R as [Rs [Rd [Rv [Rn [Rph [RB [RC [RV [RN [Re Rec]]]]]]]]]].
  rewrite Hv in Rv. rewrite HB, HN in RB. rewrite HC, HN in RC. rewrite HV, HN in RV.
  rewrite HN in RN. rewrite He in Re. rewrite Hec in Rec.
  repeat split; assumption.
Qed.

Definition compose_copy_final (n : nat) (c : HWB) : HWB :=
  norm_commit_final n (copy_iter (S n) c).

(** The copy loop: the raw pairs are the first source slice followed by the
    second. *)
Theorem compose_copy_run : forall c P a1 c1 a2 c2,
  hw_mc_phase c = natToWord 4 4 -> hw_mc_i c = natToWord 5 0 -> hw_mc_j c = natToWord 5 0 ->
  hw_mc_src1_count c = natToWord 5 c1 -> hw_mc_src2_count c = natToWord 5 c2 ->
  hw_mc_src1_base c = natToWord 4 a1 -> hw_mc_src2_base c = natToWord 4 a2 ->
  hw_mc_write_base c = natToWord 5 P -> hw_mc_write_ptr c = natToWord 5 P ->
  c1 <= 16 -> c2 <= 16 -> a1 + c1 <= P -> a2 + c2 <= P -> P + (c1 + c2) <= 16 ->
  let raw := table_slice (hw_coupling_pair_src_table c) (hw_coupling_pair_dst_table c) a1 c1 ++
             table_slice (hw_coupling_pair_src_table c) (hw_coupling_pair_dst_table c) a2 c2 in
  exists labels out src' dst',
    Multistep thieleCore (hwb_regs c) (hwb_regs (compose_copy_final (c1 + c2) c)) labels /\
    P <= out <= P + (c1 + c2) /\
    table_slice src' dst' P (out - P) = nodup coupling_pair_eq_dec raw /\
    (forall k, k < P -> table_pair src' dst' k =
       table_pair (hw_coupling_pair_src_table c) (hw_coupling_pair_dst_table c) k) /\
    hw_coupling_pair_src_table (compose_copy_final (c1 + c2) c) = src' /\
    hw_coupling_pair_dst_table (compose_copy_final (c1 + c2) c) = dst' /\
    hw_coupling_pair_valid_table (compose_copy_final (c1 + c2) c) =
      loaded_valid P (c1 + c2) (hw_coupling_pair_valid_table c) /\
    hw_coupling_pair_next_id (compose_copy_final (c1 + c2) c) = natToWord 5 out /\
    hw_mc_phase (compose_copy_final (c1 + c2) c) = natToWord 4 0 /\
    hw_coupling_desc_base_table (compose_copy_final (c1 + c2) c) =
      put_vector (hw_coupling_desc_base_table c) (split1 4 1 (hw_coupling_desc_next_id c)) (split1 4 1 (natToWord 5 P)) /\
    hw_coupling_desc_count_table (compose_copy_final (c1 + c2) c) =
      put_vector (hw_coupling_desc_count_table c) (split1 4 1 (hw_coupling_desc_next_id c))
        (wminus (natToWord 5 out) (natToWord 5 P)) /\
    hw_coupling_desc_valid_table (compose_copy_final (c1 + c2) c) =
      put_vector (hw_coupling_desc_valid_table c) (split1 4 1 (hw_coupling_desc_next_id c)) true /\
    hw_coupling_desc_next_id (compose_copy_final (c1 + c2) c) =
      wplus (hw_coupling_desc_next_id c) (natToWord 5 1) /\
    hw_err (compose_copy_final (c1 + c2) c) = hw_err c /\
    hw_error_code (compose_copy_final (c1 + c2) c) = hw_error_code c.
Proof.
  intros c P a1 c1 a2 c2 Hp Hi Hj Hc1 Hc2 Ha1 Ha2 Hwb Hwp Hb1 Hb2 Hr1 Hr2 Hcap raw.
  assert (Low : forall t, low_agrees P t t) by (intros t k _; reflexivity).
  destruct (copy_run (c1 + c2) c (hw_coupling_pair_src_table c) (hw_coupling_pair_dst_table c)
    P P 0 0 c1 c2 a1 a2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hr1 Hr2
    (Low _) (Low _) Hp Hi Hj Hc1 Hc2 Ha1 Ha2 Hwp)
    as [Pm [Pp [Pw [Ps [Pd [Pv [Pe Pc]]]]]]].
  assert (Hraw : remaining_pairs (hw_coupling_pair_src_table c) (hw_coupling_pair_dst_table c) a1 c1 a2 c2 0 0 = raw)
    by (unfold remaining_pairs, raw; rewrite !Nat.add_0_r, !Nat.sub_0_r; reflexivity).
  rewrite Hraw in Ps, Pd.
  assert (Hlen : List.length raw = c1 + c2) by (rewrite <- Hraw, remaining_pairs_length; lia).
  unfold compose_copy_final.
  pose proof (front_commit c (copy_iter (S (c1 + c2)) c) P raw
    (copy_multistep (S (c1 + c2)) c (fun m Hm => Pm m ltac:(lia))) Pp
    ltac:(rewrite copy_iter_keeps_mc_write_base; exact Hwb)
    ltac:(rewrite Hlen; exact Pw) ltac:(rewrite Hlen; exact Hcap) Ps Pd
    ltac:(rewrite Hlen; exact Pv)
    (copy_iter_keeps_coupling_desc_base_table _ c) (copy_iter_keeps_coupling_desc_count_table _ c)
    (copy_iter_keeps_coupling_desc_valid_table _ c) (copy_iter_keeps_coupling_desc_next_id _ c)
    Pe Pc) as F.
  rewrite Hlen in F. exact F.
Qed.

Definition join_firings_hw (c1 c2 : nat) : nat :=
  if orb (Nat.eqb c1 0) (Nat.eqb c2 0) then 1 else List.length (candidate_indices 0 0 c1 c2).

Definition compose_join_final (c1 c2 k : nat) (c : HWB) : HWB :=
  norm_commit_final k (join_iter (join_firings_hw c1 c2) c).

(** The join loop: the raw pairs are the relational join of the two source
    slices, in the loop's row-major order. *)
Theorem compose_join_run : forall c P a1 c1 a2 c2,
  hw_mc_phase c = natToWord 4 7 -> hw_mc_i c = natToWord 5 0 -> hw_mc_j c = natToWord 5 0 ->
  hw_mc_src1_count c = natToWord 5 c1 -> hw_mc_src2_count c = natToWord 5 c2 ->
  hw_mc_src1_base c = natToWord 4 a1 -> hw_mc_src2_base c = natToWord 4 a2 ->
  hw_mc_write_base c = natToWord 5 P -> hw_mc_write_ptr c = natToWord 5 P ->
  c1 <= 16 -> c2 <= 16 -> a1 + c1 <= P -> a2 + c2 <= P ->
  let raw := raw_join (hw_coupling_pair_src_table c) (hw_coupling_pair_dst_table c) a1 c1 a2 c2 in
  P + List.length raw <= 16 ->
  exists labels out src' dst',
    Multistep thieleCore (hwb_regs c) (hwb_regs (compose_join_final c1 c2 (List.length raw) c)) labels /\
    P <= out <= P + List.length raw /\
    table_slice src' dst' P (out - P) = nodup coupling_pair_eq_dec raw /\
    (forall k, k < P -> table_pair src' dst' k =
       table_pair (hw_coupling_pair_src_table c) (hw_coupling_pair_dst_table c) k) /\
    hw_coupling_pair_src_table (compose_join_final c1 c2 (List.length raw) c) = src' /\
    hw_coupling_pair_dst_table (compose_join_final c1 c2 (List.length raw) c) = dst' /\
    hw_coupling_pair_valid_table (compose_join_final c1 c2 (List.length raw) c) =
      loaded_valid P (List.length raw) (hw_coupling_pair_valid_table c) /\
    hw_coupling_pair_next_id (compose_join_final c1 c2 (List.length raw) c) = natToWord 5 out /\
    hw_mc_phase (compose_join_final c1 c2 (List.length raw) c) = natToWord 4 0 /\
    hw_coupling_desc_base_table (compose_join_final c1 c2 (List.length raw) c) =
      put_vector (hw_coupling_desc_base_table c) (split1 4 1 (hw_coupling_desc_next_id c)) (split1 4 1 (natToWord 5 P)) /\
    hw_coupling_desc_count_table (compose_join_final c1 c2 (List.length raw) c) =
      put_vector (hw_coupling_desc_count_table c) (split1 4 1 (hw_coupling_desc_next_id c))
        (wminus (natToWord 5 out) (natToWord 5 P)) /\
    hw_coupling_desc_valid_table (compose_join_final c1 c2 (List.length raw) c) =
      put_vector (hw_coupling_desc_valid_table c) (split1 4 1 (hw_coupling_desc_next_id c)) true /\
    hw_coupling_desc_next_id (compose_join_final c1 c2 (List.length raw) c) =
      wplus (hw_coupling_desc_next_id c) (natToWord 5 1) /\
    hw_err (compose_join_final c1 c2 (List.length raw) c) = hw_err c /\
    hw_error_code (compose_join_final c1 c2 (List.length raw) c) = hw_error_code c.
Proof.
  intros c P a1 c1 a2 c2 Hp Hi Hj Hc1 Hc2 Ha1 Ha2 Hwb Hwp Hb1 Hb2 Hr1 Hr2 raw Hcap.
  unfold compose_join_final, join_firings_hw.
  destruct (orb (Nat.eqb c1 0) (Nat.eqb c2 0)) eqn:E.
  - assert (Hempty : raw = nil).
    { apply raw_join_empty. apply orb_true_iff in E.
      destruct E as [E|E]; apply Nat.eqb_eq in E; [left|right]; exact E. }
    assert (O : cjoin_overflow c = false)
      by (unfold cjoin_overflow, join_overflow; rewrite Hc1, Hc2, join_empty_nat, E by lia; reflexivity).
    assert (Em : cjoin_emits c = false)
      by (unfold cjoin_emits, join_emits; rewrite Hc1, Hc2, join_empty_nat, E by lia; reflexivity).
    assert (M : exists l, Multistep thieleCore (hwb_regs c) (hwb_regs (join_iter 1 c)) l).
    { apply join_multistep. intros m Hm. assert (m = 0) by lia. subst m. exact Hp. }
    pose proof (front_commit c (join_iter 1 c) P raw M
      ltac:(cbn [join_iter]; rewrite mcjoin_phase, O, Hc1, Hc2, join_empty_nat, E by lia; reflexivity)
      ltac:(cbn [join_iter]; rewrite mcjoin_keeps_mc_write_base; exact Hwb)
      ltac:(rewrite Hempty; cbn [join_iter List.length]; rewrite Nat.add_0_r, mcjoin_write_ptr, Em; exact Hwp)
      ltac:(exact Hcap)
      ltac:(rewrite Hempty; cbn [join_iter store_pairs]; rewrite mcjoin_src, Em; reflexivity)
      ltac:(rewrite Hempty; cbn [join_iter store_pairs]; rewrite mcjoin_dst, Em; reflexivity)
      ltac:(rewrite Hempty; cbn [join_iter List.length loaded_valid]; rewrite mcjoin_valid, Em; reflexivity)
      ltac:(cbn [join_iter]; apply mcjoin_keeps_coupling_desc_base_table)
      ltac:(cbn [join_iter]; apply mcjoin_keeps_coupling_desc_count_table)
      ltac:(cbn [join_iter]; apply mcjoin_keeps_coupling_desc_valid_table)
      ltac:(cbn [join_iter]; apply mcjoin_keeps_coupling_desc_next_id)
      ltac:(cbn [join_iter]; rewrite mcjoin_err, O, orb_false_r; reflexivity)
      ltac:(cbn [join_iter]; rewrite mcjoin_error_code, O; reflexivity)) as F.
    exact F.
  - apply orb_false_iff in E. destruct E as [E1 E2].
    apply Nat.eqb_neq in E1. apply Nat.eqb_neq in E2.
    assert (Low : forall t, low_agrees P t t) by (intros t k _; reflexivity).
    destruct (join_run _ c _ _ P P 0 0 c1 c2 a1 a2 eq_refl ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(exact Hcap) Hr1 Hr2 (Low _) (Low _) Hp Hi Hj Hc1 Hc2 Ha1 Ha2 Hwp)
      as [Pm [Pp [Pw [Ps [Pd [Pv [Pe Pc]]]]]]].
    exact (front_commit c _ P raw (join_multistep _ c Pm) Pp
      ltac:(rewrite join_iter_keeps_mc_write_base; exact Hwb) Pw Hcap Ps Pd Pv
      (join_iter_keeps_coupling_desc_base_table _ c) (join_iter_keeps_coupling_desc_count_table _ c)
      (join_iter_keeps_coupling_desc_valid_table _ c) (join_iter_keeps_coupling_desc_next_id _ c)
      Pe Pc).
Qed.

(** * Registers both COMPOSE runs leave unchanged *)

Lemma compose_copy_keeps_active_module : forall n c, hw_active_module (compose_copy_final n c) = hw_active_module c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_active_module, nouter_iter_keeps_active_module, mcnstart_keeps_active_module. apply copy_iter_keeps_active_module. Qed.
Lemma compose_join_keeps_active_module : forall c1 c2 k c, hw_active_module (compose_join_final c1 c2 k c) = hw_active_module c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_active_module, nouter_iter_keeps_active_module, mcnstart_keeps_active_module. apply join_iter_keeps_active_module. Qed.
Lemma compose_copy_keeps_bus_load_instr_addr : forall n c, hw_bus_load_instr_addr (compose_copy_final n c) = hw_bus_load_instr_addr c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_bus_load_instr_addr, nouter_iter_keeps_bus_load_instr_addr, mcnstart_keeps_bus_load_instr_addr. apply copy_iter_keeps_bus_load_instr_addr. Qed.
Lemma compose_join_keeps_bus_load_instr_addr : forall c1 c2 k c, hw_bus_load_instr_addr (compose_join_final c1 c2 k c) = hw_bus_load_instr_addr c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_bus_load_instr_addr, nouter_iter_keeps_bus_load_instr_addr, mcnstart_keeps_bus_load_instr_addr. apply join_iter_keeps_bus_load_instr_addr. Qed.
Lemma compose_copy_keeps_bus_load_instr_data : forall n c, hw_bus_load_instr_data (compose_copy_final n c) = hw_bus_load_instr_data c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_bus_load_instr_data, nouter_iter_keeps_bus_load_instr_data, mcnstart_keeps_bus_load_instr_data. apply copy_iter_keeps_bus_load_instr_data. Qed.
Lemma compose_join_keeps_bus_load_instr_data : forall c1 c2 k c, hw_bus_load_instr_data (compose_join_final c1 c2 k c) = hw_bus_load_instr_data c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_bus_load_instr_data, nouter_iter_keeps_bus_load_instr_data, mcnstart_keeps_bus_load_instr_data. apply join_iter_keeps_bus_load_instr_data. Qed.
Lemma compose_copy_keeps_bus_load_instr_kick : forall n c, hw_bus_load_instr_kick (compose_copy_final n c) = hw_bus_load_instr_kick c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_bus_load_instr_kick, nouter_iter_keeps_bus_load_instr_kick, mcnstart_keeps_bus_load_instr_kick. apply copy_iter_keeps_bus_load_instr_kick. Qed.
Lemma compose_join_keeps_bus_load_instr_kick : forall c1 c2 k c, hw_bus_load_instr_kick (compose_join_final c1 c2 k c) = hw_bus_load_instr_kick c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_bus_load_instr_kick, nouter_iter_keeps_bus_load_instr_kick, mcnstart_keeps_bus_load_instr_kick. apply join_iter_keeps_bus_load_instr_kick. Qed.
Lemma compose_copy_keeps_cert_addr : forall n c, hw_cert_addr (compose_copy_final n c) = hw_cert_addr c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_cert_addr, nouter_iter_keeps_cert_addr, mcnstart_keeps_cert_addr. apply copy_iter_keeps_cert_addr. Qed.
Lemma compose_join_keeps_cert_addr : forall c1 c2 k c, hw_cert_addr (compose_join_final c1 c2 k c) = hw_cert_addr c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_cert_addr, nouter_iter_keeps_cert_addr, mcnstart_keeps_cert_addr. apply join_iter_keeps_cert_addr. Qed.
Lemma compose_copy_keeps_cert_desc_base_table : forall n c, hw_cert_desc_base_table (compose_copy_final n c) = hw_cert_desc_base_table c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_cert_desc_base_table, nouter_iter_keeps_cert_desc_base_table, mcnstart_keeps_cert_desc_base_table. apply copy_iter_keeps_cert_desc_base_table. Qed.
Lemma compose_join_keeps_cert_desc_base_table : forall c1 c2 k c, hw_cert_desc_base_table (compose_join_final c1 c2 k c) = hw_cert_desc_base_table c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_cert_desc_base_table, nouter_iter_keeps_cert_desc_base_table, mcnstart_keeps_cert_desc_base_table. apply join_iter_keeps_cert_desc_base_table. Qed.
Lemma compose_copy_keeps_cert_desc_count_table : forall n c, hw_cert_desc_count_table (compose_copy_final n c) = hw_cert_desc_count_table c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_cert_desc_count_table, nouter_iter_keeps_cert_desc_count_table, mcnstart_keeps_cert_desc_count_table. apply copy_iter_keeps_cert_desc_count_table. Qed.
Lemma compose_join_keeps_cert_desc_count_table : forall c1 c2 k c, hw_cert_desc_count_table (compose_join_final c1 c2 k c) = hw_cert_desc_count_table c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_cert_desc_count_table, nouter_iter_keeps_cert_desc_count_table, mcnstart_keeps_cert_desc_count_table. apply join_iter_keeps_cert_desc_count_table. Qed.
Lemma compose_copy_keeps_cert_desc_next_id : forall n c, hw_cert_desc_next_id (compose_copy_final n c) = hw_cert_desc_next_id c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_cert_desc_next_id, nouter_iter_keeps_cert_desc_next_id, mcnstart_keeps_cert_desc_next_id. apply copy_iter_keeps_cert_desc_next_id. Qed.
Lemma compose_join_keeps_cert_desc_next_id : forall c1 c2 k c, hw_cert_desc_next_id (compose_join_final c1 c2 k c) = hw_cert_desc_next_id c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_cert_desc_next_id, nouter_iter_keeps_cert_desc_next_id, mcnstart_keeps_cert_desc_next_id. apply join_iter_keeps_cert_desc_next_id. Qed.
Lemma compose_copy_keeps_cert_desc_valid_table : forall n c, hw_cert_desc_valid_table (compose_copy_final n c) = hw_cert_desc_valid_table c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_cert_desc_valid_table, nouter_iter_keeps_cert_desc_valid_table, mcnstart_keeps_cert_desc_valid_table. apply copy_iter_keeps_cert_desc_valid_table. Qed.
Lemma compose_join_keeps_cert_desc_valid_table : forall c1 c2 k c, hw_cert_desc_valid_table (compose_join_final c1 c2 k c) = hw_cert_desc_valid_table c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_cert_desc_valid_table, nouter_iter_keeps_cert_desc_valid_table, mcnstart_keeps_cert_desc_valid_table. apply join_iter_keeps_cert_desc_valid_table. Qed.
Lemma compose_copy_keeps_certified : forall n c, hw_certified (compose_copy_final n c) = hw_certified c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_certified, nouter_iter_keeps_certified, mcnstart_keeps_certified. apply copy_iter_keeps_certified. Qed.
Lemma compose_join_keeps_certified : forall c1 c2 k c, hw_certified (compose_join_final c1 c2 k c) = hw_certified c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_certified, nouter_iter_keeps_certified, mcnstart_keeps_certified. apply join_iter_keeps_certified. Qed.
Lemma compose_copy_keeps_chsh_A_neg_a : forall n c, hw_chsh_A_neg_a (compose_copy_final n c) = hw_chsh_A_neg_a c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_chsh_A_neg_a, nouter_iter_keeps_chsh_A_neg_a, mcnstart_keeps_chsh_A_neg_a. apply copy_iter_keeps_chsh_A_neg_a. Qed.
Lemma compose_join_keeps_chsh_A_neg_a : forall c1 c2 k c, hw_chsh_A_neg_a (compose_join_final c1 c2 k c) = hw_chsh_A_neg_a c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_chsh_A_neg_a, nouter_iter_keeps_chsh_A_neg_a, mcnstart_keeps_chsh_A_neg_a. apply join_iter_keeps_chsh_A_neg_a. Qed.
Lemma compose_copy_keeps_chsh_A_neg_b : forall n c, hw_chsh_A_neg_b (compose_copy_final n c) = hw_chsh_A_neg_b c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_chsh_A_neg_b, nouter_iter_keeps_chsh_A_neg_b, mcnstart_keeps_chsh_A_neg_b. apply copy_iter_keeps_chsh_A_neg_b. Qed.
Lemma compose_join_keeps_chsh_A_neg_b : forall c1 c2 k c, hw_chsh_A_neg_b (compose_join_final c1 c2 k c) = hw_chsh_A_neg_b c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_chsh_A_neg_b, nouter_iter_keeps_chsh_A_neg_b, mcnstart_keeps_chsh_A_neg_b. apply join_iter_keeps_chsh_A_neg_b. Qed.
Lemma compose_copy_keeps_chsh_A_pos : forall n c, hw_chsh_A_pos (compose_copy_final n c) = hw_chsh_A_pos c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_chsh_A_pos, nouter_iter_keeps_chsh_A_pos, mcnstart_keeps_chsh_A_pos. apply copy_iter_keeps_chsh_A_pos. Qed.
Lemma compose_join_keeps_chsh_A_pos : forall c1 c2 k c, hw_chsh_A_pos (compose_join_final c1 c2 k c) = hw_chsh_A_pos c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_chsh_A_pos, nouter_iter_keeps_chsh_A_pos, mcnstart_keeps_chsh_A_pos. apply join_iter_keeps_chsh_A_pos. Qed.
Lemma compose_copy_keeps_chsh_A_times_B : forall n c, hw_chsh_A_times_B (compose_copy_final n c) = hw_chsh_A_times_B c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_chsh_A_times_B, nouter_iter_keeps_chsh_A_times_B, mcnstart_keeps_chsh_A_times_B. apply copy_iter_keeps_chsh_A_times_B. Qed.
Lemma compose_join_keeps_chsh_A_times_B : forall c1 c2 k c, hw_chsh_A_times_B (compose_join_final c1 c2 k c) = hw_chsh_A_times_B c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_chsh_A_times_B, nouter_iter_keeps_chsh_A_times_B, mcnstart_keeps_chsh_A_times_B. apply join_iter_keeps_chsh_A_times_B. Qed.
Lemma compose_copy_keeps_chsh_B_neg_a : forall n c, hw_chsh_B_neg_a (compose_copy_final n c) = hw_chsh_B_neg_a c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_chsh_B_neg_a, nouter_iter_keeps_chsh_B_neg_a, mcnstart_keeps_chsh_B_neg_a. apply copy_iter_keeps_chsh_B_neg_a. Qed.
Lemma compose_join_keeps_chsh_B_neg_a : forall c1 c2 k c, hw_chsh_B_neg_a (compose_join_final c1 c2 k c) = hw_chsh_B_neg_a c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_chsh_B_neg_a, nouter_iter_keeps_chsh_B_neg_a, mcnstart_keeps_chsh_B_neg_a. apply join_iter_keeps_chsh_B_neg_a. Qed.
Lemma compose_copy_keeps_chsh_B_neg_b : forall n c, hw_chsh_B_neg_b (compose_copy_final n c) = hw_chsh_B_neg_b c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_chsh_B_neg_b, nouter_iter_keeps_chsh_B_neg_b, mcnstart_keeps_chsh_B_neg_b. apply copy_iter_keeps_chsh_B_neg_b. Qed.
Lemma compose_join_keeps_chsh_B_neg_b : forall c1 c2 k c, hw_chsh_B_neg_b (compose_join_final c1 c2 k c) = hw_chsh_B_neg_b c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_chsh_B_neg_b, nouter_iter_keeps_chsh_B_neg_b, mcnstart_keeps_chsh_B_neg_b. apply join_iter_keeps_chsh_B_neg_b. Qed.
Lemma compose_copy_keeps_chsh_B_pos : forall n c, hw_chsh_B_pos (compose_copy_final n c) = hw_chsh_B_pos c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_chsh_B_pos, nouter_iter_keeps_chsh_B_pos, mcnstart_keeps_chsh_B_pos. apply copy_iter_keeps_chsh_B_pos. Qed.
Lemma compose_join_keeps_chsh_B_pos : forall c1 c2 k c, hw_chsh_B_pos (compose_join_final c1 c2 k c) = hw_chsh_B_pos c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_chsh_B_pos, nouter_iter_keeps_chsh_B_pos, mcnstart_keeps_chsh_B_pos. apply join_iter_keeps_chsh_B_pos. Qed.
Lemma compose_copy_keeps_chsh_C_sq : forall n c, hw_chsh_C_sq (compose_copy_final n c) = hw_chsh_C_sq c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_chsh_C_sq, nouter_iter_keeps_chsh_C_sq, mcnstart_keeps_chsh_C_sq. apply copy_iter_keeps_chsh_C_sq. Qed.
Lemma compose_join_keeps_chsh_C_sq : forall c1 c2 k c, hw_chsh_C_sq (compose_join_final c1 c2 k c) = hw_chsh_C_sq c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_chsh_C_sq, nouter_iter_keeps_chsh_C_sq, mcnstart_keeps_chsh_C_sq. apply join_iter_keeps_chsh_C_sq. Qed.
Lemma compose_copy_keeps_chsh_abs_C1 : forall n c, hw_chsh_abs_C1 (compose_copy_final n c) = hw_chsh_abs_C1 c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_chsh_abs_C1, nouter_iter_keeps_chsh_abs_C1, mcnstart_keeps_chsh_abs_C1. apply copy_iter_keeps_chsh_abs_C1. Qed.
Lemma compose_join_keeps_chsh_abs_C1 : forall c1 c2 k c, hw_chsh_abs_C1 (compose_join_final c1 c2 k c) = hw_chsh_abs_C1 c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_chsh_abs_C1, nouter_iter_keeps_chsh_abs_C1, mcnstart_keeps_chsh_abs_C1. apply join_iter_keeps_chsh_abs_C1. Qed.
Lemma compose_copy_keeps_chsh_abs_C2 : forall n c, hw_chsh_abs_C2 (compose_copy_final n c) = hw_chsh_abs_C2 c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_chsh_abs_C2, nouter_iter_keeps_chsh_abs_C2, mcnstart_keeps_chsh_abs_C2. apply copy_iter_keeps_chsh_abs_C2. Qed.
Lemma compose_join_keeps_chsh_abs_C2 : forall c1 c2 k c, hw_chsh_abs_C2 (compose_join_final c1 c2 k c) = hw_chsh_abs_C2 c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_chsh_abs_C2, nouter_iter_keeps_chsh_abs_C2, mcnstart_keeps_chsh_abs_C2. apply join_iter_keeps_chsh_abs_C2. Qed.
Lemma compose_copy_keeps_chsh_check_result : forall n c, hw_chsh_check_result (compose_copy_final n c) = hw_chsh_check_result c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_chsh_check_result, nouter_iter_keeps_chsh_check_result, mcnstart_keeps_chsh_check_result. apply copy_iter_keeps_chsh_check_result. Qed.
Lemma compose_join_keeps_chsh_check_result : forall c1 c2 k c, hw_chsh_check_result (compose_join_final c1 c2 k c) = hw_chsh_check_result c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_chsh_check_result, nouter_iter_keeps_chsh_check_result, mcnstart_keeps_chsh_check_result. apply join_iter_keeps_chsh_check_result. Qed.
Lemma compose_copy_keeps_chsh_d00 : forall n c, hw_chsh_d00 (compose_copy_final n c) = hw_chsh_d00 c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_chsh_d00, nouter_iter_keeps_chsh_d00, mcnstart_keeps_chsh_d00. apply copy_iter_keeps_chsh_d00. Qed.
Lemma compose_join_keeps_chsh_d00 : forall c1 c2 k c, hw_chsh_d00 (compose_join_final c1 c2 k c) = hw_chsh_d00 c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_chsh_d00, nouter_iter_keeps_chsh_d00, mcnstart_keeps_chsh_d00. apply join_iter_keeps_chsh_d00. Qed.
Lemma compose_copy_keeps_chsh_d00d01 : forall n c, hw_chsh_d00d01 (compose_copy_final n c) = hw_chsh_d00d01 c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_chsh_d00d01, nouter_iter_keeps_chsh_d00d01, mcnstart_keeps_chsh_d00d01. apply copy_iter_keeps_chsh_d00d01. Qed.
Lemma compose_join_keeps_chsh_d00d01 : forall c1 c2 k c, hw_chsh_d00d01 (compose_join_final c1 c2 k c) = hw_chsh_d00d01 c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_chsh_d00d01, nouter_iter_keeps_chsh_d00d01, mcnstart_keeps_chsh_d00d01. apply join_iter_keeps_chsh_d00d01. Qed.
Lemma compose_copy_keeps_chsh_d00sq : forall n c, hw_chsh_d00sq (compose_copy_final n c) = hw_chsh_d00sq c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_chsh_d00sq, nouter_iter_keeps_chsh_d00sq, mcnstart_keeps_chsh_d00sq. apply copy_iter_keeps_chsh_d00sq. Qed.
Lemma compose_join_keeps_chsh_d00sq : forall c1 c2 k c, hw_chsh_d00sq (compose_join_final c1 c2 k c) = hw_chsh_d00sq c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_chsh_d00sq, nouter_iter_keeps_chsh_d00sq, mcnstart_keeps_chsh_d00sq. apply join_iter_keeps_chsh_d00sq. Qed.
Lemma compose_copy_keeps_chsh_d01 : forall n c, hw_chsh_d01 (compose_copy_final n c) = hw_chsh_d01 c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_chsh_d01, nouter_iter_keeps_chsh_d01, mcnstart_keeps_chsh_d01. apply copy_iter_keeps_chsh_d01. Qed.
Lemma compose_join_keeps_chsh_d01 : forall c1 c2 k c, hw_chsh_d01 (compose_join_final c1 c2 k c) = hw_chsh_d01 c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_chsh_d01, nouter_iter_keeps_chsh_d01, mcnstart_keeps_chsh_d01. apply join_iter_keeps_chsh_d01. Qed.
Lemma compose_copy_keeps_chsh_d01sq : forall n c, hw_chsh_d01sq (compose_copy_final n c) = hw_chsh_d01sq c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_chsh_d01sq, nouter_iter_keeps_chsh_d01sq, mcnstart_keeps_chsh_d01sq. apply copy_iter_keeps_chsh_d01sq. Qed.
Lemma compose_join_keeps_chsh_d01sq : forall c1 c2 k c, hw_chsh_d01sq (compose_join_final c1 c2 k c) = hw_chsh_d01sq c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_chsh_d01sq, nouter_iter_keeps_chsh_d01sq, mcnstart_keeps_chsh_d01sq. apply join_iter_keeps_chsh_d01sq. Qed.
Lemma compose_copy_keeps_chsh_d10 : forall n c, hw_chsh_d10 (compose_copy_final n c) = hw_chsh_d10 c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_chsh_d10, nouter_iter_keeps_chsh_d10, mcnstart_keeps_chsh_d10. apply copy_iter_keeps_chsh_d10. Qed.
Lemma compose_join_keeps_chsh_d10 : forall c1 c2 k c, hw_chsh_d10 (compose_join_final c1 c2 k c) = hw_chsh_d10 c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_chsh_d10, nouter_iter_keeps_chsh_d10, mcnstart_keeps_chsh_d10. apply join_iter_keeps_chsh_d10. Qed.
Lemma compose_copy_keeps_chsh_d10d11 : forall n c, hw_chsh_d10d11 (compose_copy_final n c) = hw_chsh_d10d11 c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_chsh_d10d11, nouter_iter_keeps_chsh_d10d11, mcnstart_keeps_chsh_d10d11. apply copy_iter_keeps_chsh_d10d11. Qed.
Lemma compose_join_keeps_chsh_d10d11 : forall c1 c2 k c, hw_chsh_d10d11 (compose_join_final c1 c2 k c) = hw_chsh_d10d11 c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_chsh_d10d11, nouter_iter_keeps_chsh_d10d11, mcnstart_keeps_chsh_d10d11. apply join_iter_keeps_chsh_d10d11. Qed.
Lemma compose_copy_keeps_chsh_d10sq : forall n c, hw_chsh_d10sq (compose_copy_final n c) = hw_chsh_d10sq c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_chsh_d10sq, nouter_iter_keeps_chsh_d10sq, mcnstart_keeps_chsh_d10sq. apply copy_iter_keeps_chsh_d10sq. Qed.
Lemma compose_join_keeps_chsh_d10sq : forall c1 c2 k c, hw_chsh_d10sq (compose_join_final c1 c2 k c) = hw_chsh_d10sq c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_chsh_d10sq, nouter_iter_keeps_chsh_d10sq, mcnstart_keeps_chsh_d10sq. apply join_iter_keeps_chsh_d10sq. Qed.
Lemma compose_copy_keeps_chsh_d11 : forall n c, hw_chsh_d11 (compose_copy_final n c) = hw_chsh_d11 c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_chsh_d11, nouter_iter_keeps_chsh_d11, mcnstart_keeps_chsh_d11. apply copy_iter_keeps_chsh_d11. Qed.
Lemma compose_join_keeps_chsh_d11 : forall c1 c2 k c, hw_chsh_d11 (compose_join_final c1 c2 k c) = hw_chsh_d11 c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_chsh_d11, nouter_iter_keeps_chsh_d11, mcnstart_keeps_chsh_d11. apply join_iter_keeps_chsh_d11. Qed.
Lemma compose_copy_keeps_chsh_d11sq : forall n c, hw_chsh_d11sq (compose_copy_final n c) = hw_chsh_d11sq c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_chsh_d11sq, nouter_iter_keeps_chsh_d11sq, mcnstart_keeps_chsh_d11sq. apply copy_iter_keeps_chsh_d11sq. Qed.
Lemma compose_join_keeps_chsh_d11sq : forall c1 c2 k c, hw_chsh_d11sq (compose_join_final c1 c2 k c) = hw_chsh_d11sq c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_chsh_d11sq, nouter_iter_keeps_chsh_d11sq, mcnstart_keeps_chsh_d11sq. apply join_iter_keeps_chsh_d11sq. Qed.
Lemma compose_copy_keeps_chsh_n00 : forall n c, hw_chsh_n00 (compose_copy_final n c) = hw_chsh_n00 c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_chsh_n00, nouter_iter_keeps_chsh_n00, mcnstart_keeps_chsh_n00. apply copy_iter_keeps_chsh_n00. Qed.
Lemma compose_join_keeps_chsh_n00 : forall c1 c2 k c, hw_chsh_n00 (compose_join_final c1 c2 k c) = hw_chsh_n00 c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_chsh_n00, nouter_iter_keeps_chsh_n00, mcnstart_keeps_chsh_n00. apply join_iter_keeps_chsh_n00. Qed.
Lemma compose_copy_keeps_chsh_n00n01 : forall n c, hw_chsh_n00n01 (compose_copy_final n c) = hw_chsh_n00n01 c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_chsh_n00n01, nouter_iter_keeps_chsh_n00n01, mcnstart_keeps_chsh_n00n01. apply copy_iter_keeps_chsh_n00n01. Qed.
Lemma compose_join_keeps_chsh_n00n01 : forall c1 c2 k c, hw_chsh_n00n01 (compose_join_final c1 c2 k c) = hw_chsh_n00n01 c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_chsh_n00n01, nouter_iter_keeps_chsh_n00n01, mcnstart_keeps_chsh_n00n01. apply join_iter_keeps_chsh_n00n01. Qed.
Lemma compose_copy_keeps_chsh_n00sq : forall n c, hw_chsh_n00sq (compose_copy_final n c) = hw_chsh_n00sq c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_chsh_n00sq, nouter_iter_keeps_chsh_n00sq, mcnstart_keeps_chsh_n00sq. apply copy_iter_keeps_chsh_n00sq. Qed.
Lemma compose_join_keeps_chsh_n00sq : forall c1 c2 k c, hw_chsh_n00sq (compose_join_final c1 c2 k c) = hw_chsh_n00sq c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_chsh_n00sq, nouter_iter_keeps_chsh_n00sq, mcnstart_keeps_chsh_n00sq. apply join_iter_keeps_chsh_n00sq. Qed.
Lemma compose_copy_keeps_chsh_n01 : forall n c, hw_chsh_n01 (compose_copy_final n c) = hw_chsh_n01 c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_chsh_n01, nouter_iter_keeps_chsh_n01, mcnstart_keeps_chsh_n01. apply copy_iter_keeps_chsh_n01. Qed.
Lemma compose_join_keeps_chsh_n01 : forall c1 c2 k c, hw_chsh_n01 (compose_join_final c1 c2 k c) = hw_chsh_n01 c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_chsh_n01, nouter_iter_keeps_chsh_n01, mcnstart_keeps_chsh_n01. apply join_iter_keeps_chsh_n01. Qed.
Lemma compose_copy_keeps_chsh_n01sq : forall n c, hw_chsh_n01sq (compose_copy_final n c) = hw_chsh_n01sq c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_chsh_n01sq, nouter_iter_keeps_chsh_n01sq, mcnstart_keeps_chsh_n01sq. apply copy_iter_keeps_chsh_n01sq. Qed.
Lemma compose_join_keeps_chsh_n01sq : forall c1 c2 k c, hw_chsh_n01sq (compose_join_final c1 c2 k c) = hw_chsh_n01sq c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_chsh_n01sq, nouter_iter_keeps_chsh_n01sq, mcnstart_keeps_chsh_n01sq. apply join_iter_keeps_chsh_n01sq. Qed.
Lemma compose_copy_keeps_chsh_n10 : forall n c, hw_chsh_n10 (compose_copy_final n c) = hw_chsh_n10 c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_chsh_n10, nouter_iter_keeps_chsh_n10, mcnstart_keeps_chsh_n10. apply copy_iter_keeps_chsh_n10. Qed.
Lemma compose_join_keeps_chsh_n10 : forall c1 c2 k c, hw_chsh_n10 (compose_join_final c1 c2 k c) = hw_chsh_n10 c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_chsh_n10, nouter_iter_keeps_chsh_n10, mcnstart_keeps_chsh_n10. apply join_iter_keeps_chsh_n10. Qed.
Lemma compose_copy_keeps_chsh_n10n11 : forall n c, hw_chsh_n10n11 (compose_copy_final n c) = hw_chsh_n10n11 c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_chsh_n10n11, nouter_iter_keeps_chsh_n10n11, mcnstart_keeps_chsh_n10n11. apply copy_iter_keeps_chsh_n10n11. Qed.
Lemma compose_join_keeps_chsh_n10n11 : forall c1 c2 k c, hw_chsh_n10n11 (compose_join_final c1 c2 k c) = hw_chsh_n10n11 c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_chsh_n10n11, nouter_iter_keeps_chsh_n10n11, mcnstart_keeps_chsh_n10n11. apply join_iter_keeps_chsh_n10n11. Qed.
Lemma compose_copy_keeps_chsh_n10sq : forall n c, hw_chsh_n10sq (compose_copy_final n c) = hw_chsh_n10sq c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_chsh_n10sq, nouter_iter_keeps_chsh_n10sq, mcnstart_keeps_chsh_n10sq. apply copy_iter_keeps_chsh_n10sq. Qed.
Lemma compose_join_keeps_chsh_n10sq : forall c1 c2 k c, hw_chsh_n10sq (compose_join_final c1 c2 k c) = hw_chsh_n10sq c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_chsh_n10sq, nouter_iter_keeps_chsh_n10sq, mcnstart_keeps_chsh_n10sq. apply join_iter_keeps_chsh_n10sq. Qed.
Lemma compose_copy_keeps_chsh_n11 : forall n c, hw_chsh_n11 (compose_copy_final n c) = hw_chsh_n11 c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_chsh_n11, nouter_iter_keeps_chsh_n11, mcnstart_keeps_chsh_n11. apply copy_iter_keeps_chsh_n11. Qed.
Lemma compose_join_keeps_chsh_n11 : forall c1 c2 k c, hw_chsh_n11 (compose_join_final c1 c2 k c) = hw_chsh_n11 c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_chsh_n11, nouter_iter_keeps_chsh_n11, mcnstart_keeps_chsh_n11. apply join_iter_keeps_chsh_n11. Qed.
Lemma compose_copy_keeps_chsh_n11sq : forall n c, hw_chsh_n11sq (compose_copy_final n c) = hw_chsh_n11sq c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_chsh_n11sq, nouter_iter_keeps_chsh_n11sq, mcnstart_keeps_chsh_n11sq. apply copy_iter_keeps_chsh_n11sq. Qed.
Lemma compose_join_keeps_chsh_n11sq : forall c1 c2 k c, hw_chsh_n11sq (compose_join_final c1 c2 k c) = hw_chsh_n11sq c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_chsh_n11sq, nouter_iter_keeps_chsh_n11sq, mcnstart_keeps_chsh_n11sq. apply join_iter_keeps_chsh_n11sq. Qed.
Lemma compose_copy_keeps_chsh_phase : forall n c, hw_chsh_phase (compose_copy_final n c) = hw_chsh_phase c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_chsh_phase, nouter_iter_keeps_chsh_phase, mcnstart_keeps_chsh_phase. apply copy_iter_keeps_chsh_phase. Qed.
Lemma compose_join_keeps_chsh_phase : forall c1 c2 k c, hw_chsh_phase (compose_join_final c1 c2 k c) = hw_chsh_phase c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_chsh_phase, nouter_iter_keeps_chsh_phase, mcnstart_keeps_chsh_phase. apply join_iter_keeps_chsh_phase. Qed.
Lemma compose_copy_keeps_chsh_sign00 : forall n c, hw_chsh_sign00 (compose_copy_final n c) = hw_chsh_sign00 c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_chsh_sign00, nouter_iter_keeps_chsh_sign00, mcnstart_keeps_chsh_sign00. apply copy_iter_keeps_chsh_sign00. Qed.
Lemma compose_join_keeps_chsh_sign00 : forall c1 c2 k c, hw_chsh_sign00 (compose_join_final c1 c2 k c) = hw_chsh_sign00 c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_chsh_sign00, nouter_iter_keeps_chsh_sign00, mcnstart_keeps_chsh_sign00. apply join_iter_keeps_chsh_sign00. Qed.
Lemma compose_copy_keeps_chsh_sign01 : forall n c, hw_chsh_sign01 (compose_copy_final n c) = hw_chsh_sign01 c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_chsh_sign01, nouter_iter_keeps_chsh_sign01, mcnstart_keeps_chsh_sign01. apply copy_iter_keeps_chsh_sign01. Qed.
Lemma compose_join_keeps_chsh_sign01 : forall c1 c2 k c, hw_chsh_sign01 (compose_join_final c1 c2 k c) = hw_chsh_sign01 c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_chsh_sign01, nouter_iter_keeps_chsh_sign01, mcnstart_keeps_chsh_sign01. apply join_iter_keeps_chsh_sign01. Qed.
Lemma compose_copy_keeps_chsh_sign10 : forall n c, hw_chsh_sign10 (compose_copy_final n c) = hw_chsh_sign10 c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_chsh_sign10, nouter_iter_keeps_chsh_sign10, mcnstart_keeps_chsh_sign10. apply copy_iter_keeps_chsh_sign10. Qed.
Lemma compose_join_keeps_chsh_sign10 : forall c1 c2 k c, hw_chsh_sign10 (compose_join_final c1 c2 k c) = hw_chsh_sign10 c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_chsh_sign10, nouter_iter_keeps_chsh_sign10, mcnstart_keeps_chsh_sign10. apply join_iter_keeps_chsh_sign10. Qed.
Lemma compose_copy_keeps_chsh_sign11 : forall n c, hw_chsh_sign11 (compose_copy_final n c) = hw_chsh_sign11 c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_chsh_sign11, nouter_iter_keeps_chsh_sign11, mcnstart_keeps_chsh_sign11. apply copy_iter_keeps_chsh_sign11. Qed.
Lemma compose_join_keeps_chsh_sign11 : forall c1 c2 k c, hw_chsh_sign11 (compose_join_final c1 c2 k c) = hw_chsh_sign11 c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_chsh_sign11, nouter_iter_keeps_chsh_sign11, mcnstart_keeps_chsh_sign11. apply join_iter_keeps_chsh_sign11. Qed.
Lemma compose_copy_keeps_coupling_desc_label_len_table : forall n c, hw_coupling_desc_label_len_table (compose_copy_final n c) = hw_coupling_desc_label_len_table c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_coupling_desc_label_len_table, nouter_iter_keeps_coupling_desc_label_len_table, mcnstart_keeps_coupling_desc_label_len_table. apply copy_iter_keeps_coupling_desc_label_len_table. Qed.
Lemma compose_join_keeps_coupling_desc_label_len_table : forall c1 c2 k c, hw_coupling_desc_label_len_table (compose_join_final c1 c2 k c) = hw_coupling_desc_label_len_table c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_coupling_desc_label_len_table, nouter_iter_keeps_coupling_desc_label_len_table, mcnstart_keeps_coupling_desc_label_len_table. apply join_iter_keeps_coupling_desc_label_len_table. Qed.
Lemma compose_copy_keeps_coupling_desc_label_table : forall n c, hw_coupling_desc_label_table (compose_copy_final n c) = hw_coupling_desc_label_table c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_coupling_desc_label_table, nouter_iter_keeps_coupling_desc_label_table, mcnstart_keeps_coupling_desc_label_table. apply copy_iter_keeps_coupling_desc_label_table. Qed.
Lemma compose_join_keeps_coupling_desc_label_table : forall c1 c2 k c, hw_coupling_desc_label_table (compose_join_final c1 c2 k c) = hw_coupling_desc_label_table c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_coupling_desc_label_table, nouter_iter_keeps_coupling_desc_label_table, mcnstart_keeps_coupling_desc_label_table. apply join_iter_keeps_coupling_desc_label_table. Qed.
Lemma compose_copy_keeps_csr_heap_base : forall n c, hw_csr_heap_base (compose_copy_final n c) = hw_csr_heap_base c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_csr_heap_base, nouter_iter_keeps_csr_heap_base, mcnstart_keeps_csr_heap_base. apply copy_iter_keeps_csr_heap_base. Qed.
Lemma compose_join_keeps_csr_heap_base : forall c1 c2 k c, hw_csr_heap_base (compose_join_final c1 c2 k c) = hw_csr_heap_base c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_csr_heap_base, nouter_iter_keeps_csr_heap_base, mcnstart_keeps_csr_heap_base. apply join_iter_keeps_csr_heap_base. Qed.
Lemma compose_copy_keeps_csr_status : forall n c, hw_csr_status (compose_copy_final n c) = hw_csr_status c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_csr_status, nouter_iter_keeps_csr_status, mcnstart_keeps_csr_status. apply copy_iter_keeps_csr_status. Qed.
Lemma compose_join_keeps_csr_status : forall c1 c2 k c, hw_csr_status (compose_join_final c1 c2 k c) = hw_csr_status c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_csr_status, nouter_iter_keeps_csr_status, mcnstart_keeps_csr_status. apply join_iter_keeps_csr_status. Qed.
Lemma compose_copy_keeps_desc_meta_aux_table : forall n c, hw_desc_meta_aux_table (compose_copy_final n c) = hw_desc_meta_aux_table c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_desc_meta_aux_table, nouter_iter_keeps_desc_meta_aux_table, mcnstart_keeps_desc_meta_aux_table. apply copy_iter_keeps_desc_meta_aux_table. Qed.
Lemma compose_join_keeps_desc_meta_aux_table : forall c1 c2 k c, hw_desc_meta_aux_table (compose_join_final c1 c2 k c) = hw_desc_meta_aux_table c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_desc_meta_aux_table, nouter_iter_keeps_desc_meta_aux_table, mcnstart_keeps_desc_meta_aux_table. apply join_iter_keeps_desc_meta_aux_table. Qed.
Lemma compose_copy_keeps_desc_meta_inline_len_table : forall n c, hw_desc_meta_inline_len_table (compose_copy_final n c) = hw_desc_meta_inline_len_table c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_desc_meta_inline_len_table, nouter_iter_keeps_desc_meta_inline_len_table, mcnstart_keeps_desc_meta_inline_len_table. apply copy_iter_keeps_desc_meta_inline_len_table. Qed.
Lemma compose_join_keeps_desc_meta_inline_len_table : forall c1 c2 k c, hw_desc_meta_inline_len_table (compose_join_final c1 c2 k c) = hw_desc_meta_inline_len_table c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_desc_meta_inline_len_table, nouter_iter_keeps_desc_meta_inline_len_table, mcnstart_keeps_desc_meta_inline_len_table. apply join_iter_keeps_desc_meta_inline_len_table. Qed.
Lemma compose_copy_keeps_desc_meta_kind_table : forall n c, hw_desc_meta_kind_table (compose_copy_final n c) = hw_desc_meta_kind_table c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_desc_meta_kind_table, nouter_iter_keeps_desc_meta_kind_table, mcnstart_keeps_desc_meta_kind_table. apply copy_iter_keeps_desc_meta_kind_table. Qed.
Lemma compose_join_keeps_desc_meta_kind_table : forall c1 c2 k c, hw_desc_meta_kind_table (compose_join_final c1 c2 k c) = hw_desc_meta_kind_table c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_desc_meta_kind_table, nouter_iter_keeps_desc_meta_kind_table, mcnstart_keeps_desc_meta_kind_table. apply join_iter_keeps_desc_meta_kind_table. Qed.
Lemma compose_copy_keeps_desc_meta_next_id : forall n c, hw_desc_meta_next_id (compose_copy_final n c) = hw_desc_meta_next_id c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_desc_meta_next_id, nouter_iter_keeps_desc_meta_next_id, mcnstart_keeps_desc_meta_next_id. apply copy_iter_keeps_desc_meta_next_id. Qed.
Lemma compose_join_keeps_desc_meta_next_id : forall c1 c2 k c, hw_desc_meta_next_id (compose_join_final c1 c2 k c) = hw_desc_meta_next_id c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_desc_meta_next_id, nouter_iter_keeps_desc_meta_next_id, mcnstart_keeps_desc_meta_next_id. apply join_iter_keeps_desc_meta_next_id. Qed.
Lemma compose_copy_keeps_desc_meta_subtype_table : forall n c, hw_desc_meta_subtype_table (compose_copy_final n c) = hw_desc_meta_subtype_table c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_desc_meta_subtype_table, nouter_iter_keeps_desc_meta_subtype_table, mcnstart_keeps_desc_meta_subtype_table. apply copy_iter_keeps_desc_meta_subtype_table. Qed.
Lemma compose_join_keeps_desc_meta_subtype_table : forall c1 c2 k c, hw_desc_meta_subtype_table (compose_join_final c1 c2 k c) = hw_desc_meta_subtype_table c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_desc_meta_subtype_table, nouter_iter_keeps_desc_meta_subtype_table, mcnstart_keeps_desc_meta_subtype_table. apply join_iter_keeps_desc_meta_subtype_table. Qed.
Lemma compose_copy_keeps_desc_meta_valid_table : forall n c, hw_desc_meta_valid_table (compose_copy_final n c) = hw_desc_meta_valid_table c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_desc_meta_valid_table, nouter_iter_keeps_desc_meta_valid_table, mcnstart_keeps_desc_meta_valid_table. apply copy_iter_keeps_desc_meta_valid_table. Qed.
Lemma compose_join_keeps_desc_meta_valid_table : forall c1 c2 k c, hw_desc_meta_valid_table (compose_join_final c1 c2 k c) = hw_desc_meta_valid_table c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_desc_meta_valid_table, nouter_iter_keeps_desc_meta_valid_table, mcnstart_keeps_desc_meta_valid_table. apply join_iter_keeps_desc_meta_valid_table. Qed.
Lemma compose_copy_keeps_formula_desc_base_table : forall n c, hw_formula_desc_base_table (compose_copy_final n c) = hw_formula_desc_base_table c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_formula_desc_base_table, nouter_iter_keeps_formula_desc_base_table, mcnstart_keeps_formula_desc_base_table. apply copy_iter_keeps_formula_desc_base_table. Qed.
Lemma compose_join_keeps_formula_desc_base_table : forall c1 c2 k c, hw_formula_desc_base_table (compose_join_final c1 c2 k c) = hw_formula_desc_base_table c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_formula_desc_base_table, nouter_iter_keeps_formula_desc_base_table, mcnstart_keeps_formula_desc_base_table. apply join_iter_keeps_formula_desc_base_table. Qed.
Lemma compose_copy_keeps_formula_desc_count_table : forall n c, hw_formula_desc_count_table (compose_copy_final n c) = hw_formula_desc_count_table c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_formula_desc_count_table, nouter_iter_keeps_formula_desc_count_table, mcnstart_keeps_formula_desc_count_table. apply copy_iter_keeps_formula_desc_count_table. Qed.
Lemma compose_join_keeps_formula_desc_count_table : forall c1 c2 k c, hw_formula_desc_count_table (compose_join_final c1 c2 k c) = hw_formula_desc_count_table c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_formula_desc_count_table, nouter_iter_keeps_formula_desc_count_table, mcnstart_keeps_formula_desc_count_table. apply join_iter_keeps_formula_desc_count_table. Qed.
Lemma compose_copy_keeps_formula_desc_next_id : forall n c, hw_formula_desc_next_id (compose_copy_final n c) = hw_formula_desc_next_id c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_formula_desc_next_id, nouter_iter_keeps_formula_desc_next_id, mcnstart_keeps_formula_desc_next_id. apply copy_iter_keeps_formula_desc_next_id. Qed.
Lemma compose_join_keeps_formula_desc_next_id : forall c1 c2 k c, hw_formula_desc_next_id (compose_join_final c1 c2 k c) = hw_formula_desc_next_id c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_formula_desc_next_id, nouter_iter_keeps_formula_desc_next_id, mcnstart_keeps_formula_desc_next_id. apply join_iter_keeps_formula_desc_next_id. Qed.
Lemma compose_copy_keeps_formula_desc_valid_table : forall n c, hw_formula_desc_valid_table (compose_copy_final n c) = hw_formula_desc_valid_table c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_formula_desc_valid_table, nouter_iter_keeps_formula_desc_valid_table, mcnstart_keeps_formula_desc_valid_table. apply copy_iter_keeps_formula_desc_valid_table. Qed.
Lemma compose_join_keeps_formula_desc_valid_table : forall c1 c2 k c, hw_formula_desc_valid_table (compose_join_final c1 c2 k c) = hw_formula_desc_valid_table c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_formula_desc_valid_table, nouter_iter_keeps_formula_desc_valid_table, mcnstart_keeps_formula_desc_valid_table. apply join_iter_keeps_formula_desc_valid_table. Qed.
Lemma compose_copy_keeps_halted : forall n c, hw_halted (compose_copy_final n c) = hw_halted c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_halted, nouter_iter_keeps_halted, mcnstart_keeps_halted. apply copy_iter_keeps_halted. Qed.
Lemma compose_join_keeps_halted : forall c1 c2 k c, hw_halted (compose_join_final c1 c2 k c) = hw_halted c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_halted, nouter_iter_keeps_halted, mcnstart_keeps_halted. apply join_iter_keeps_halted. Qed.
Lemma compose_copy_keeps_imem : forall n c, hw_imem (compose_copy_final n c) = hw_imem c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_imem, nouter_iter_keeps_imem, mcnstart_keeps_imem. apply copy_iter_keeps_imem. Qed.
Lemma compose_join_keeps_imem : forall c1 c2 k c, hw_imem (compose_join_final c1 c2 k c) = hw_imem c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_imem, nouter_iter_keeps_imem, mcnstart_keeps_imem. apply join_iter_keeps_imem. Qed.
Lemma compose_copy_keeps_info_gain : forall n c, hw_info_gain (compose_copy_final n c) = hw_info_gain c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_info_gain, nouter_iter_keeps_info_gain, mcnstart_keeps_info_gain. apply copy_iter_keeps_info_gain. Qed.
Lemma compose_join_keeps_info_gain : forall c1 c2 k c, hw_info_gain (compose_join_final c1 c2 k c) = hw_info_gain c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_info_gain, nouter_iter_keeps_info_gain, mcnstart_keeps_info_gain. apply join_iter_keeps_info_gain. Qed.
Lemma compose_copy_keeps_lassert_cbase : forall n c, hw_lassert_cbase (compose_copy_final n c) = hw_lassert_cbase c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_lassert_cbase, nouter_iter_keeps_lassert_cbase, mcnstart_keeps_lassert_cbase. apply copy_iter_keeps_lassert_cbase. Qed.
Lemma compose_join_keeps_lassert_cbase : forall c1 c2 k c, hw_lassert_cbase (compose_join_final c1 c2 k c) = hw_lassert_cbase c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_lassert_cbase, nouter_iter_keeps_lassert_cbase, mcnstart_keeps_lassert_cbase. apply join_iter_keeps_lassert_cbase. Qed.
Lemma compose_copy_keeps_lassert_cbuf : forall n c, hw_lassert_cbuf (compose_copy_final n c) = hw_lassert_cbuf c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_lassert_cbuf, nouter_iter_keeps_lassert_cbuf, mcnstart_keeps_lassert_cbuf. apply copy_iter_keeps_lassert_cbuf. Qed.
Lemma compose_join_keeps_lassert_cbuf : forall c1 c2 k c, hw_lassert_cbuf (compose_join_final c1 c2 k c) = hw_lassert_cbuf c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_lassert_cbuf, nouter_iter_keeps_lassert_cbuf, mcnstart_keeps_lassert_cbuf. apply join_iter_keeps_lassert_cbuf. Qed.
Lemma compose_copy_keeps_lassert_clause_sat : forall n c, hw_lassert_clause_sat (compose_copy_final n c) = hw_lassert_clause_sat c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_lassert_clause_sat, nouter_iter_keeps_lassert_clause_sat, mcnstart_keeps_lassert_clause_sat. apply copy_iter_keeps_lassert_clause_sat. Qed.
Lemma compose_join_keeps_lassert_clause_sat : forall c1 c2 k c, hw_lassert_clause_sat (compose_join_final c1 c2 k c) = hw_lassert_clause_sat c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_lassert_clause_sat, nouter_iter_keeps_lassert_clause_sat, mcnstart_keeps_lassert_clause_sat. apply join_iter_keeps_lassert_clause_sat. Qed.
Lemma compose_copy_keeps_lassert_clen : forall n c, hw_lassert_clen (compose_copy_final n c) = hw_lassert_clen c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_lassert_clen, nouter_iter_keeps_lassert_clen, mcnstart_keeps_lassert_clen. apply copy_iter_keeps_lassert_clen. Qed.
Lemma compose_join_keeps_lassert_clen : forall c1 c2 k c, hw_lassert_clen (compose_join_final c1 c2 k c) = hw_lassert_clen c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_lassert_clen, nouter_iter_keeps_lassert_clen, mcnstart_keeps_lassert_clen. apply join_iter_keeps_lassert_clen. Qed.
Lemma compose_copy_keeps_lassert_counter_clause_sat : forall n c, hw_lassert_counter_clause_sat (compose_copy_final n c) = hw_lassert_counter_clause_sat c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_lassert_counter_clause_sat, nouter_iter_keeps_lassert_counter_clause_sat, mcnstart_keeps_lassert_counter_clause_sat. apply copy_iter_keeps_lassert_counter_clause_sat. Qed.
Lemma compose_join_keeps_lassert_counter_clause_sat : forall c1 c2 k c, hw_lassert_counter_clause_sat (compose_join_final c1 c2 k c) = hw_lassert_counter_clause_sat c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_lassert_counter_clause_sat, nouter_iter_keeps_lassert_counter_clause_sat, mcnstart_keeps_lassert_counter_clause_sat. apply join_iter_keeps_lassert_counter_clause_sat. Qed.
Lemma compose_copy_keeps_lassert_counter_seen_fail : forall n c, hw_lassert_counter_seen_fail (compose_copy_final n c) = hw_lassert_counter_seen_fail c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_lassert_counter_seen_fail, nouter_iter_keeps_lassert_counter_seen_fail, mcnstart_keeps_lassert_counter_seen_fail. apply copy_iter_keeps_lassert_counter_seen_fail. Qed.
Lemma compose_join_keeps_lassert_counter_seen_fail : forall c1 c2 k c, hw_lassert_counter_seen_fail (compose_join_final c1 c2 k c) = hw_lassert_counter_seen_fail c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_lassert_counter_seen_fail, nouter_iter_keeps_lassert_counter_seen_fail, mcnstart_keeps_lassert_counter_seen_fail. apply join_iter_keeps_lassert_counter_seen_fail. Qed.
Lemma compose_copy_keeps_lassert_cptr : forall n c, hw_lassert_cptr (compose_copy_final n c) = hw_lassert_cptr c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_lassert_cptr, nouter_iter_keeps_lassert_cptr, mcnstart_keeps_lassert_cptr. apply copy_iter_keeps_lassert_cptr. Qed.
Lemma compose_join_keeps_lassert_cptr : forall c1 c2 k c, hw_lassert_cptr (compose_join_final c1 c2 k c) = hw_lassert_cptr c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_lassert_cptr, nouter_iter_keeps_lassert_cptr, mcnstart_keeps_lassert_cptr. apply join_iter_keeps_lassert_cptr. Qed.
Lemma compose_copy_keeps_lassert_fbase : forall n c, hw_lassert_fbase (compose_copy_final n c) = hw_lassert_fbase c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_lassert_fbase, nouter_iter_keeps_lassert_fbase, mcnstart_keeps_lassert_fbase. apply copy_iter_keeps_lassert_fbase. Qed.
Lemma compose_join_keeps_lassert_fbase : forall c1 c2 k c, hw_lassert_fbase (compose_join_final c1 c2 k c) = hw_lassert_fbase c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_lassert_fbase, nouter_iter_keeps_lassert_fbase, mcnstart_keeps_lassert_fbase. apply join_iter_keeps_lassert_fbase. Qed.
Lemma compose_copy_keeps_lassert_fbuf : forall n c, hw_lassert_fbuf (compose_copy_final n c) = hw_lassert_fbuf c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_lassert_fbuf, nouter_iter_keeps_lassert_fbuf, mcnstart_keeps_lassert_fbuf. apply copy_iter_keeps_lassert_fbuf. Qed.
Lemma compose_join_keeps_lassert_fbuf : forall c1 c2 k c, hw_lassert_fbuf (compose_join_final c1 c2 k c) = hw_lassert_fbuf c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_lassert_fbuf, nouter_iter_keeps_lassert_fbuf, mcnstart_keeps_lassert_fbuf. apply join_iter_keeps_lassert_fbuf. Qed.
Lemma compose_copy_keeps_lassert_flen : forall n c, hw_lassert_flen (compose_copy_final n c) = hw_lassert_flen c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_lassert_flen, nouter_iter_keeps_lassert_flen, mcnstart_keeps_lassert_flen. apply copy_iter_keeps_lassert_flen. Qed.
Lemma compose_join_keeps_lassert_flen : forall c1 c2 k c, hw_lassert_flen (compose_join_final c1 c2 k c) = hw_lassert_flen c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_lassert_flen, nouter_iter_keeps_lassert_flen, mcnstart_keeps_lassert_flen. apply join_iter_keeps_lassert_flen. Qed.
Lemma compose_copy_keeps_lassert_fptr : forall n c, hw_lassert_fptr (compose_copy_final n c) = hw_lassert_fptr c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_lassert_fptr, nouter_iter_keeps_lassert_fptr, mcnstart_keeps_lassert_fptr. apply copy_iter_keeps_lassert_fptr. Qed.
Lemma compose_join_keeps_lassert_fptr : forall c1 c2 k c, hw_lassert_fptr (compose_join_final c1 c2 k c) = hw_lassert_fptr c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_lassert_fptr, nouter_iter_keeps_lassert_fptr, mcnstart_keeps_lassert_fptr. apply join_iter_keeps_lassert_fptr. Qed.
Lemma compose_copy_keeps_lassert_kind : forall n c, hw_lassert_kind (compose_copy_final n c) = hw_lassert_kind c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_lassert_kind, nouter_iter_keeps_lassert_kind, mcnstart_keeps_lassert_kind. apply copy_iter_keeps_lassert_kind. Qed.
Lemma compose_join_keeps_lassert_kind : forall c1 c2 k c, hw_lassert_kind (compose_join_final c1 c2 k c) = hw_lassert_kind c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_lassert_kind, nouter_iter_keeps_lassert_kind, mcnstart_keeps_lassert_kind. apply join_iter_keeps_lassert_kind. Qed.
Lemma compose_copy_keeps_lassert_nvars : forall n c, hw_lassert_nvars (compose_copy_final n c) = hw_lassert_nvars c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_lassert_nvars, nouter_iter_keeps_lassert_nvars, mcnstart_keeps_lassert_nvars. apply copy_iter_keeps_lassert_nvars. Qed.
Lemma compose_join_keeps_lassert_nvars : forall c1 c2 k c, hw_lassert_nvars (compose_join_final c1 c2 k c) = hw_lassert_nvars c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_lassert_nvars, nouter_iter_keeps_lassert_nvars, mcnstart_keeps_lassert_nvars. apply join_iter_keeps_lassert_nvars. Qed.
Lemma compose_copy_keeps_lassert_phase : forall n c, hw_lassert_phase (compose_copy_final n c) = hw_lassert_phase c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_lassert_phase, nouter_iter_keeps_lassert_phase, mcnstart_keeps_lassert_phase. apply copy_iter_keeps_lassert_phase. Qed.
Lemma compose_join_keeps_lassert_phase : forall c1 c2 k c, hw_lassert_phase (compose_join_final c1 c2 k c) = hw_lassert_phase c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_lassert_phase, nouter_iter_keeps_lassert_phase, mcnstart_keeps_lassert_phase. apply join_iter_keeps_lassert_phase. Qed.
Lemma compose_copy_keeps_logic_acc : forall n c, hw_logic_acc (compose_copy_final n c) = hw_logic_acc c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_logic_acc, nouter_iter_keeps_logic_acc, mcnstart_keeps_logic_acc. apply copy_iter_keeps_logic_acc. Qed.
Lemma compose_join_keeps_logic_acc : forall c1 c2 k c, hw_logic_acc (compose_join_final c1 c2 k c) = hw_logic_acc c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_logic_acc, nouter_iter_keeps_logic_acc, mcnstart_keeps_logic_acc. apply join_iter_keeps_logic_acc. Qed.
Lemma compose_copy_keeps_mc_cost : forall n c, hw_mc_cost (compose_copy_final n c) = hw_mc_cost c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_mc_cost, nouter_iter_keeps_mc_cost, mcnstart_keeps_mc_cost. apply copy_iter_keeps_mc_cost. Qed.
Lemma compose_join_keeps_mc_cost : forall c1 c2 k c, hw_mc_cost (compose_join_final c1 c2 k c) = hw_mc_cost c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_mc_cost, nouter_iter_keeps_mc_cost, mcnstart_keeps_mc_cost. apply join_iter_keeps_mc_cost. Qed.
Lemma compose_copy_keeps_mc_dst_reg : forall n c, hw_mc_dst_reg (compose_copy_final n c) = hw_mc_dst_reg c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_mc_dst_reg, nouter_iter_keeps_mc_dst_reg, mcnstart_keeps_mc_dst_reg. apply copy_iter_keeps_mc_dst_reg. Qed.
Lemma compose_join_keeps_mc_dst_reg : forall c1 c2 k c, hw_mc_dst_reg (compose_join_final c1 c2 k c) = hw_mc_dst_reg c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_mc_dst_reg, nouter_iter_keeps_mc_dst_reg, mcnstart_keeps_mc_dst_reg. apply join_iter_keeps_mc_dst_reg. Qed.
Lemma compose_copy_keeps_mc_is_id1 : forall n c, hw_mc_is_id1 (compose_copy_final n c) = hw_mc_is_id1 c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_mc_is_id1, nouter_iter_keeps_mc_is_id1, mcnstart_keeps_mc_is_id1. apply copy_iter_keeps_mc_is_id1. Qed.
Lemma compose_join_keeps_mc_is_id1 : forall c1 c2 k c, hw_mc_is_id1 (compose_join_final c1 c2 k c) = hw_mc_is_id1 c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_mc_is_id1, nouter_iter_keeps_mc_is_id1, mcnstart_keeps_mc_is_id1. apply join_iter_keeps_mc_is_id1. Qed.
Lemma compose_copy_keeps_mc_is_id2 : forall n c, hw_mc_is_id2 (compose_copy_final n c) = hw_mc_is_id2 c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_mc_is_id2, nouter_iter_keeps_mc_is_id2, mcnstart_keeps_mc_is_id2. apply copy_iter_keeps_mc_is_id2. Qed.
Lemma compose_join_keeps_mc_is_id2 : forall c1 c2 k c, hw_mc_is_id2 (compose_join_final c1 c2 k c) = hw_mc_is_id2 c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_mc_is_id2, nouter_iter_keeps_mc_is_id2, mcnstart_keeps_mc_is_id2. apply join_iter_keeps_mc_is_id2. Qed.
Lemma compose_copy_keeps_mc_mem_base : forall n c, hw_mc_mem_base (compose_copy_final n c) = hw_mc_mem_base c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_mc_mem_base, nouter_iter_keeps_mc_mem_base, mcnstart_keeps_mc_mem_base. apply copy_iter_keeps_mc_mem_base. Qed.
Lemma compose_join_keeps_mc_mem_base : forall c1 c2 k c, hw_mc_mem_base (compose_join_final c1 c2 k c) = hw_mc_mem_base c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_mc_mem_base, nouter_iter_keeps_mc_mem_base, mcnstart_keeps_mc_mem_base. apply join_iter_keeps_mc_mem_base. Qed.
Lemma compose_copy_keeps_mc_morph_slot : forall n c, hw_mc_morph_slot (compose_copy_final n c) = hw_mc_morph_slot c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_mc_morph_slot, nouter_iter_keeps_mc_morph_slot, mcnstart_keeps_mc_morph_slot. apply copy_iter_keeps_mc_morph_slot. Qed.
Lemma compose_join_keeps_mc_morph_slot : forall c1 c2 k c, hw_mc_morph_slot (compose_join_final c1 c2 k c) = hw_mc_morph_slot c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_mc_morph_slot, nouter_iter_keeps_mc_morph_slot, mcnstart_keeps_mc_morph_slot. apply join_iter_keeps_mc_morph_slot. Qed.
Lemma compose_copy_keeps_mc_new_dst_mod : forall n c, hw_mc_new_dst_mod (compose_copy_final n c) = hw_mc_new_dst_mod c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_mc_new_dst_mod, nouter_iter_keeps_mc_new_dst_mod, mcnstart_keeps_mc_new_dst_mod. apply copy_iter_keeps_mc_new_dst_mod. Qed.
Lemma compose_join_keeps_mc_new_dst_mod : forall c1 c2 k c, hw_mc_new_dst_mod (compose_join_final c1 c2 k c) = hw_mc_new_dst_mod c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_mc_new_dst_mod, nouter_iter_keeps_mc_new_dst_mod, mcnstart_keeps_mc_new_dst_mod. apply join_iter_keeps_mc_new_dst_mod. Qed.
Lemma compose_copy_keeps_mc_new_src_mod : forall n c, hw_mc_new_src_mod (compose_copy_final n c) = hw_mc_new_src_mod c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_mc_new_src_mod, nouter_iter_keeps_mc_new_src_mod, mcnstart_keeps_mc_new_src_mod. apply copy_iter_keeps_mc_new_src_mod. Qed.
Lemma compose_join_keeps_mc_new_src_mod : forall c1 c2 k c, hw_mc_new_src_mod (compose_join_final c1 c2 k c) = hw_mc_new_src_mod c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_mc_new_src_mod, nouter_iter_keeps_mc_new_src_mod, mcnstart_keeps_mc_new_src_mod. apply join_iter_keeps_mc_new_src_mod. Qed.
Lemma compose_copy_keeps_mc_op : forall n c, hw_mc_op (compose_copy_final n c) = hw_mc_op c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_mc_op, nouter_iter_keeps_mc_op, mcnstart_keeps_mc_op. apply copy_iter_keeps_mc_op. Qed.
Lemma compose_join_keeps_mc_op : forall c1 c2 k c, hw_mc_op (compose_join_final c1 c2 k c) = hw_mc_op c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_mc_op, nouter_iter_keeps_mc_op, mcnstart_keeps_mc_op. apply join_iter_keeps_mc_op. Qed.
Lemma compose_copy_keeps_mc_pair_count : forall n c, hw_mc_pair_count (compose_copy_final n c) = hw_mc_pair_count c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_mc_pair_count, nouter_iter_keeps_mc_pair_count, mcnstart_keeps_mc_pair_count. apply copy_iter_keeps_mc_pair_count. Qed.
Lemma compose_join_keeps_mc_pair_count : forall c1 c2 k c, hw_mc_pair_count (compose_join_final c1 c2 k c) = hw_mc_pair_count c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_mc_pair_count, nouter_iter_keeps_mc_pair_count, mcnstart_keeps_mc_pair_count. apply join_iter_keeps_mc_pair_count. Qed.
Lemma compose_copy_keeps_mc_read_ptr : forall n c, hw_mc_read_ptr (compose_copy_final n c) = hw_mc_read_ptr c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_mc_read_ptr, nouter_iter_keeps_mc_read_ptr, mcnstart_keeps_mc_read_ptr. apply copy_iter_keeps_mc_read_ptr. Qed.
Lemma compose_join_keeps_mc_read_ptr : forall c1 c2 k c, hw_mc_read_ptr (compose_join_final c1 c2 k c) = hw_mc_read_ptr c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_mc_read_ptr, nouter_iter_keeps_mc_read_ptr, mcnstart_keeps_mc_read_ptr. apply join_iter_keeps_mc_read_ptr. Qed.
Lemma compose_copy_keeps_mc_src1_base : forall n c, hw_mc_src1_base (compose_copy_final n c) = hw_mc_src1_base c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_mc_src1_base, nouter_iter_keeps_mc_src1_base, mcnstart_keeps_mc_src1_base. apply copy_iter_keeps_mc_src1_base. Qed.
Lemma compose_join_keeps_mc_src1_base : forall c1 c2 k c, hw_mc_src1_base (compose_join_final c1 c2 k c) = hw_mc_src1_base c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_mc_src1_base, nouter_iter_keeps_mc_src1_base, mcnstart_keeps_mc_src1_base. apply join_iter_keeps_mc_src1_base. Qed.
Lemma compose_copy_keeps_mc_src1_count : forall n c, hw_mc_src1_count (compose_copy_final n c) = hw_mc_src1_count c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_mc_src1_count, nouter_iter_keeps_mc_src1_count, mcnstart_keeps_mc_src1_count. apply copy_iter_keeps_mc_src1_count. Qed.
Lemma compose_join_keeps_mc_src1_count : forall c1 c2 k c, hw_mc_src1_count (compose_join_final c1 c2 k c) = hw_mc_src1_count c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_mc_src1_count, nouter_iter_keeps_mc_src1_count, mcnstart_keeps_mc_src1_count. apply join_iter_keeps_mc_src1_count. Qed.
Lemma compose_copy_keeps_mc_src2_base : forall n c, hw_mc_src2_base (compose_copy_final n c) = hw_mc_src2_base c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_mc_src2_base, nouter_iter_keeps_mc_src2_base, mcnstart_keeps_mc_src2_base. apply copy_iter_keeps_mc_src2_base. Qed.
Lemma compose_join_keeps_mc_src2_base : forall c1 c2 k c, hw_mc_src2_base (compose_join_final c1 c2 k c) = hw_mc_src2_base c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_mc_src2_base, nouter_iter_keeps_mc_src2_base, mcnstart_keeps_mc_src2_base. apply join_iter_keeps_mc_src2_base. Qed.
Lemma compose_copy_keeps_mc_src2_count : forall n c, hw_mc_src2_count (compose_copy_final n c) = hw_mc_src2_count c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_mc_src2_count, nouter_iter_keeps_mc_src2_count, mcnstart_keeps_mc_src2_count. apply copy_iter_keeps_mc_src2_count. Qed.
Lemma compose_join_keeps_mc_src2_count : forall c1 c2 k c, hw_mc_src2_count (compose_join_final c1 c2 k c) = hw_mc_src2_count c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_mc_src2_count, nouter_iter_keeps_mc_src2_count, mcnstart_keeps_mc_src2_count. apply join_iter_keeps_mc_src2_count. Qed.
Lemma compose_copy_keeps_mc_write_base : forall n c, hw_mc_write_base (compose_copy_final n c) = hw_mc_write_base c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_mc_write_base, nouter_iter_keeps_mc_write_base, mcnstart_keeps_mc_write_base. apply copy_iter_keeps_mc_write_base. Qed.
Lemma compose_join_keeps_mc_write_base : forall c1 c2 k c, hw_mc_write_base (compose_join_final c1 c2 k c) = hw_mc_write_base c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_mc_write_base, nouter_iter_keeps_mc_write_base, mcnstart_keeps_mc_write_base. apply join_iter_keeps_mc_write_base. Qed.
Lemma compose_copy_keeps_mcycle_hi : forall n c, hw_mcycle_hi (compose_copy_final n c) = hw_mcycle_hi c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_mcycle_hi, nouter_iter_keeps_mcycle_hi, mcnstart_keeps_mcycle_hi. apply copy_iter_keeps_mcycle_hi. Qed.
Lemma compose_join_keeps_mcycle_hi : forall c1 c2 k c, hw_mcycle_hi (compose_join_final c1 c2 k c) = hw_mcycle_hi c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_mcycle_hi, nouter_iter_keeps_mcycle_hi, mcnstart_keeps_mcycle_hi. apply join_iter_keeps_mcycle_hi. Qed.
Lemma compose_copy_keeps_mcycle_lo : forall n c, hw_mcycle_lo (compose_copy_final n c) = hw_mcycle_lo c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_mcycle_lo, nouter_iter_keeps_mcycle_lo, mcnstart_keeps_mcycle_lo. apply copy_iter_keeps_mcycle_lo. Qed.
Lemma compose_join_keeps_mcycle_lo : forall c1 c2 k c, hw_mcycle_lo (compose_join_final c1 c2 k c) = hw_mcycle_lo c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_mcycle_lo, nouter_iter_keeps_mcycle_lo, mcnstart_keeps_mcycle_lo. apply join_iter_keeps_mcycle_lo. Qed.
Lemma compose_copy_keeps_mdl_ops : forall n c, hw_mdl_ops (compose_copy_final n c) = hw_mdl_ops c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_mdl_ops, nouter_iter_keeps_mdl_ops, mcnstart_keeps_mdl_ops. apply copy_iter_keeps_mdl_ops. Qed.
Lemma compose_join_keeps_mdl_ops : forall c1 c2 k c, hw_mdl_ops (compose_join_final c1 c2 k c) = hw_mdl_ops c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_mdl_ops, nouter_iter_keeps_mdl_ops, mcnstart_keeps_mdl_ops. apply join_iter_keeps_mdl_ops. Qed.
Lemma compose_copy_keeps_mem : forall n c, hw_mem (compose_copy_final n c) = hw_mem c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_mem, nouter_iter_keeps_mem, mcnstart_keeps_mem. apply copy_iter_keeps_mem. Qed.
Lemma compose_join_keeps_mem : forall c1 c2 k c, hw_mem (compose_join_final c1 c2 k c) = hw_mem c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_mem, nouter_iter_keeps_mem, mcnstart_keeps_mem. apply join_iter_keeps_mem. Qed.
Lemma compose_copy_keeps_minstret_hi : forall n c, hw_minstret_hi (compose_copy_final n c) = hw_minstret_hi c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_minstret_hi, nouter_iter_keeps_minstret_hi, mcnstart_keeps_minstret_hi. apply copy_iter_keeps_minstret_hi. Qed.
Lemma compose_join_keeps_minstret_hi : forall c1 c2 k c, hw_minstret_hi (compose_join_final c1 c2 k c) = hw_minstret_hi c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_minstret_hi, nouter_iter_keeps_minstret_hi, mcnstart_keeps_minstret_hi. apply join_iter_keeps_minstret_hi. Qed.
Lemma compose_copy_keeps_minstret_lo : forall n c, hw_minstret_lo (compose_copy_final n c) = hw_minstret_lo c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_minstret_lo, nouter_iter_keeps_minstret_lo, mcnstart_keeps_minstret_lo. apply copy_iter_keeps_minstret_lo. Qed.
Lemma compose_join_keeps_minstret_lo : forall c1 c2 k c, hw_minstret_lo (compose_join_final c1 c2 k c) = hw_minstret_lo c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_minstret_lo, nouter_iter_keeps_minstret_lo, mcnstart_keeps_minstret_lo. apply join_iter_keeps_minstret_lo. Qed.
Lemma compose_copy_keeps_module_tensors : forall n c, hw_module_tensors (compose_copy_final n c) = hw_module_tensors c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_module_tensors, nouter_iter_keeps_module_tensors, mcnstart_keeps_module_tensors. apply copy_iter_keeps_module_tensors. Qed.
Lemma compose_join_keeps_module_tensors : forall c1 c2 k c, hw_module_tensors (compose_join_final c1 c2 k c) = hw_module_tensors c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_module_tensors, nouter_iter_keeps_module_tensors, mcnstart_keeps_module_tensors. apply join_iter_keeps_module_tensors. Qed.
Lemma compose_copy_keeps_morph_coupling_desc_table : forall n c, hw_morph_coupling_desc_table (compose_copy_final n c) = hw_morph_coupling_desc_table c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_morph_coupling_desc_table, nouter_iter_keeps_morph_coupling_desc_table, mcnstart_keeps_morph_coupling_desc_table. apply copy_iter_keeps_morph_coupling_desc_table. Qed.
Lemma compose_join_keeps_morph_coupling_desc_table : forall c1 c2 k c, hw_morph_coupling_desc_table (compose_join_final c1 c2 k c) = hw_morph_coupling_desc_table c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_morph_coupling_desc_table, nouter_iter_keeps_morph_coupling_desc_table, mcnstart_keeps_morph_coupling_desc_table. apply join_iter_keeps_morph_coupling_desc_table. Qed.
Lemma compose_copy_keeps_morph_dst_table : forall n c, hw_morph_dst_table (compose_copy_final n c) = hw_morph_dst_table c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_morph_dst_table, nouter_iter_keeps_morph_dst_table, mcnstart_keeps_morph_dst_table. apply copy_iter_keeps_morph_dst_table. Qed.
Lemma compose_join_keeps_morph_dst_table : forall c1 c2 k c, hw_morph_dst_table (compose_join_final c1 c2 k c) = hw_morph_dst_table c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_morph_dst_table, nouter_iter_keeps_morph_dst_table, mcnstart_keeps_morph_dst_table. apply join_iter_keeps_morph_dst_table. Qed.
Lemma compose_copy_keeps_morph_identity_table : forall n c, hw_morph_identity_table (compose_copy_final n c) = hw_morph_identity_table c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_morph_identity_table, nouter_iter_keeps_morph_identity_table, mcnstart_keeps_morph_identity_table. apply copy_iter_keeps_morph_identity_table. Qed.
Lemma compose_join_keeps_morph_identity_table : forall c1 c2 k c, hw_morph_identity_table (compose_join_final c1 c2 k c) = hw_morph_identity_table c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_morph_identity_table, nouter_iter_keeps_morph_identity_table, mcnstart_keeps_morph_identity_table. apply join_iter_keeps_morph_identity_table. Qed.
Lemma compose_copy_keeps_morph_next_id : forall n c, hw_morph_next_id (compose_copy_final n c) = hw_morph_next_id c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_morph_next_id, nouter_iter_keeps_morph_next_id, mcnstart_keeps_morph_next_id. apply copy_iter_keeps_morph_next_id. Qed.
Lemma compose_join_keeps_morph_next_id : forall c1 c2 k c, hw_morph_next_id (compose_join_final c1 c2 k c) = hw_morph_next_id c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_morph_next_id, nouter_iter_keeps_morph_next_id, mcnstart_keeps_morph_next_id. apply join_iter_keeps_morph_next_id. Qed.
Lemma compose_copy_keeps_morph_src_table : forall n c, hw_morph_src_table (compose_copy_final n c) = hw_morph_src_table c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_morph_src_table, nouter_iter_keeps_morph_src_table, mcnstart_keeps_morph_src_table. apply copy_iter_keeps_morph_src_table. Qed.
Lemma compose_join_keeps_morph_src_table : forall c1 c2 k c, hw_morph_src_table (compose_join_final c1 c2 k c) = hw_morph_src_table c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_morph_src_table, nouter_iter_keeps_morph_src_table, mcnstart_keeps_morph_src_table. apply join_iter_keeps_morph_src_table. Qed.
Lemma compose_copy_keeps_morph_valid_table : forall n c, hw_morph_valid_table (compose_copy_final n c) = hw_morph_valid_table c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_morph_valid_table, nouter_iter_keeps_morph_valid_table, mcnstart_keeps_morph_valid_table. apply copy_iter_keeps_morph_valid_table. Qed.
Lemma compose_join_keeps_morph_valid_table : forall c1 c2 k c, hw_morph_valid_table (compose_join_final c1 c2 k c) = hw_morph_valid_table c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_morph_valid_table, nouter_iter_keeps_morph_valid_table, mcnstart_keeps_morph_valid_table. apply join_iter_keeps_morph_valid_table. Qed.
Lemma compose_copy_keeps_mstatus : forall n c, hw_mstatus (compose_copy_final n c) = hw_mstatus c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_mstatus, nouter_iter_keeps_mstatus, mcnstart_keeps_mstatus. apply copy_iter_keeps_mstatus. Qed.
Lemma compose_join_keeps_mstatus : forall c1 c2 k c, hw_mstatus (compose_join_final c1 c2 k c) = hw_mstatus c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_mstatus, nouter_iter_keeps_mstatus, mcnstart_keeps_mstatus. apply join_iter_keeps_mstatus. Qed.
Lemma compose_copy_keeps_mu : forall n c, hw_mu (compose_copy_final n c) = hw_mu c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_mu, nouter_iter_keeps_mu, mcnstart_keeps_mu. apply copy_iter_keeps_mu. Qed.
Lemma compose_join_keeps_mu : forall c1 c2 k c, hw_mu (compose_join_final c1 c2 k c) = hw_mu c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_mu, nouter_iter_keeps_mu, mcnstart_keeps_mu. apply join_iter_keeps_mu. Qed.
Lemma compose_copy_keeps_mu_tensor : forall n c, hw_mu_tensor (compose_copy_final n c) = hw_mu_tensor c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_mu_tensor, nouter_iter_keeps_mu_tensor, mcnstart_keeps_mu_tensor. apply copy_iter_keeps_mu_tensor. Qed.
Lemma compose_join_keeps_mu_tensor : forall c1 c2 k c, hw_mu_tensor (compose_join_final c1 c2 k c) = hw_mu_tensor c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_mu_tensor, nouter_iter_keeps_mu_tensor, mcnstart_keeps_mu_tensor. apply join_iter_keeps_mu_tensor. Qed.
Lemma compose_copy_keeps_partition_ops : forall n c, hw_partition_ops (compose_copy_final n c) = hw_partition_ops c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_partition_ops, nouter_iter_keeps_partition_ops, mcnstart_keeps_partition_ops. apply copy_iter_keeps_partition_ops. Qed.
Lemma compose_join_keeps_partition_ops : forall c1 c2 k c, hw_partition_ops (compose_join_final c1 c2 k c) = hw_partition_ops c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_partition_ops, nouter_iter_keeps_partition_ops, mcnstart_keeps_partition_ops. apply join_iter_keeps_partition_ops. Qed.
Lemma compose_copy_keeps_pc : forall n c, hw_pc (compose_copy_final n c) = hw_pc c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_pc, nouter_iter_keeps_pc, mcnstart_keeps_pc. apply copy_iter_keeps_pc. Qed.
Lemma compose_join_keeps_pc : forall c1 c2 k c, hw_pc (compose_join_final c1 c2 k c) = hw_pc c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_pc, nouter_iter_keeps_pc, mcnstart_keeps_pc. apply join_iter_keeps_pc. Qed.
Lemma compose_copy_keeps_ptTable : forall n c, hw_ptTable (compose_copy_final n c) = hw_ptTable c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_ptTable, nouter_iter_keeps_ptTable, mcnstart_keeps_ptTable. apply copy_iter_keeps_ptTable. Qed.
Lemma compose_join_keeps_ptTable : forall c1 c2 k c, hw_ptTable (compose_join_final c1 c2 k c) = hw_ptTable c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_ptTable, nouter_iter_keeps_ptTable, mcnstart_keeps_ptTable. apply join_iter_keeps_ptTable. Qed.
Lemma compose_copy_keeps_pt_next_id : forall n c, hw_pt_next_id (compose_copy_final n c) = hw_pt_next_id c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_pt_next_id, nouter_iter_keeps_pt_next_id, mcnstart_keeps_pt_next_id. apply copy_iter_keeps_pt_next_id. Qed.
Lemma compose_join_keeps_pt_next_id : forall c1 c2 k c, hw_pt_next_id (compose_join_final c1 c2 k c) = hw_pt_next_id c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_pt_next_id, nouter_iter_keeps_pt_next_id, mcnstart_keeps_pt_next_id. apply join_iter_keeps_pt_next_id. Qed.
Lemma compose_copy_keeps_regs : forall n c, hw_regs (compose_copy_final n c) = hw_regs c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_regs, nouter_iter_keeps_regs, mcnstart_keeps_regs. apply copy_iter_keeps_regs. Qed.
Lemma compose_join_keeps_regs : forall c1 c2 k c, hw_regs (compose_join_final c1 c2 k c) = hw_regs c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_regs, nouter_iter_keeps_regs, mcnstart_keeps_regs. apply join_iter_keeps_regs. Qed.
Lemma compose_copy_keeps_trap_vector : forall n c, hw_trap_vector (compose_copy_final n c) = hw_trap_vector c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_trap_vector, nouter_iter_keeps_trap_vector, mcnstart_keeps_trap_vector. apply copy_iter_keeps_trap_vector. Qed.
Lemma compose_join_keeps_trap_vector : forall c1 c2 k c, hw_trap_vector (compose_join_final c1 c2 k c) = hw_trap_vector c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_trap_vector, nouter_iter_keeps_trap_vector, mcnstart_keeps_trap_vector. apply join_iter_keeps_trap_vector. Qed.
Lemma compose_copy_keeps_wc_diff_00 : forall n c, hw_wc_diff_00 (compose_copy_final n c) = hw_wc_diff_00 c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_wc_diff_00, nouter_iter_keeps_wc_diff_00, mcnstart_keeps_wc_diff_00. apply copy_iter_keeps_wc_diff_00. Qed.
Lemma compose_join_keeps_wc_diff_00 : forall c1 c2 k c, hw_wc_diff_00 (compose_join_final c1 c2 k c) = hw_wc_diff_00 c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_wc_diff_00, nouter_iter_keeps_wc_diff_00, mcnstart_keeps_wc_diff_00. apply join_iter_keeps_wc_diff_00. Qed.
Lemma compose_copy_keeps_wc_diff_01 : forall n c, hw_wc_diff_01 (compose_copy_final n c) = hw_wc_diff_01 c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_wc_diff_01, nouter_iter_keeps_wc_diff_01, mcnstart_keeps_wc_diff_01. apply copy_iter_keeps_wc_diff_01. Qed.
Lemma compose_join_keeps_wc_diff_01 : forall c1 c2 k c, hw_wc_diff_01 (compose_join_final c1 c2 k c) = hw_wc_diff_01 c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_wc_diff_01, nouter_iter_keeps_wc_diff_01, mcnstart_keeps_wc_diff_01. apply join_iter_keeps_wc_diff_01. Qed.
Lemma compose_copy_keeps_wc_diff_10 : forall n c, hw_wc_diff_10 (compose_copy_final n c) = hw_wc_diff_10 c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_wc_diff_10, nouter_iter_keeps_wc_diff_10, mcnstart_keeps_wc_diff_10. apply copy_iter_keeps_wc_diff_10. Qed.
Lemma compose_join_keeps_wc_diff_10 : forall c1 c2 k c, hw_wc_diff_10 (compose_join_final c1 c2 k c) = hw_wc_diff_10 c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_wc_diff_10, nouter_iter_keeps_wc_diff_10, mcnstart_keeps_wc_diff_10. apply join_iter_keeps_wc_diff_10. Qed.
Lemma compose_copy_keeps_wc_diff_11 : forall n c, hw_wc_diff_11 (compose_copy_final n c) = hw_wc_diff_11 c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_wc_diff_11, nouter_iter_keeps_wc_diff_11, mcnstart_keeps_wc_diff_11. apply copy_iter_keeps_wc_diff_11. Qed.
Lemma compose_join_keeps_wc_diff_11 : forall c1 c2 k c, hw_wc_diff_11 (compose_join_final c1 c2 k c) = hw_wc_diff_11 c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_wc_diff_11, nouter_iter_keeps_wc_diff_11, mcnstart_keeps_wc_diff_11. apply join_iter_keeps_wc_diff_11. Qed.
Lemma compose_copy_keeps_wc_same_00 : forall n c, hw_wc_same_00 (compose_copy_final n c) = hw_wc_same_00 c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_wc_same_00, nouter_iter_keeps_wc_same_00, mcnstart_keeps_wc_same_00. apply copy_iter_keeps_wc_same_00. Qed.
Lemma compose_join_keeps_wc_same_00 : forall c1 c2 k c, hw_wc_same_00 (compose_join_final c1 c2 k c) = hw_wc_same_00 c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_wc_same_00, nouter_iter_keeps_wc_same_00, mcnstart_keeps_wc_same_00. apply join_iter_keeps_wc_same_00. Qed.
Lemma compose_copy_keeps_wc_same_01 : forall n c, hw_wc_same_01 (compose_copy_final n c) = hw_wc_same_01 c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_wc_same_01, nouter_iter_keeps_wc_same_01, mcnstart_keeps_wc_same_01. apply copy_iter_keeps_wc_same_01. Qed.
Lemma compose_join_keeps_wc_same_01 : forall c1 c2 k c, hw_wc_same_01 (compose_join_final c1 c2 k c) = hw_wc_same_01 c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_wc_same_01, nouter_iter_keeps_wc_same_01, mcnstart_keeps_wc_same_01. apply join_iter_keeps_wc_same_01. Qed.
Lemma compose_copy_keeps_wc_same_10 : forall n c, hw_wc_same_10 (compose_copy_final n c) = hw_wc_same_10 c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_wc_same_10, nouter_iter_keeps_wc_same_10, mcnstart_keeps_wc_same_10. apply copy_iter_keeps_wc_same_10. Qed.
Lemma compose_join_keeps_wc_same_10 : forall c1 c2 k c, hw_wc_same_10 (compose_join_final c1 c2 k c) = hw_wc_same_10 c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_wc_same_10, nouter_iter_keeps_wc_same_10, mcnstart_keeps_wc_same_10. apply join_iter_keeps_wc_same_10. Qed.
Lemma compose_copy_keeps_wc_same_11 : forall n c, hw_wc_same_11 (compose_copy_final n c) = hw_wc_same_11 c.
Proof. intros n c. unfold compose_copy_final, norm_commit_final. rewrite mccommit_keeps_wc_same_11, nouter_iter_keeps_wc_same_11, mcnstart_keeps_wc_same_11. apply copy_iter_keeps_wc_same_11. Qed.
Lemma compose_join_keeps_wc_same_11 : forall c1 c2 k c, hw_wc_same_11 (compose_join_final c1 c2 k c) = hw_wc_same_11 c.
Proof. intros c1 c2 k c. unfold compose_join_final, norm_commit_final. rewrite mccommit_keeps_wc_same_11, nouter_iter_keeps_wc_same_11, mcnstart_keeps_wc_same_11. apply join_iter_keeps_wc_same_11. Qed.
