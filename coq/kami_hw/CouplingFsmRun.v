(** CouplingFsmRun.v: the whole MORPH coupling FSM run at the typed boundary,
    from phase 1 to phase 0. [morph_fsm_run]: header, loading loop,
    normalization start, normalization loop and commit are an actual Kami
    execution; the committed pair slice is the deduplicated loaded pairs, pairs
    below the loading base are untouched, and the descriptor tables record the
    new descriptor. *)
Require Import Kami.Kami Kami.Semantics Kami.Lib.NatLib.
From Coq Require Import String List Arith Lia Bool.
Import ListNotations.
From KamiHW Require Import ThieleTypes ThieleCPUCore HWBoundary RuleNext RuleStep ActionEvaluator
  CoreRules CoreExecution NormalizationSteps NormalizationExecution NormalizationRetirement
  NormalizationLoop NormalizationPrefix NormalizationScanExecution NormalizationFrame MorphLoading
  RuleEnabled FsmDecoded ChshRetire CouplingFsmEnds CouplingFsmLoad CouplingFsmNorm.
Local Open Scope nat_scope.
Local Open Scope list_scope.

Lemma split1_5_27_small : forall n, n <= 16 -> split1 5 27 (natToWord 32 n) = natToWord 5 n.
Proof.
  intros n Hn. do 17 (destruct n as [|n]; [vm_compute; reflexivity|]). lia.
Qed.

Lemma weq_nat32_zero : forall n, n <= 16 ->
  (if weq (natToWord 32 n) (natToWord 32 0) then true else false) = Nat.eqb n 0.
Proof.
  intros n Hn. do 17 (destruct n as [|n]; [vm_compute; reflexivity|]). lia.
Qed.

(** Pairs below the loading base are untouched by the normalization loop. *)
Lemma nouter_prefix : forall rem c rawsrc rawdst src dst b i out e,
  e - i = rem -> i < e ->
  normalization_prefix_invariant rawsrc rawdst src dst b i out e ->
  hw_mc_phase c = natToWord 4 8 -> hw_mc_i c = natToWord 5 i -> hw_mc_j c = natToWord 5 (S i) ->
  hw_mc_write_ptr c = natToWord 5 e -> hw_mc_duplicate c = false -> hw_mc_norm_ptr c = natToWord 5 out ->
  hw_coupling_pair_src_table c = src -> hw_coupling_pair_dst_table c = dst ->
  forall k, k < b ->
  table_pair (hw_coupling_pair_src_table (nouter_iter rem c)) (hw_coupling_pair_dst_table (nouter_iter rem c)) k =
  table_pair src dst k.
Proof.
  induction rem as [|n IH]; intros c rawsrc rawdst src dst b i out e Hn Hi Hinv Hp Hic Hj Hw Hd Ho Hs Ht k Hk; [lia|].
  pose proof Hinv as [Hb _].
  destruct (nouter_step_facts c src dst i out e Hi ltac:(lia) Hp Hic Hj Hw Hd Ho Hs Ht)
    as [_ [Pp [Pi [Pj [Pw [Pd [Po [Ps Pt]]]]]]]].
  pose proof (normalization_prefix_preserved rawsrc rawdst src dst b i out e Hinv Hi) as Hinv1.
  cbv zeta in Hinv1, Pw, Po, Ps, Pt.
  assert (Step : table_pair (hw_coupling_pair_src_table (nouter_step c)) (hw_coupling_pair_dst_table (nouter_step c)) k =
                 table_pair src dst k).
  { rewrite Ps, Pt. apply table_pair_after_emit_other; lia. }
  cbn [nouter_iter].
  destruct (Nat.eq_dec (S i) e) as [E|E].
  - assert (n = 0) by lia. subst n. cbn [nouter_iter]. exact Step.
  - rewrite (proj2 (Nat.eqb_neq _ _) E) in Pp, Pw.
    rewrite (IH (nouter_step c) rawsrc rawdst _ _ b (S i) _ e ltac:(lia) ltac:(lia) Hinv1
      Pp Pi Pj Pw Pd Po Ps Pt k Hk).
    rewrite <- Ps, <- Pt. exact Step.
Qed.

Lemma fire_rule : forall idx b next, idx <= 11 ->
  (exists u, eval_cpu_rule (hwb_regs b) (normalization_rule idx) = Some u /\ M.union u (hwb_regs b) = hwb_regs next) ->
  exists l, Multistep thieleCore (hwb_regs b) (hwb_regs next) l.
Proof.
  intros idx b next Hi [u [Hu Eu]]. eexists. rewrite <- Eu.
  apply normalization_substep_execution. exact (cpu_rule_substep _ _ _ (rule_in_index idx Hi) Hu).
Qed.

Lemma multi_join : forall a b c, (exists l, Multistep thieleCore a b l) -> (exists l, Multistep thieleCore b c l) ->
  exists l, Multistep thieleCore a c l.
Proof. intros a b c [l1 H1] [l2 H2]. eexists. exact (normalization_multistep_trans _ _ _ _ _ H1 H2). Qed.

Definition morph_fsm_final (count : nat) (c0 : HWB) : HWB :=
  mccommit_next (nouter_iter count (mcnstart_next (mload_iter count (mchdr_next c0)))).

Theorem morph_fsm_run : forall c0 (base : word 7) P count,
  hw_mc_phase c0 = WO~0~0~0~1 ->
  hw_mc_mem_base c0 = zext base 25 ->
  hw_coupling_pair_next_id c0 = natToWord 5 P ->
  hw_mc_write_base c0 = natToWord 5 P -> hw_mc_write_ptr c0 = natToWord 5 P ->
  hw_mem c0 (split1 7 25 (zext base 25)) = natToWord 32 count ->
  count + P <= 16 -> 2 * count + wordToNat base <= 127 ->
  let r := wplus (zext base 25) (natToWord 32 1) in
  let rawsrc := loaded_table (hw_mem c0) r P count (hw_coupling_pair_src_table c0) 0 in
  let rawdst := loaded_table (hw_mem c0) r P count (hw_coupling_pair_dst_table c0) 1 in
  exists labels out src' dst',
    Multistep thieleCore (hwb_regs c0) (hwb_regs (morph_fsm_final count c0)) labels /\
    P <= out <= P + count /\
    table_slice src' dst' P (out - P) = nodup coupling_pair_eq_dec (table_slice rawsrc rawdst P count) /\
    (forall k, k < P -> table_pair src' dst' k = table_pair (hw_coupling_pair_src_table c0) (hw_coupling_pair_dst_table c0) k) /\
    hw_coupling_pair_src_table (morph_fsm_final count c0) = src' /\
    hw_coupling_pair_dst_table (morph_fsm_final count c0) = dst' /\
    hw_coupling_pair_valid_table (morph_fsm_final count c0) = loaded_valid P count (hw_coupling_pair_valid_table c0) /\
    hw_coupling_pair_next_id (morph_fsm_final count c0) = natToWord 5 out /\
    hw_mc_phase (morph_fsm_final count c0) = natToWord 4 0 /\
    hw_mc_write_base (morph_fsm_final count c0) = natToWord 5 P /\
    hw_coupling_desc_base_table (morph_fsm_final count c0) =
      put_vector (hw_coupling_desc_base_table c0) (split1 4 1 (hw_coupling_desc_next_id c0)) (split1 4 1 (natToWord 5 P)) /\
    hw_coupling_desc_count_table (morph_fsm_final count c0) =
      put_vector (hw_coupling_desc_count_table c0) (split1 4 1 (hw_coupling_desc_next_id c0))
        (wminus (natToWord 5 out) (natToWord 5 P)) /\
    hw_coupling_desc_valid_table (morph_fsm_final count c0) =
      put_vector (hw_coupling_desc_valid_table c0) (split1 4 1 (hw_coupling_desc_next_id c0)) true /\
    hw_coupling_desc_next_id (morph_fsm_final count c0) = wplus (hw_coupling_desc_next_id c0) (natToWord 5 1) /\
    hw_err (morph_fsm_final count c0) = hw_err c0 /\
    hw_error_code (morph_fsm_final count c0) = hw_error_code c0.
Proof.
  intros c0 base P count Hp Hb Hn Hwb Hwp Hm Hc Hs r rawsrc rawdst.
  set (s1 := mchdr_next c0).
  assert (Fits : mchdr_mc_fits c0 = true).
  { apply (mchdr_fits_nat c0 base P count Hb Hn ltac:(lia)); [rewrite mchdr_raw_count, Hb; exact Hm|lia|lia]. }
  assert (S1p : hw_mc_phase s1 = if Nat.eqb count 0 then WO~0~1~0~1 else WO~0~0~1~0).
  { unfold s1. rewrite mchdr_phase, Fits, mchdr_raw_count, Hb, Hm, weq_nat32_zero by lia. reflexivity. }
  assert (S1err : hw_err s1 = hw_err c0) by (unfold s1; rewrite mchdr_err, Fits, orb_false_r; reflexivity).
  assert (S1ec : hw_error_code s1 = hw_error_code c0) by (unfold s1; rewrite mchdr_error_code, Fits; reflexivity).
  (* the loading loop *)
  set (s2 := mload_iter count s1).
  assert (L : (forall m, m < count -> hw_mc_phase (mload_iter m s1) = WO~0~0~1~0) /\
    hw_mc_phase s2 = WO~0~1~0~1 /\
    hw_mc_write_ptr s2 = natToWord 5 (P + count) /\
    hw_coupling_pair_src_table s2 = rawsrc /\ hw_coupling_pair_dst_table s2 = rawdst /\
    hw_coupling_pair_valid_table s2 = loaded_valid P count (hw_coupling_pair_valid_table c0)).
  { destruct count as [|n].
    - unfold s2. cbn [mload_iter loaded_table loaded_valid]. unfold s1 in *.
      split; [intros; lia|]. rewrite S1p. split; [reflexivity|].
      rewrite mchdr_keeps_mc_write_ptr, Hwp, Nat.add_0_r.
      rewrite mchdr_keeps_coupling_pair_src_table, mchdr_keeps_coupling_pair_dst_table,
        mchdr_keeps_coupling_pair_valid_table. auto.
    - destruct (mload_loop (S n) s1 r P 0 (S n) (hw_coupling_pair_src_table c0) (hw_coupling_pair_dst_table c0)
        (hw_coupling_pair_valid_table c0) ltac:(lia) ltac:(lia) ltac:(rewrite S1p; reflexivity)
        ltac:(unfold s1; rewrite mchdr_read_ptr, Hb; reflexivity)
        ltac:(unfold s1; rewrite mchdr_keeps_mc_write_ptr; exact Hwp)
        ltac:(unfold s1; apply mchdr_i)
        ltac:(unfold s1; rewrite mchdr_pair_count, mchdr_raw_count, Hb, Hm; apply split1_5_27_small; lia)
        ltac:(unfold s1; apply mchdr_keeps_coupling_pair_src_table)
        ltac:(unfold s1; apply mchdr_keeps_coupling_pair_dst_table)
        ltac:(unfold s1; apply mchdr_keeps_coupling_pair_valid_table))
        as [A [B [C [D [E F]]]]].
      unfold rawsrc, rawdst, s2. unfold s1 in D, E. rewrite mchdr_keeps_mem in D, E.
      split; [exact A|]. split; [exact B|]. split; [rewrite C; reflexivity|]. split; [exact D|]. split; [exact E|exact F].
  }
  destruct L as [La [Lp [Lw [Ls [Ld Lv]]]]].
  assert (S2wb : hw_mc_write_base s2 = natToWord 5 P)
    by (unfold s2, s1; rewrite mload_iter_keeps_mc_write_base, mchdr_keeps_mc_write_base; exact Hwb).
  set (s3 := mcnstart_next s2).
  assert (S3p : hw_mc_phase s3 = natToWord 4 (if Nat.eqb count 0 then 11 else 8)).
  { unfold s3. rewrite mcnstart_phase, S2wb, Lw, weq_nat5 by lia.
    destruct count as [|n]; [rewrite Nat.add_0_r, Nat.eqb_refl; reflexivity|].
    rewrite (proj2 (Nat.eqb_neq P (P + S n)) ltac:(lia)). reflexivity. }
  assert (S3i : hw_mc_i s3 = natToWord 5 P) by (unfold s3; rewrite mcnstart_i; exact S2wb).
  assert (S3j : hw_mc_j s3 = natToWord 5 (S P)) by (unfold s3; rewrite mcnstart_j, S2wb; apply succ_word5).
  assert (S3o : hw_mc_norm_ptr s3 = natToWord 5 P) by (unfold s3; rewrite mcnstart_norm; exact S2wb).
  assert (S3d : hw_mc_duplicate s3 = false) by (unfold s3; apply mcnstart_dup).
  assert (S3w : hw_mc_write_ptr s3 = natToWord 5 (P + count)) by (unfold s3; rewrite mcnstart_keeps_mc_write_ptr; exact Lw).
  assert (S3s : hw_coupling_pair_src_table s3 = rawsrc) by (unfold s3; rewrite mcnstart_keeps_coupling_pair_src_table; exact Ls).
  assert (S3t : hw_coupling_pair_dst_table s3 = rawdst) by (unfold s3; rewrite mcnstart_keeps_coupling_pair_dst_table; exact Ld).
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
    by (unfold s4, s3; rewrite nouter_iter_keeps_mc_write_base, mcnstart_keeps_mc_write_base; exact S2wb).
  assert (Dn : hw_coupling_desc_next_id s4 = hw_coupling_desc_next_id c0)
    by (unfold s4, s3, s2, s1; rewrite nouter_iter_keeps_coupling_desc_next_id, mcnstart_keeps_coupling_desc_next_id,
          mload_iter_keeps_coupling_desc_next_id, mchdr_keeps_coupling_desc_next_id; reflexivity).
  assert (M : exists l, Multistep thieleCore (hwb_regs c0) (hwb_regs (mccommit_next s4)) l).
  { apply (multi_join _ (hwb_regs s1)).
    { apply (fire_rule 3 c0 s1 ltac:(lia)). apply mchdr_enabled. cbn [evalExpr evalConstT]. rewrite Hp. reflexivity. }
    apply (multi_join _ (hwb_regs s2)); [exists (mload_labels count); exact (mload_multistep count s1 La)|].
    apply (multi_join _ (hwb_regs s3)).
    { apply (fire_rule 7 s2 s3 ltac:(lia)). apply mcnstart_enabled. cbn [evalExpr evalConstT]. rewrite Lp. reflexivity. }
    apply (multi_join _ (hwb_regs s4)); [exact Mn|].
    apply (fire_rule 10 s4 (mccommit_next s4) ltac:(lia)). apply mccommit_enabled.
    cbn [evalExpr evalConstT]. rewrite N4p. reflexivity. }
  destruct M as [l Hl].
  change (morph_fsm_final count c0) with (mccommit_next s4).
  exists l, out, src', dst'.
  split; [exact Hl|]. split; [exact Hout|]. split; [exact Hslice|].
  split.
  { intros k Hk. rewrite Hpre by exact Hk. unfold rawsrc, rawdst, table_pair.
    rewrite !loaded_table_outside by lia. reflexivity. }
  rewrite mccommit_keeps_coupling_pair_src_table, mccommit_keeps_coupling_pair_dst_table, N4s, N4t.
  split; [reflexivity|]. split; [reflexivity|].
  rewrite mccommit_keeps_coupling_pair_valid_table.
  split; [unfold s4, s3; rewrite nouter_iter_keeps_coupling_pair_valid_table, mcnstart_keeps_coupling_pair_valid_table; exact Lv|].
  rewrite mccommit_pair_next, N4w. split; [reflexivity|].
  split; [apply mccommit_phase|].
  rewrite mccommit_keeps_mc_write_base, S4wb. split; [reflexivity|].
  rewrite mccommit_base, mccommit_count, mccommit_valid, mccommit_desc_next, Dn, S4wb, N4w.
  assert (Keep : forall A (f : HWB -> A),
    (forall c, f (nouter_iter count c) = f c) -> (forall c, f (mcnstart_next c) = f c) ->
    (forall c, f (mload_iter count c) = f c) -> (forall c, f (mchdr_next c) = f c) -> f s4 = f c0).
  { intros A f K1 K2 K3 K4. unfold s4, s3, s2, s1. rewrite K1, K2, K3, K4. reflexivity. }
  rewrite (Keep _ hw_coupling_desc_base_table (nouter_iter_keeps_coupling_desc_base_table count)
    mcnstart_keeps_coupling_desc_base_table (mload_iter_keeps_coupling_desc_base_table count)
    mchdr_keeps_coupling_desc_base_table).
  rewrite (Keep _ hw_coupling_desc_count_table (nouter_iter_keeps_coupling_desc_count_table count)
    mcnstart_keeps_coupling_desc_count_table (mload_iter_keeps_coupling_desc_count_table count)
    mchdr_keeps_coupling_desc_count_table).
  rewrite (Keep _ hw_coupling_desc_valid_table (nouter_iter_keeps_coupling_desc_valid_table count)
    mcnstart_keeps_coupling_desc_valid_table (mload_iter_keeps_coupling_desc_valid_table count)
    mchdr_keeps_coupling_desc_valid_table).
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  rewrite mccommit_keeps_err, mccommit_keeps_error_code.
  unfold s4, s3, s2.
  rewrite nouter_iter_keeps_err, mcnstart_keeps_err, mload_iter_keeps_err, S1err.
  rewrite nouter_iter_keeps_error_code, mcnstart_keeps_error_code, mload_iter_keeps_error_code, S1ec.
  split; reflexivity.
Qed.


(** Registers the run leaves unchanged. *)
Lemma morph_fsm_keeps_pc : forall n c, hw_pc (morph_fsm_final n c) = hw_pc c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_pc, nouter_iter_keeps_pc, mcnstart_keeps_pc, mload_iter_keeps_pc. apply mchdr_keeps_pc. Qed.
Lemma morph_fsm_keeps_mu : forall n c, hw_mu (morph_fsm_final n c) = hw_mu c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_mu, nouter_iter_keeps_mu, mcnstart_keeps_mu, mload_iter_keeps_mu. apply mchdr_keeps_mu. Qed.
Lemma morph_fsm_keeps_halted : forall n c, hw_halted (morph_fsm_final n c) = hw_halted c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_halted, nouter_iter_keeps_halted, mcnstart_keeps_halted, mload_iter_keeps_halted. apply mchdr_keeps_halted. Qed.
Lemma morph_fsm_keeps_regs : forall n c, hw_regs (morph_fsm_final n c) = hw_regs c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_regs, nouter_iter_keeps_regs, mcnstart_keeps_regs, mload_iter_keeps_regs. apply mchdr_keeps_regs. Qed.
Lemma morph_fsm_keeps_mem : forall n c, hw_mem (morph_fsm_final n c) = hw_mem c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_mem, nouter_iter_keeps_mem, mcnstart_keeps_mem, mload_iter_keeps_mem. apply mchdr_keeps_mem. Qed.
Lemma morph_fsm_keeps_imem : forall n c, hw_imem (morph_fsm_final n c) = hw_imem c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_imem, nouter_iter_keeps_imem, mcnstart_keeps_imem, mload_iter_keeps_imem. apply mchdr_keeps_imem. Qed.
Lemma morph_fsm_keeps_partition_ops : forall n c, hw_partition_ops (morph_fsm_final n c) = hw_partition_ops c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_partition_ops, nouter_iter_keeps_partition_ops, mcnstart_keeps_partition_ops, mload_iter_keeps_partition_ops. apply mchdr_keeps_partition_ops. Qed.
Lemma morph_fsm_keeps_mdl_ops : forall n c, hw_mdl_ops (morph_fsm_final n c) = hw_mdl_ops c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_mdl_ops, nouter_iter_keeps_mdl_ops, mcnstart_keeps_mdl_ops, mload_iter_keeps_mdl_ops. apply mchdr_keeps_mdl_ops. Qed.
Lemma morph_fsm_keeps_info_gain : forall n c, hw_info_gain (morph_fsm_final n c) = hw_info_gain c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_info_gain, nouter_iter_keeps_info_gain, mcnstart_keeps_info_gain, mload_iter_keeps_info_gain. apply mchdr_keeps_info_gain. Qed.
Lemma morph_fsm_keeps_logic_acc : forall n c, hw_logic_acc (morph_fsm_final n c) = hw_logic_acc c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_logic_acc, nouter_iter_keeps_logic_acc, mcnstart_keeps_logic_acc, mload_iter_keeps_logic_acc. apply mchdr_keeps_logic_acc. Qed.
Lemma morph_fsm_keeps_cert_addr : forall n c, hw_cert_addr (morph_fsm_final n c) = hw_cert_addr c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_cert_addr, nouter_iter_keeps_cert_addr, mcnstart_keeps_cert_addr, mload_iter_keeps_cert_addr. apply mchdr_keeps_cert_addr. Qed.
Lemma morph_fsm_keeps_active_module : forall n c, hw_active_module (morph_fsm_final n c) = hw_active_module c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_active_module, nouter_iter_keeps_active_module, mcnstart_keeps_active_module, mload_iter_keeps_active_module. apply mchdr_keeps_active_module. Qed.
Lemma morph_fsm_keeps_mstatus : forall n c, hw_mstatus (morph_fsm_final n c) = hw_mstatus c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_mstatus, nouter_iter_keeps_mstatus, mcnstart_keeps_mstatus, mload_iter_keeps_mstatus. apply mchdr_keeps_mstatus. Qed.
Lemma morph_fsm_keeps_mcycle_lo : forall n c, hw_mcycle_lo (morph_fsm_final n c) = hw_mcycle_lo c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_mcycle_lo, nouter_iter_keeps_mcycle_lo, mcnstart_keeps_mcycle_lo, mload_iter_keeps_mcycle_lo. apply mchdr_keeps_mcycle_lo. Qed.
Lemma morph_fsm_keeps_mcycle_hi : forall n c, hw_mcycle_hi (morph_fsm_final n c) = hw_mcycle_hi c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_mcycle_hi, nouter_iter_keeps_mcycle_hi, mcnstart_keeps_mcycle_hi, mload_iter_keeps_mcycle_hi. apply mchdr_keeps_mcycle_hi. Qed.
Lemma morph_fsm_keeps_minstret_lo : forall n c, hw_minstret_lo (morph_fsm_final n c) = hw_minstret_lo c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_minstret_lo, nouter_iter_keeps_minstret_lo, mcnstart_keeps_minstret_lo, mload_iter_keeps_minstret_lo. apply mchdr_keeps_minstret_lo. Qed.
Lemma morph_fsm_keeps_minstret_hi : forall n c, hw_minstret_hi (morph_fsm_final n c) = hw_minstret_hi c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_minstret_hi, nouter_iter_keeps_minstret_hi, mcnstart_keeps_minstret_hi, mload_iter_keeps_minstret_hi. apply mchdr_keeps_minstret_hi. Qed.
Lemma morph_fsm_keeps_trap_vector : forall n c, hw_trap_vector (morph_fsm_final n c) = hw_trap_vector c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_trap_vector, nouter_iter_keeps_trap_vector, mcnstart_keeps_trap_vector, mload_iter_keeps_trap_vector. apply mchdr_keeps_trap_vector. Qed.
Lemma morph_fsm_keeps_certified : forall n c, hw_certified (morph_fsm_final n c) = hw_certified c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_certified, nouter_iter_keeps_certified, mcnstart_keeps_certified, mload_iter_keeps_certified. apply mchdr_keeps_certified. Qed.
Lemma morph_fsm_keeps_lassert_phase : forall n c, hw_lassert_phase (morph_fsm_final n c) = hw_lassert_phase c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_lassert_phase, nouter_iter_keeps_lassert_phase, mcnstart_keeps_lassert_phase, mload_iter_keeps_lassert_phase. apply mchdr_keeps_lassert_phase. Qed.
Lemma morph_fsm_keeps_lassert_kind : forall n c, hw_lassert_kind (morph_fsm_final n c) = hw_lassert_kind c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_lassert_kind, nouter_iter_keeps_lassert_kind, mcnstart_keeps_lassert_kind, mload_iter_keeps_lassert_kind. apply mchdr_keeps_lassert_kind. Qed.
Lemma morph_fsm_keeps_lassert_fbase : forall n c, hw_lassert_fbase (morph_fsm_final n c) = hw_lassert_fbase c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_lassert_fbase, nouter_iter_keeps_lassert_fbase, mcnstart_keeps_lassert_fbase, mload_iter_keeps_lassert_fbase. apply mchdr_keeps_lassert_fbase. Qed.
Lemma morph_fsm_keeps_lassert_cbase : forall n c, hw_lassert_cbase (morph_fsm_final n c) = hw_lassert_cbase c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_lassert_cbase, nouter_iter_keeps_lassert_cbase, mcnstart_keeps_lassert_cbase, mload_iter_keeps_lassert_cbase. apply mchdr_keeps_lassert_cbase. Qed.
Lemma morph_fsm_keeps_lassert_flen : forall n c, hw_lassert_flen (morph_fsm_final n c) = hw_lassert_flen c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_lassert_flen, nouter_iter_keeps_lassert_flen, mcnstart_keeps_lassert_flen, mload_iter_keeps_lassert_flen. apply mchdr_keeps_lassert_flen. Qed.
Lemma morph_fsm_keeps_lassert_clen : forall n c, hw_lassert_clen (morph_fsm_final n c) = hw_lassert_clen c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_lassert_clen, nouter_iter_keeps_lassert_clen, mcnstart_keeps_lassert_clen, mload_iter_keeps_lassert_clen. apply mchdr_keeps_lassert_clen. Qed.
Lemma morph_fsm_keeps_lassert_nvars : forall n c, hw_lassert_nvars (morph_fsm_final n c) = hw_lassert_nvars c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_lassert_nvars, nouter_iter_keeps_lassert_nvars, mcnstart_keeps_lassert_nvars, mload_iter_keeps_lassert_nvars. apply mchdr_keeps_lassert_nvars. Qed.
Lemma morph_fsm_keeps_lassert_fptr : forall n c, hw_lassert_fptr (morph_fsm_final n c) = hw_lassert_fptr c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_lassert_fptr, nouter_iter_keeps_lassert_fptr, mcnstart_keeps_lassert_fptr, mload_iter_keeps_lassert_fptr. apply mchdr_keeps_lassert_fptr. Qed.
Lemma morph_fsm_keeps_lassert_cptr : forall n c, hw_lassert_cptr (morph_fsm_final n c) = hw_lassert_cptr c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_lassert_cptr, nouter_iter_keeps_lassert_cptr, mcnstart_keeps_lassert_cptr, mload_iter_keeps_lassert_cptr. apply mchdr_keeps_lassert_cptr. Qed.
Lemma morph_fsm_keeps_lassert_fbuf : forall n c, hw_lassert_fbuf (morph_fsm_final n c) = hw_lassert_fbuf c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_lassert_fbuf, nouter_iter_keeps_lassert_fbuf, mcnstart_keeps_lassert_fbuf, mload_iter_keeps_lassert_fbuf. apply mchdr_keeps_lassert_fbuf. Qed.
Lemma morph_fsm_keeps_lassert_cbuf : forall n c, hw_lassert_cbuf (morph_fsm_final n c) = hw_lassert_cbuf c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_lassert_cbuf, nouter_iter_keeps_lassert_cbuf, mcnstart_keeps_lassert_cbuf, mload_iter_keeps_lassert_cbuf. apply mchdr_keeps_lassert_cbuf. Qed.
Lemma morph_fsm_keeps_lassert_clause_sat : forall n c, hw_lassert_clause_sat (morph_fsm_final n c) = hw_lassert_clause_sat c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_lassert_clause_sat, nouter_iter_keeps_lassert_clause_sat, mcnstart_keeps_lassert_clause_sat, mload_iter_keeps_lassert_clause_sat. apply mchdr_keeps_lassert_clause_sat. Qed.
Lemma morph_fsm_keeps_lassert_counter_clause_sat : forall n c, hw_lassert_counter_clause_sat (morph_fsm_final n c) = hw_lassert_counter_clause_sat c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_lassert_counter_clause_sat, nouter_iter_keeps_lassert_counter_clause_sat, mcnstart_keeps_lassert_counter_clause_sat, mload_iter_keeps_lassert_counter_clause_sat. apply mchdr_keeps_lassert_counter_clause_sat. Qed.
Lemma morph_fsm_keeps_lassert_counter_seen_fail : forall n c, hw_lassert_counter_seen_fail (morph_fsm_final n c) = hw_lassert_counter_seen_fail c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_lassert_counter_seen_fail, nouter_iter_keeps_lassert_counter_seen_fail, mcnstart_keeps_lassert_counter_seen_fail, mload_iter_keeps_lassert_counter_seen_fail. apply mchdr_keeps_lassert_counter_seen_fail. Qed.
Lemma morph_fsm_keeps_chsh_phase : forall n c, hw_chsh_phase (morph_fsm_final n c) = hw_chsh_phase c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_chsh_phase, nouter_iter_keeps_chsh_phase, mcnstart_keeps_chsh_phase, mload_iter_keeps_chsh_phase. apply mchdr_keeps_chsh_phase. Qed.
Lemma morph_fsm_keeps_chsh_n00 : forall n c, hw_chsh_n00 (morph_fsm_final n c) = hw_chsh_n00 c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_chsh_n00, nouter_iter_keeps_chsh_n00, mcnstart_keeps_chsh_n00, mload_iter_keeps_chsh_n00. apply mchdr_keeps_chsh_n00. Qed.
Lemma morph_fsm_keeps_chsh_n01 : forall n c, hw_chsh_n01 (morph_fsm_final n c) = hw_chsh_n01 c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_chsh_n01, nouter_iter_keeps_chsh_n01, mcnstart_keeps_chsh_n01, mload_iter_keeps_chsh_n01. apply mchdr_keeps_chsh_n01. Qed.
Lemma morph_fsm_keeps_chsh_n10 : forall n c, hw_chsh_n10 (morph_fsm_final n c) = hw_chsh_n10 c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_chsh_n10, nouter_iter_keeps_chsh_n10, mcnstart_keeps_chsh_n10, mload_iter_keeps_chsh_n10. apply mchdr_keeps_chsh_n10. Qed.
Lemma morph_fsm_keeps_chsh_n11 : forall n c, hw_chsh_n11 (morph_fsm_final n c) = hw_chsh_n11 c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_chsh_n11, nouter_iter_keeps_chsh_n11, mcnstart_keeps_chsh_n11, mload_iter_keeps_chsh_n11. apply mchdr_keeps_chsh_n11. Qed.
Lemma morph_fsm_keeps_chsh_d00 : forall n c, hw_chsh_d00 (morph_fsm_final n c) = hw_chsh_d00 c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_chsh_d00, nouter_iter_keeps_chsh_d00, mcnstart_keeps_chsh_d00, mload_iter_keeps_chsh_d00. apply mchdr_keeps_chsh_d00. Qed.
Lemma morph_fsm_keeps_chsh_d01 : forall n c, hw_chsh_d01 (morph_fsm_final n c) = hw_chsh_d01 c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_chsh_d01, nouter_iter_keeps_chsh_d01, mcnstart_keeps_chsh_d01, mload_iter_keeps_chsh_d01. apply mchdr_keeps_chsh_d01. Qed.
Lemma morph_fsm_keeps_chsh_d10 : forall n c, hw_chsh_d10 (morph_fsm_final n c) = hw_chsh_d10 c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_chsh_d10, nouter_iter_keeps_chsh_d10, mcnstart_keeps_chsh_d10, mload_iter_keeps_chsh_d10. apply mchdr_keeps_chsh_d10. Qed.
Lemma morph_fsm_keeps_chsh_d11 : forall n c, hw_chsh_d11 (morph_fsm_final n c) = hw_chsh_d11 c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_chsh_d11, nouter_iter_keeps_chsh_d11, mcnstart_keeps_chsh_d11, mload_iter_keeps_chsh_d11. apply mchdr_keeps_chsh_d11. Qed.
Lemma morph_fsm_keeps_chsh_sign00 : forall n c, hw_chsh_sign00 (morph_fsm_final n c) = hw_chsh_sign00 c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_chsh_sign00, nouter_iter_keeps_chsh_sign00, mcnstart_keeps_chsh_sign00, mload_iter_keeps_chsh_sign00. apply mchdr_keeps_chsh_sign00. Qed.
Lemma morph_fsm_keeps_chsh_sign01 : forall n c, hw_chsh_sign01 (morph_fsm_final n c) = hw_chsh_sign01 c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_chsh_sign01, nouter_iter_keeps_chsh_sign01, mcnstart_keeps_chsh_sign01, mload_iter_keeps_chsh_sign01. apply mchdr_keeps_chsh_sign01. Qed.
Lemma morph_fsm_keeps_chsh_sign10 : forall n c, hw_chsh_sign10 (morph_fsm_final n c) = hw_chsh_sign10 c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_chsh_sign10, nouter_iter_keeps_chsh_sign10, mcnstart_keeps_chsh_sign10, mload_iter_keeps_chsh_sign10. apply mchdr_keeps_chsh_sign10. Qed.
Lemma morph_fsm_keeps_chsh_sign11 : forall n c, hw_chsh_sign11 (morph_fsm_final n c) = hw_chsh_sign11 c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_chsh_sign11, nouter_iter_keeps_chsh_sign11, mcnstart_keeps_chsh_sign11, mload_iter_keeps_chsh_sign11. apply mchdr_keeps_chsh_sign11. Qed.
Lemma morph_fsm_keeps_chsh_n00sq : forall n c, hw_chsh_n00sq (morph_fsm_final n c) = hw_chsh_n00sq c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_chsh_n00sq, nouter_iter_keeps_chsh_n00sq, mcnstart_keeps_chsh_n00sq, mload_iter_keeps_chsh_n00sq. apply mchdr_keeps_chsh_n00sq. Qed.
Lemma morph_fsm_keeps_chsh_n01sq : forall n c, hw_chsh_n01sq (morph_fsm_final n c) = hw_chsh_n01sq c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_chsh_n01sq, nouter_iter_keeps_chsh_n01sq, mcnstart_keeps_chsh_n01sq, mload_iter_keeps_chsh_n01sq. apply mchdr_keeps_chsh_n01sq. Qed.
Lemma morph_fsm_keeps_chsh_n10sq : forall n c, hw_chsh_n10sq (morph_fsm_final n c) = hw_chsh_n10sq c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_chsh_n10sq, nouter_iter_keeps_chsh_n10sq, mcnstart_keeps_chsh_n10sq, mload_iter_keeps_chsh_n10sq. apply mchdr_keeps_chsh_n10sq. Qed.
Lemma morph_fsm_keeps_chsh_n11sq : forall n c, hw_chsh_n11sq (morph_fsm_final n c) = hw_chsh_n11sq c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_chsh_n11sq, nouter_iter_keeps_chsh_n11sq, mcnstart_keeps_chsh_n11sq, mload_iter_keeps_chsh_n11sq. apply mchdr_keeps_chsh_n11sq. Qed.
Lemma morph_fsm_keeps_chsh_d00sq : forall n c, hw_chsh_d00sq (morph_fsm_final n c) = hw_chsh_d00sq c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_chsh_d00sq, nouter_iter_keeps_chsh_d00sq, mcnstart_keeps_chsh_d00sq, mload_iter_keeps_chsh_d00sq. apply mchdr_keeps_chsh_d00sq. Qed.
Lemma morph_fsm_keeps_chsh_d01sq : forall n c, hw_chsh_d01sq (morph_fsm_final n c) = hw_chsh_d01sq c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_chsh_d01sq, nouter_iter_keeps_chsh_d01sq, mcnstart_keeps_chsh_d01sq, mload_iter_keeps_chsh_d01sq. apply mchdr_keeps_chsh_d01sq. Qed.
Lemma morph_fsm_keeps_chsh_d10sq : forall n c, hw_chsh_d10sq (morph_fsm_final n c) = hw_chsh_d10sq c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_chsh_d10sq, nouter_iter_keeps_chsh_d10sq, mcnstart_keeps_chsh_d10sq, mload_iter_keeps_chsh_d10sq. apply mchdr_keeps_chsh_d10sq. Qed.
Lemma morph_fsm_keeps_chsh_d11sq : forall n c, hw_chsh_d11sq (morph_fsm_final n c) = hw_chsh_d11sq c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_chsh_d11sq, nouter_iter_keeps_chsh_d11sq, mcnstart_keeps_chsh_d11sq, mload_iter_keeps_chsh_d11sq. apply mchdr_keeps_chsh_d11sq. Qed.
Lemma morph_fsm_keeps_chsh_A_pos : forall n c, hw_chsh_A_pos (morph_fsm_final n c) = hw_chsh_A_pos c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_chsh_A_pos, nouter_iter_keeps_chsh_A_pos, mcnstart_keeps_chsh_A_pos, mload_iter_keeps_chsh_A_pos. apply mchdr_keeps_chsh_A_pos. Qed.
Lemma morph_fsm_keeps_chsh_A_neg_a : forall n c, hw_chsh_A_neg_a (morph_fsm_final n c) = hw_chsh_A_neg_a c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_chsh_A_neg_a, nouter_iter_keeps_chsh_A_neg_a, mcnstart_keeps_chsh_A_neg_a, mload_iter_keeps_chsh_A_neg_a. apply mchdr_keeps_chsh_A_neg_a. Qed.
Lemma morph_fsm_keeps_chsh_A_neg_b : forall n c, hw_chsh_A_neg_b (morph_fsm_final n c) = hw_chsh_A_neg_b c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_chsh_A_neg_b, nouter_iter_keeps_chsh_A_neg_b, mcnstart_keeps_chsh_A_neg_b, mload_iter_keeps_chsh_A_neg_b. apply mchdr_keeps_chsh_A_neg_b. Qed.
Lemma morph_fsm_keeps_chsh_B_pos : forall n c, hw_chsh_B_pos (morph_fsm_final n c) = hw_chsh_B_pos c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_chsh_B_pos, nouter_iter_keeps_chsh_B_pos, mcnstart_keeps_chsh_B_pos, mload_iter_keeps_chsh_B_pos. apply mchdr_keeps_chsh_B_pos. Qed.
Lemma morph_fsm_keeps_chsh_B_neg_a : forall n c, hw_chsh_B_neg_a (morph_fsm_final n c) = hw_chsh_B_neg_a c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_chsh_B_neg_a, nouter_iter_keeps_chsh_B_neg_a, mcnstart_keeps_chsh_B_neg_a, mload_iter_keeps_chsh_B_neg_a. apply mchdr_keeps_chsh_B_neg_a. Qed.
Lemma morph_fsm_keeps_chsh_B_neg_b : forall n c, hw_chsh_B_neg_b (morph_fsm_final n c) = hw_chsh_B_neg_b c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_chsh_B_neg_b, nouter_iter_keeps_chsh_B_neg_b, mcnstart_keeps_chsh_B_neg_b, mload_iter_keeps_chsh_B_neg_b. apply mchdr_keeps_chsh_B_neg_b. Qed.
Lemma morph_fsm_keeps_chsh_d00d01 : forall n c, hw_chsh_d00d01 (morph_fsm_final n c) = hw_chsh_d00d01 c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_chsh_d00d01, nouter_iter_keeps_chsh_d00d01, mcnstart_keeps_chsh_d00d01, mload_iter_keeps_chsh_d00d01. apply mchdr_keeps_chsh_d00d01. Qed.
Lemma morph_fsm_keeps_chsh_n10n11 : forall n c, hw_chsh_n10n11 (morph_fsm_final n c) = hw_chsh_n10n11 c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_chsh_n10n11, nouter_iter_keeps_chsh_n10n11, mcnstart_keeps_chsh_n10n11, mload_iter_keeps_chsh_n10n11. apply mchdr_keeps_chsh_n10n11. Qed.
Lemma morph_fsm_keeps_chsh_d10d11 : forall n c, hw_chsh_d10d11 (morph_fsm_final n c) = hw_chsh_d10d11 c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_chsh_d10d11, nouter_iter_keeps_chsh_d10d11, mcnstart_keeps_chsh_d10d11, mload_iter_keeps_chsh_d10d11. apply mchdr_keeps_chsh_d10d11. Qed.
Lemma morph_fsm_keeps_chsh_n00n01 : forall n c, hw_chsh_n00n01 (morph_fsm_final n c) = hw_chsh_n00n01 c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_chsh_n00n01, nouter_iter_keeps_chsh_n00n01, mcnstart_keeps_chsh_n00n01, mload_iter_keeps_chsh_n00n01. apply mchdr_keeps_chsh_n00n01. Qed.
Lemma morph_fsm_keeps_chsh_abs_C1 : forall n c, hw_chsh_abs_C1 (morph_fsm_final n c) = hw_chsh_abs_C1 c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_chsh_abs_C1, nouter_iter_keeps_chsh_abs_C1, mcnstart_keeps_chsh_abs_C1, mload_iter_keeps_chsh_abs_C1. apply mchdr_keeps_chsh_abs_C1. Qed.
Lemma morph_fsm_keeps_chsh_abs_C2 : forall n c, hw_chsh_abs_C2 (morph_fsm_final n c) = hw_chsh_abs_C2 c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_chsh_abs_C2, nouter_iter_keeps_chsh_abs_C2, mcnstart_keeps_chsh_abs_C2, mload_iter_keeps_chsh_abs_C2. apply mchdr_keeps_chsh_abs_C2. Qed.
Lemma morph_fsm_keeps_chsh_C_sq : forall n c, hw_chsh_C_sq (morph_fsm_final n c) = hw_chsh_C_sq c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_chsh_C_sq, nouter_iter_keeps_chsh_C_sq, mcnstart_keeps_chsh_C_sq, mload_iter_keeps_chsh_C_sq. apply mchdr_keeps_chsh_C_sq. Qed.
Lemma morph_fsm_keeps_chsh_A_times_B : forall n c, hw_chsh_A_times_B (morph_fsm_final n c) = hw_chsh_A_times_B c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_chsh_A_times_B, nouter_iter_keeps_chsh_A_times_B, mcnstart_keeps_chsh_A_times_B, mload_iter_keeps_chsh_A_times_B. apply mchdr_keeps_chsh_A_times_B. Qed.
Lemma morph_fsm_keeps_chsh_check_result : forall n c, hw_chsh_check_result (morph_fsm_final n c) = hw_chsh_check_result c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_chsh_check_result, nouter_iter_keeps_chsh_check_result, mcnstart_keeps_chsh_check_result, mload_iter_keeps_chsh_check_result. apply mchdr_keeps_chsh_check_result. Qed.
Lemma morph_fsm_keeps_bus_load_instr_addr : forall n c, hw_bus_load_instr_addr (morph_fsm_final n c) = hw_bus_load_instr_addr c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_bus_load_instr_addr, nouter_iter_keeps_bus_load_instr_addr, mcnstart_keeps_bus_load_instr_addr, mload_iter_keeps_bus_load_instr_addr. apply mchdr_keeps_bus_load_instr_addr. Qed.
Lemma morph_fsm_keeps_bus_load_instr_data : forall n c, hw_bus_load_instr_data (morph_fsm_final n c) = hw_bus_load_instr_data c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_bus_load_instr_data, nouter_iter_keeps_bus_load_instr_data, mcnstart_keeps_bus_load_instr_data, mload_iter_keeps_bus_load_instr_data. apply mchdr_keeps_bus_load_instr_data. Qed.
Lemma morph_fsm_keeps_bus_load_instr_kick : forall n c, hw_bus_load_instr_kick (morph_fsm_final n c) = hw_bus_load_instr_kick c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_bus_load_instr_kick, nouter_iter_keeps_bus_load_instr_kick, mcnstart_keeps_bus_load_instr_kick, mload_iter_keeps_bus_load_instr_kick. apply mchdr_keeps_bus_load_instr_kick. Qed.
Lemma morph_fsm_keeps_mu_tensor : forall n c, hw_mu_tensor (morph_fsm_final n c) = hw_mu_tensor c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_mu_tensor, nouter_iter_keeps_mu_tensor, mcnstart_keeps_mu_tensor, mload_iter_keeps_mu_tensor. apply mchdr_keeps_mu_tensor. Qed.
Lemma morph_fsm_keeps_module_tensors : forall n c, hw_module_tensors (morph_fsm_final n c) = hw_module_tensors c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_module_tensors, nouter_iter_keeps_module_tensors, mcnstart_keeps_module_tensors, mload_iter_keeps_module_tensors. apply mchdr_keeps_module_tensors. Qed.
Lemma morph_fsm_keeps_csr_status : forall n c, hw_csr_status (morph_fsm_final n c) = hw_csr_status c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_csr_status, nouter_iter_keeps_csr_status, mcnstart_keeps_csr_status, mload_iter_keeps_csr_status. apply mchdr_keeps_csr_status. Qed.
Lemma morph_fsm_keeps_csr_heap_base : forall n c, hw_csr_heap_base (morph_fsm_final n c) = hw_csr_heap_base c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_csr_heap_base, nouter_iter_keeps_csr_heap_base, mcnstart_keeps_csr_heap_base, mload_iter_keeps_csr_heap_base. apply mchdr_keeps_csr_heap_base. Qed.
Lemma morph_fsm_keeps_ptTable : forall n c, hw_ptTable (morph_fsm_final n c) = hw_ptTable c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_ptTable, nouter_iter_keeps_ptTable, mcnstart_keeps_ptTable, mload_iter_keeps_ptTable. apply mchdr_keeps_ptTable. Qed.
Lemma morph_fsm_keeps_pt_next_id : forall n c, hw_pt_next_id (morph_fsm_final n c) = hw_pt_next_id c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_pt_next_id, nouter_iter_keeps_pt_next_id, mcnstart_keeps_pt_next_id, mload_iter_keeps_pt_next_id. apply mchdr_keeps_pt_next_id. Qed.
Lemma morph_fsm_keeps_morph_src_table : forall n c, hw_morph_src_table (morph_fsm_final n c) = hw_morph_src_table c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_morph_src_table, nouter_iter_keeps_morph_src_table, mcnstart_keeps_morph_src_table, mload_iter_keeps_morph_src_table. apply mchdr_keeps_morph_src_table. Qed.
Lemma morph_fsm_keeps_morph_dst_table : forall n c, hw_morph_dst_table (morph_fsm_final n c) = hw_morph_dst_table c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_morph_dst_table, nouter_iter_keeps_morph_dst_table, mcnstart_keeps_morph_dst_table, mload_iter_keeps_morph_dst_table. apply mchdr_keeps_morph_dst_table. Qed.
Lemma morph_fsm_keeps_morph_coupling_desc_table : forall n c, hw_morph_coupling_desc_table (morph_fsm_final n c) = hw_morph_coupling_desc_table c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_morph_coupling_desc_table, nouter_iter_keeps_morph_coupling_desc_table, mcnstart_keeps_morph_coupling_desc_table, mload_iter_keeps_morph_coupling_desc_table. apply mchdr_keeps_morph_coupling_desc_table. Qed.
Lemma morph_fsm_keeps_morph_valid_table : forall n c, hw_morph_valid_table (morph_fsm_final n c) = hw_morph_valid_table c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_morph_valid_table, nouter_iter_keeps_morph_valid_table, mcnstart_keeps_morph_valid_table, mload_iter_keeps_morph_valid_table. apply mchdr_keeps_morph_valid_table. Qed.
Lemma morph_fsm_keeps_morph_identity_table : forall n c, hw_morph_identity_table (morph_fsm_final n c) = hw_morph_identity_table c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_morph_identity_table, nouter_iter_keeps_morph_identity_table, mcnstart_keeps_morph_identity_table, mload_iter_keeps_morph_identity_table. apply mchdr_keeps_morph_identity_table. Qed.
Lemma morph_fsm_keeps_morph_next_id : forall n c, hw_morph_next_id (morph_fsm_final n c) = hw_morph_next_id c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_morph_next_id, nouter_iter_keeps_morph_next_id, mcnstart_keeps_morph_next_id, mload_iter_keeps_morph_next_id. apply mchdr_keeps_morph_next_id. Qed.
Lemma morph_fsm_keeps_coupling_desc_label_table : forall n c, hw_coupling_desc_label_table (morph_fsm_final n c) = hw_coupling_desc_label_table c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_coupling_desc_label_table, nouter_iter_keeps_coupling_desc_label_table, mcnstart_keeps_coupling_desc_label_table, mload_iter_keeps_coupling_desc_label_table. apply mchdr_keeps_coupling_desc_label_table. Qed.
Lemma morph_fsm_keeps_coupling_desc_label_len_table : forall n c, hw_coupling_desc_label_len_table (morph_fsm_final n c) = hw_coupling_desc_label_len_table c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_coupling_desc_label_len_table, nouter_iter_keeps_coupling_desc_label_len_table, mcnstart_keeps_coupling_desc_label_len_table, mload_iter_keeps_coupling_desc_label_len_table. apply mchdr_keeps_coupling_desc_label_len_table. Qed.
Lemma morph_fsm_keeps_mc_op : forall n c, hw_mc_op (morph_fsm_final n c) = hw_mc_op c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_mc_op, nouter_iter_keeps_mc_op, mcnstart_keeps_mc_op, mload_iter_keeps_mc_op. apply mchdr_keeps_mc_op. Qed.
Lemma morph_fsm_keeps_mc_mem_base : forall n c, hw_mc_mem_base (morph_fsm_final n c) = hw_mc_mem_base c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_mc_mem_base, nouter_iter_keeps_mc_mem_base, mcnstart_keeps_mc_mem_base, mload_iter_keeps_mc_mem_base. apply mchdr_keeps_mc_mem_base. Qed.
Lemma morph_fsm_keeps_mc_src1_base : forall n c, hw_mc_src1_base (morph_fsm_final n c) = hw_mc_src1_base c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_mc_src1_base, nouter_iter_keeps_mc_src1_base, mcnstart_keeps_mc_src1_base, mload_iter_keeps_mc_src1_base. apply mchdr_keeps_mc_src1_base. Qed.
Lemma morph_fsm_keeps_mc_src1_count : forall n c, hw_mc_src1_count (morph_fsm_final n c) = hw_mc_src1_count c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_mc_src1_count, nouter_iter_keeps_mc_src1_count, mcnstart_keeps_mc_src1_count, mload_iter_keeps_mc_src1_count. apply mchdr_keeps_mc_src1_count. Qed.
Lemma morph_fsm_keeps_mc_src2_base : forall n c, hw_mc_src2_base (morph_fsm_final n c) = hw_mc_src2_base c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_mc_src2_base, nouter_iter_keeps_mc_src2_base, mcnstart_keeps_mc_src2_base, mload_iter_keeps_mc_src2_base. apply mchdr_keeps_mc_src2_base. Qed.
Lemma morph_fsm_keeps_mc_src2_count : forall n c, hw_mc_src2_count (morph_fsm_final n c) = hw_mc_src2_count c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_mc_src2_count, nouter_iter_keeps_mc_src2_count, mcnstart_keeps_mc_src2_count, mload_iter_keeps_mc_src2_count. apply mchdr_keeps_mc_src2_count. Qed.
Lemma morph_fsm_keeps_mc_is_id1 : forall n c, hw_mc_is_id1 (morph_fsm_final n c) = hw_mc_is_id1 c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_mc_is_id1, nouter_iter_keeps_mc_is_id1, mcnstart_keeps_mc_is_id1, mload_iter_keeps_mc_is_id1. apply mchdr_keeps_mc_is_id1. Qed.
Lemma morph_fsm_keeps_mc_is_id2 : forall n c, hw_mc_is_id2 (morph_fsm_final n c) = hw_mc_is_id2 c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_mc_is_id2, nouter_iter_keeps_mc_is_id2, mcnstart_keeps_mc_is_id2, mload_iter_keeps_mc_is_id2. apply mchdr_keeps_mc_is_id2. Qed.
Lemma morph_fsm_keeps_mc_write_base : forall n c, hw_mc_write_base (morph_fsm_final n c) = hw_mc_write_base c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_mc_write_base, nouter_iter_keeps_mc_write_base, mcnstart_keeps_mc_write_base, mload_iter_keeps_mc_write_base. apply mchdr_keeps_mc_write_base. Qed.
Lemma morph_fsm_keeps_mc_dst_reg : forall n c, hw_mc_dst_reg (morph_fsm_final n c) = hw_mc_dst_reg c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_mc_dst_reg, nouter_iter_keeps_mc_dst_reg, mcnstart_keeps_mc_dst_reg, mload_iter_keeps_mc_dst_reg. apply mchdr_keeps_mc_dst_reg. Qed.
Lemma morph_fsm_keeps_mc_morph_slot : forall n c, hw_mc_morph_slot (morph_fsm_final n c) = hw_mc_morph_slot c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_mc_morph_slot, nouter_iter_keeps_mc_morph_slot, mcnstart_keeps_mc_morph_slot, mload_iter_keeps_mc_morph_slot. apply mchdr_keeps_mc_morph_slot. Qed.
Lemma morph_fsm_keeps_mc_new_src_mod : forall n c, hw_mc_new_src_mod (morph_fsm_final n c) = hw_mc_new_src_mod c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_mc_new_src_mod, nouter_iter_keeps_mc_new_src_mod, mcnstart_keeps_mc_new_src_mod, mload_iter_keeps_mc_new_src_mod. apply mchdr_keeps_mc_new_src_mod. Qed.
Lemma morph_fsm_keeps_mc_new_dst_mod : forall n c, hw_mc_new_dst_mod (morph_fsm_final n c) = hw_mc_new_dst_mod c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_mc_new_dst_mod, nouter_iter_keeps_mc_new_dst_mod, mcnstart_keeps_mc_new_dst_mod, mload_iter_keeps_mc_new_dst_mod. apply mchdr_keeps_mc_new_dst_mod. Qed.
Lemma morph_fsm_keeps_mc_cost : forall n c, hw_mc_cost (morph_fsm_final n c) = hw_mc_cost c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_mc_cost, nouter_iter_keeps_mc_cost, mcnstart_keeps_mc_cost, mload_iter_keeps_mc_cost. apply mchdr_keeps_mc_cost. Qed.
Lemma morph_fsm_keeps_formula_desc_base_table : forall n c, hw_formula_desc_base_table (morph_fsm_final n c) = hw_formula_desc_base_table c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_formula_desc_base_table, nouter_iter_keeps_formula_desc_base_table, mcnstart_keeps_formula_desc_base_table, mload_iter_keeps_formula_desc_base_table. apply mchdr_keeps_formula_desc_base_table. Qed.
Lemma morph_fsm_keeps_formula_desc_count_table : forall n c, hw_formula_desc_count_table (morph_fsm_final n c) = hw_formula_desc_count_table c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_formula_desc_count_table, nouter_iter_keeps_formula_desc_count_table, mcnstart_keeps_formula_desc_count_table, mload_iter_keeps_formula_desc_count_table. apply mchdr_keeps_formula_desc_count_table. Qed.
Lemma morph_fsm_keeps_formula_desc_valid_table : forall n c, hw_formula_desc_valid_table (morph_fsm_final n c) = hw_formula_desc_valid_table c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_formula_desc_valid_table, nouter_iter_keeps_formula_desc_valid_table, mcnstart_keeps_formula_desc_valid_table, mload_iter_keeps_formula_desc_valid_table. apply mchdr_keeps_formula_desc_valid_table. Qed.
Lemma morph_fsm_keeps_formula_desc_next_id : forall n c, hw_formula_desc_next_id (morph_fsm_final n c) = hw_formula_desc_next_id c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_formula_desc_next_id, nouter_iter_keeps_formula_desc_next_id, mcnstart_keeps_formula_desc_next_id, mload_iter_keeps_formula_desc_next_id. apply mchdr_keeps_formula_desc_next_id. Qed.
Lemma morph_fsm_keeps_cert_desc_base_table : forall n c, hw_cert_desc_base_table (morph_fsm_final n c) = hw_cert_desc_base_table c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_cert_desc_base_table, nouter_iter_keeps_cert_desc_base_table, mcnstart_keeps_cert_desc_base_table, mload_iter_keeps_cert_desc_base_table. apply mchdr_keeps_cert_desc_base_table. Qed.
Lemma morph_fsm_keeps_cert_desc_count_table : forall n c, hw_cert_desc_count_table (morph_fsm_final n c) = hw_cert_desc_count_table c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_cert_desc_count_table, nouter_iter_keeps_cert_desc_count_table, mcnstart_keeps_cert_desc_count_table, mload_iter_keeps_cert_desc_count_table. apply mchdr_keeps_cert_desc_count_table. Qed.
Lemma morph_fsm_keeps_cert_desc_valid_table : forall n c, hw_cert_desc_valid_table (morph_fsm_final n c) = hw_cert_desc_valid_table c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_cert_desc_valid_table, nouter_iter_keeps_cert_desc_valid_table, mcnstart_keeps_cert_desc_valid_table, mload_iter_keeps_cert_desc_valid_table. apply mchdr_keeps_cert_desc_valid_table. Qed.
Lemma morph_fsm_keeps_cert_desc_next_id : forall n c, hw_cert_desc_next_id (morph_fsm_final n c) = hw_cert_desc_next_id c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_cert_desc_next_id, nouter_iter_keeps_cert_desc_next_id, mcnstart_keeps_cert_desc_next_id, mload_iter_keeps_cert_desc_next_id. apply mchdr_keeps_cert_desc_next_id. Qed.
Lemma morph_fsm_keeps_desc_meta_subtype_table : forall n c, hw_desc_meta_subtype_table (morph_fsm_final n c) = hw_desc_meta_subtype_table c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_desc_meta_subtype_table, nouter_iter_keeps_desc_meta_subtype_table, mcnstart_keeps_desc_meta_subtype_table, mload_iter_keeps_desc_meta_subtype_table. apply mchdr_keeps_desc_meta_subtype_table. Qed.
Lemma morph_fsm_keeps_desc_meta_kind_table : forall n c, hw_desc_meta_kind_table (morph_fsm_final n c) = hw_desc_meta_kind_table c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_desc_meta_kind_table, nouter_iter_keeps_desc_meta_kind_table, mcnstart_keeps_desc_meta_kind_table, mload_iter_keeps_desc_meta_kind_table. apply mchdr_keeps_desc_meta_kind_table. Qed.
Lemma morph_fsm_keeps_desc_meta_inline_len_table : forall n c, hw_desc_meta_inline_len_table (morph_fsm_final n c) = hw_desc_meta_inline_len_table c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_desc_meta_inline_len_table, nouter_iter_keeps_desc_meta_inline_len_table, mcnstart_keeps_desc_meta_inline_len_table, mload_iter_keeps_desc_meta_inline_len_table. apply mchdr_keeps_desc_meta_inline_len_table. Qed.
Lemma morph_fsm_keeps_desc_meta_aux_table : forall n c, hw_desc_meta_aux_table (morph_fsm_final n c) = hw_desc_meta_aux_table c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_desc_meta_aux_table, nouter_iter_keeps_desc_meta_aux_table, mcnstart_keeps_desc_meta_aux_table, mload_iter_keeps_desc_meta_aux_table. apply mchdr_keeps_desc_meta_aux_table. Qed.
Lemma morph_fsm_keeps_desc_meta_valid_table : forall n c, hw_desc_meta_valid_table (morph_fsm_final n c) = hw_desc_meta_valid_table c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_desc_meta_valid_table, nouter_iter_keeps_desc_meta_valid_table, mcnstart_keeps_desc_meta_valid_table, mload_iter_keeps_desc_meta_valid_table. apply mchdr_keeps_desc_meta_valid_table. Qed.
Lemma morph_fsm_keeps_desc_meta_next_id : forall n c, hw_desc_meta_next_id (morph_fsm_final n c) = hw_desc_meta_next_id c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_desc_meta_next_id, nouter_iter_keeps_desc_meta_next_id, mcnstart_keeps_desc_meta_next_id, mload_iter_keeps_desc_meta_next_id. apply mchdr_keeps_desc_meta_next_id. Qed.
Lemma morph_fsm_keeps_wc_same_00 : forall n c, hw_wc_same_00 (morph_fsm_final n c) = hw_wc_same_00 c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_wc_same_00, nouter_iter_keeps_wc_same_00, mcnstart_keeps_wc_same_00, mload_iter_keeps_wc_same_00. apply mchdr_keeps_wc_same_00. Qed.
Lemma morph_fsm_keeps_wc_diff_00 : forall n c, hw_wc_diff_00 (morph_fsm_final n c) = hw_wc_diff_00 c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_wc_diff_00, nouter_iter_keeps_wc_diff_00, mcnstart_keeps_wc_diff_00, mload_iter_keeps_wc_diff_00. apply mchdr_keeps_wc_diff_00. Qed.
Lemma morph_fsm_keeps_wc_same_01 : forall n c, hw_wc_same_01 (morph_fsm_final n c) = hw_wc_same_01 c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_wc_same_01, nouter_iter_keeps_wc_same_01, mcnstart_keeps_wc_same_01, mload_iter_keeps_wc_same_01. apply mchdr_keeps_wc_same_01. Qed.
Lemma morph_fsm_keeps_wc_diff_01 : forall n c, hw_wc_diff_01 (morph_fsm_final n c) = hw_wc_diff_01 c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_wc_diff_01, nouter_iter_keeps_wc_diff_01, mcnstart_keeps_wc_diff_01, mload_iter_keeps_wc_diff_01. apply mchdr_keeps_wc_diff_01. Qed.
Lemma morph_fsm_keeps_wc_same_10 : forall n c, hw_wc_same_10 (morph_fsm_final n c) = hw_wc_same_10 c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_wc_same_10, nouter_iter_keeps_wc_same_10, mcnstart_keeps_wc_same_10, mload_iter_keeps_wc_same_10. apply mchdr_keeps_wc_same_10. Qed.
Lemma morph_fsm_keeps_wc_diff_10 : forall n c, hw_wc_diff_10 (morph_fsm_final n c) = hw_wc_diff_10 c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_wc_diff_10, nouter_iter_keeps_wc_diff_10, mcnstart_keeps_wc_diff_10, mload_iter_keeps_wc_diff_10. apply mchdr_keeps_wc_diff_10. Qed.
Lemma morph_fsm_keeps_wc_same_11 : forall n c, hw_wc_same_11 (morph_fsm_final n c) = hw_wc_same_11 c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_wc_same_11, nouter_iter_keeps_wc_same_11, mcnstart_keeps_wc_same_11, mload_iter_keeps_wc_same_11. apply mchdr_keeps_wc_same_11. Qed.
Lemma morph_fsm_keeps_wc_diff_11 : forall n c, hw_wc_diff_11 (morph_fsm_final n c) = hw_wc_diff_11 c.
Proof. intros n c. unfold morph_fsm_final. rewrite mccommit_keeps_wc_diff_11, nouter_iter_keeps_wc_diff_11, mcnstart_keeps_wc_diff_11, mload_iter_keeps_wc_diff_11. apply mchdr_keeps_wc_diff_11. Qed.
