(** LassertWord.v: the LASSERT scan rule over natural numbers. Word-level
    facts about the literal, its sign and magnitude and the assignment reads;
    one firing of [lscan_next] in each of the four cases of [hw_scan]; and
    [lscan_loop], a terminating [hw_scan] run is an iteration of the rule
    ending at phase 0 with the matching commit. *)
Require Import Kami.Kami Kami.Semantics Kami.Lib.NatLib.
From Coq Require Import String Arith Lia Bool.
From KamiHW Require Import ThieleTypes ThieleCPUCore HWBoundary RuleNext FsmDecoded ChshArith LassertSpec
  StepWordFacts StepRefineCommon.
Local Open Scope nat_scope.

(** * Word facts *)

Lemma wordToNat_neg : forall sz (w : word sz),
  wordToNat w <> 0 -> wordToNat (wminus (natToWord sz 0) w) = pow2 sz - wordToNat w.
Proof.
  intros sz w Hw.
  assert (E : wplus (wminus (natToWord sz 0) w) w = natToWord sz 0).
  { rewrite wminus_def, wplus_unit, wplus_comm. apply wminus_inv. }
  apply (f_equal (@wordToNat sz)) in E.
  rewrite wordToNat_wplus in E.
  pose proof (wordToNat_bound (wminus (natToWord sz 0) w)) as B1.
  pose proof (wordToNat_bound w) as B2.
  assert (Z : wordToNat (natToWord sz 0) = 0) by (apply wordToNat_natToWord_idempotent'; apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia).
  rewrite Z in E.
  apply Nat.mod_divide in E; [|apply Nat.pow_nonzero; lia].
  destruct E as [q Eq].
  assert (q = 1) by (destruct q as [|[|q]]; nia).
  subst q. lia.
Qed.


Lemma wordToNat_trunc7_mod : forall w : word WordSz, wordToNat (split1 7 25 w) = wordToNat w mod 128.
Proof. intro w. exact (wordToNat_split1 7 25 w). Qed.

Lemma mod_2_32_mod_128 : forall x, (x mod pow2 32) mod 128 = x mod 128.
Proof.
  intro x. change 128 with (pow2 7). replace (pow2 32) with (pow2 7 * pow2 25) by (rewrite <- Nat.pow_add_r; reflexivity).
  rewrite Nat.mod_mul_r by (apply Nat.pow_nonzero; lia).
  rewrite Nat.mul_comm, Nat.mod_add by (apply Nat.pow_nonzero; lia). apply Nat.mod_mod. apply Nat.pow_nonzero; lia.
Qed.

(** The memory word at a 7-bit address given as a natural number. *)
Definition mem_at (b : HWB) (a : nat) : nat := wordToNat (hw_mem b (natToWord 7 (a mod 128))).

Lemma read_mem_trunc7 : forall b (w : word WordSz),
  wordToNat (hw_mem b (split1 7 25 w)) = mem_at b (wordToNat w).
Proof.
  intros b w. unfold mem_at. f_equal. f_equal.
  apply wordToNat_inj. rewrite wordToNat_trunc7_mod, wordToNat_natToWord_idempotent'.
  - reflexivity.
  - change (pow2 7) with 128. apply Nat.mod_upper_bound. discriminate.
Qed.

(** * The scan rule over natural numbers *)

Lemma sign_bit_eq : forall w : word WordSz,
  (if weq (split2 31 1 (split1 (31 + 1) 0 w)) WO~1 then true else false) = lit_neg (wordToNat w).
Proof.
  intro w. change (hw_eqb (split2 31 1 (split1 (31 + 1) 0 w)) WO~1 = lit_neg (wordToNat w)).
  rewrite hw_eqb_nat, wordToNat_split2, (wordToNat_split1 (31 + 1) 0). change (wordToNat WO~1) with 1.
  assert (Hb : wordToNat w < pow2 32) by apply wordToNat_bound.
  rewrite (Nat.mod_small (wordToNat w)) by exact Hb.
  unfold lit_neg. replace (pow2 32) with (2 * pow2 31) in Hb by (rewrite <- Nat.pow_succ_r'; reflexivity).
  destruct (Nat.leb_spec (pow2 31) (wordToNat w)) as [H|H].
  - apply Nat.eqb_eq. symmetry. apply Nat.div_unique with (r := wordToNat w - pow2 31); lia.
  - apply Nat.eqb_neq. rewrite Nat.div_small by exact H. lia.
Qed.

Lemma wordToNat_wplus_mod_128 : forall (x y : word WordSz),
  (wordToNat (wplus x y)) mod 128 = (wordToNat x + wordToNat y) mod 128.
Proof. intros x y. rewrite wordToNat_wplus. apply mod_2_32_mod_128. Qed.

Lemma mem_at_mod : forall b a, mem_at b (a mod 128) = mem_at b a.
Proof. intros b a. unfold mem_at. rewrite Nat.mod_mod by discriminate. reflexivity. Qed.

Lemma weq_bool_nat : forall n (a b : type (Bit n)),
  (if isEq (Bit n) a b then true else false) = Nat.eqb (wordToNat a) (wordToNat b).
Proof. exact hw_eqb_nat. Qed.

Lemma read_mem_trunc : forall b (w : word WordSz),
  wordToNat (hw_mem b (split1 MemAddrSz 25 w)) = mem_at b (wordToNat w).
Proof. exact read_mem_trunc7. Qed.

Lemma wordToNat_zero32 : @wordToNat WordSz (natToWord WordSz 0) = 0.
Proof. reflexivity. Qed.

Section Scan.
Variable c : HWB.

Definition lw : nat := wordToNat (lscan_literal c).
Definition gm (var : nat) : nat := mem_at c (wordToNat (hw_lassert_cbase c) + var).
Definition gc (var : nat) : nat :=
  mem_at c (wordToNat (hw_lassert_cbase c) + wordToNat (hw_lassert_nvars c) + var).

Lemma lscan_literal_mem : lw = mem_at c (wordToNat (hw_lassert_fptr c)).
Proof. unfold lw, lscan_literal, lscan_fptr_a. cbn [evalExpr]. unfold read_mem. cbn [evalExpr]. apply read_mem_trunc7. Qed.

Lemma lscan_is_zero : lscan_lit_is_zero c = Nat.eqb lw 0.
Proof. unfold lscan_lit_is_zero, lw. cbn [evalExpr evalConstT]. unfold isEq. exact (hw_eqb_nat _ _ _). Qed.

Lemma lw_bound : lw < pow2 32.
Proof. apply wordToNat_bound. Qed.


End Scan.
Section ScanValues.
Variable c : HWB.

Lemma lscan_neg : lscan_lit_is_neg c = andb (lit_neg (lw c)) (negb (Nat.eqb (lw c) 0)).
Proof.
  unfold lscan_lit_is_neg. cbn [evalExpr evalBinBool evalUniBool evalConstT evalUniBit]. unfold isEq.
  unfold lscan_lit_sign. cbn [evalExpr evalUniBit]. rewrite sign_bit_eq, lscan_is_zero. reflexivity.
Qed.

Lemma lscan_abs : lw c <> 0 -> wordToNat (lscan_lit_abs c) = lit_var (lw c).
Proof.
  intro Hz. unfold lscan_lit_abs. cbn [evalExpr evalBinBit evalConstT]. rewrite lscan_neg.
  rewrite (proj2 (Nat.eqb_neq _ _) Hz). unfold lit_var. cbn [negb]. rewrite andb_true_r.
  destruct (lit_neg (lw c)); [|reflexivity].
  exact (wordToNat_neg _ _ Hz).
Qed.

Lemma lscan_asgn : lw c <> 0 -> lscan_asgn_t c = negb (Nat.eqb (gm c (lit_var (lw c))) 0).
Proof.
  intro Hz. unfold lscan_asgn_t, lscan_asgn_word, lscan_caddr. cbn [evalExpr evalUniBool evalConstT evalUniBit evalBinBit].
  unfold read_mem. cbn [evalExpr].
  rewrite weq_bool_nat, ?read_mem_trunc, ?read_mem_trunc7, ?wordToNat_zero32.
  unfold gm. rewrite <- (mem_at_mod c (wordToNat (wplus (hw_lassert_cbase c) (lscan_lit_abs c)))), wordToNat_wplus_mod_128, mem_at_mod, lscan_abs by exact Hz.
  reflexivity.
Qed.

Lemma lscan_counter_asgn : lw c <> 0 -> lscan_counter_asgn_t c = negb (Nat.eqb (gc c (lit_var (lw c))) 0).
Proof.
  intro Hz. unfold lscan_counter_asgn_t, lscan_counter_asgn_word, lscan_counter_caddr.
  cbn [evalExpr evalUniBool evalConstT evalUniBit evalBinBit].
  unfold read_mem. cbn [evalExpr].
  rewrite weq_bool_nat, ?read_mem_trunc, ?read_mem_trunc7, ?wordToNat_zero32.
  unfold gc. rewrite <- (mem_at_mod c (wordToNat (wplus (wplus (hw_lassert_cbase c) (hw_lassert_nvars c)) (lscan_lit_abs c)))), wordToNat_wplus_mod_128.
  rewrite Nat.Div0.add_mod, wordToNat_wplus_mod_128, <- Nat.Div0.add_mod, mem_at_mod, lscan_abs by (exact Hz || discriminate).
  reflexivity.
Qed.

Lemma lscan_sat : lw c <> 0 -> lscan_lit_sat c = hw_lsat (gm c) (lw c).
Proof.
  intro Hz. unfold lscan_lit_sat. cbn [evalExpr evalBinBool evalUniBool].
  rewrite lscan_is_zero, lscan_neg, lscan_asgn by exact Hz. rewrite (proj2 (Nat.eqb_neq _ _) Hz).
  unfold hw_lsat. cbn [negb andb]. rewrite andb_true_r. destruct (lit_neg (lw c)); rewrite ?negb_involutive; reflexivity.
Qed.

Lemma lscan_counter_sat : lw c <> 0 -> lscan_counter_lit_sat c = hw_lsat (gc c) (lw c).
Proof.
  intro Hz. unfold lscan_counter_lit_sat. cbn [evalExpr evalBinBool evalUniBool].
  rewrite lscan_is_zero, lscan_neg, lscan_counter_asgn by exact Hz. rewrite (proj2 (Nat.eqb_neq _ _) Hz).
  unfold hw_lsat. cbn [negb andb]. rewrite andb_true_r. destruct (lit_neg (lw c)); rewrite ?negb_involutive; reflexivity.
Qed.

Lemma lscan_last : lscan_last_clause c = negb (Nat.ltb 1 (wordToNat (hw_lassert_clen c))).
Proof.
  unfold lscan_last_clause. cbn [evalExpr evalConstT evalUniBool evalBinBitBool].
  exact (f_equal negb (hw_ltb_nat _ (natToWord 32 1) (hw_lassert_clen c))).
Qed.
End ScanValues.

(** * One firing of the scan rule, by case *)

Ltac scan_unfold :=
  unfold lscan_next_phase, lscan_next_clen, lscan_next_fptr, lscan_next_clause_sat,
    lscan_next_counter_clause_sat, lscan_next_counter_seen_fail, lscan_new_pc, lscan_new_mu,
    lscan_new_err, lscan_new_error_code_fsm, lscan_all_done, lscan_clause_fail,
    lscan_model_clause_fail, lscan_final_counter_fail, lscan_clause_ok_cont,
    lscan_counter_seen_fail_next, lscan_counter_clause_fail, lscan_end_of_clause;
  cbn [evalExpr evalBinBool evalUniBool evalConstT].

Section Steps.
Variable c : HWB.
Let sat := hw_lassert_clause_sat c.
Let csat := hw_lassert_counter_clause_sat c.
Let seen := hw_lassert_counter_seen_fail c.

Lemma lscan_step_literal : lw c <> 0 ->
  hw_lassert_phase (lscan_next c) = WO~0~1~0 /\
  hw_lassert_fptr (lscan_next c) = wplus (hw_lassert_fptr c) (natToWord WordSz 1) /\
  hw_lassert_clen (lscan_next c) = hw_lassert_clen c /\
  hw_lassert_clause_sat (lscan_next c) = orb sat (hw_lsat (gm c) (lw c)) /\
  hw_lassert_counter_clause_sat (lscan_next c) = orb csat (hw_lsat (gc c) (lw c)) /\
  hw_lassert_counter_seen_fail (lscan_next c) = seen /\
  hw_pc (lscan_next c) = hw_pc c /\ hw_mu (lscan_next c) = hw_mu c /\
  hw_err (lscan_next c) = hw_err c /\ hw_error_code (lscan_next c) = hw_error_code c.
Proof.
  intro Hz. unfold lscan_next. cbn [hw_lassert_phase hw_lassert_fptr hw_lassert_clen hw_lassert_clause_sat
    hw_lassert_counter_clause_sat hw_lassert_counter_seen_fail hw_pc hw_mu hw_err hw_error_code evalExpr].
  scan_unfold.
  rewrite lscan_is_zero, lscan_sat, lscan_counter_sat by exact Hz.
  rewrite (proj2 (Nat.eqb_neq _ _) Hz). cbn [andb orb negb].
  subst sat csat seen.
  destruct (hw_lsat (gm c) (lw c)), (hw_lsat (gc c) (lw c));
    rewrite ?orb_true_r, ?orb_false_r; repeat split; reflexivity.
Qed.

Lemma lscan_step_unsat : lw c = 0 -> sat = false ->
  hw_lassert_phase (lscan_next c) = WO~0~0~0 /\
  hw_pc (lscan_next c) = hw_trap_vector c /\ hw_mu (lscan_next c) = lscan_mu_fail c /\
  hw_err (lscan_next c) = true /\ hw_error_code (lscan_next c) = ERR_LOGIC_VAL.
Proof.
  intros Hz Hs. unfold lscan_next. cbn [hw_lassert_phase hw_pc hw_mu hw_err hw_error_code evalExpr].
  scan_unfold. rewrite lscan_is_zero, Hz. subst sat. rewrite Hs. cbn [andb orb negb Nat.eqb].
  repeat split; reflexivity.
Qed.

Lemma lscan_step_last : lw c = 0 -> sat = true -> Nat.ltb 1 (wordToNat (hw_lassert_clen c)) = false ->
  let ok := orb seen (negb csat) in
  hw_lassert_phase (lscan_next c) = WO~0~0~0 /\
  hw_pc (lscan_next c) = (if ok then wplus (hw_pc c) (natToWord WordSz 1) else hw_trap_vector c) /\
  hw_mu (lscan_next c) = lscan_mu_success c /\
  hw_err (lscan_next c) = (if ok then hw_err c else true) /\
  hw_error_code (lscan_next c) = (if ok then hw_error_code c else ERR_LOGIC_VAL).
Proof.
  intros Hz Hs Hl ok. unfold lscan_next. cbn [hw_lassert_phase hw_pc hw_mu hw_err hw_error_code evalExpr].
  scan_unfold. rewrite lscan_is_zero, lscan_last, Hz, Hl. subst ok sat csat seen. rewrite Hs.
  cbn [andb orb negb Nat.eqb].
  destruct (hw_lassert_counter_seen_fail c), (hw_lassert_counter_clause_sat c); cbn [andb orb negb];
    repeat split; reflexivity.
Qed.

Lemma lscan_step_next_clause : lw c = 0 -> sat = true -> Nat.ltb 1 (wordToNat (hw_lassert_clen c)) = true ->
  hw_lassert_phase (lscan_next c) = WO~0~1~0 /\
  hw_lassert_fptr (lscan_next c) = wplus (hw_lassert_fptr c) (natToWord WordSz 1) /\
  hw_lassert_clen (lscan_next c) = wminus (hw_lassert_clen c) (natToWord WordSz 1) /\
  hw_lassert_clause_sat (lscan_next c) = false /\
  hw_lassert_counter_clause_sat (lscan_next c) = false /\
  hw_lassert_counter_seen_fail (lscan_next c) = orb seen (negb csat) /\
  hw_pc (lscan_next c) = hw_pc c /\ hw_mu (lscan_next c) = hw_mu c /\
  hw_err (lscan_next c) = hw_err c /\ hw_error_code (lscan_next c) = hw_error_code c.
Proof.
  intros Hz Hs Hl. unfold lscan_next. cbn [hw_lassert_phase hw_lassert_fptr hw_lassert_clen hw_lassert_clause_sat
    hw_lassert_counter_clause_sat hw_lassert_counter_seen_fail hw_pc hw_mu hw_err hw_error_code evalExpr].
  scan_unfold. rewrite lscan_is_zero, lscan_last, Hz, Hl. subst sat csat seen. rewrite Hs.
  cbn [andb orb negb Nat.eqb].
  destruct (hw_lassert_counter_seen_fail c), (hw_lassert_counter_clause_sat c); cbn [andb orb negb];
    repeat split; reflexivity.
Qed.
End Steps.

(** * The scan loop *)

Fixpoint lscan_iter (n : nat) (c : HWB) : HWB :=
  match n with
  | O => c
  | S m => lscan_iter m (lscan_next c)
  end.

Lemma lscan_iter_keeps_halted : forall n c, hw_halted (lscan_iter n c) = hw_halted c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_regs : forall n c, hw_regs (lscan_iter n c) = hw_regs c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_mem : forall n c, hw_mem (lscan_iter n c) = hw_mem c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_imem : forall n c, hw_imem (lscan_iter n c) = hw_imem c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_partition_ops : forall n c, hw_partition_ops (lscan_iter n c) = hw_partition_ops c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_mdl_ops : forall n c, hw_mdl_ops (lscan_iter n c) = hw_mdl_ops c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_info_gain : forall n c, hw_info_gain (lscan_iter n c) = hw_info_gain c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_logic_acc : forall n c, hw_logic_acc (lscan_iter n c) = hw_logic_acc c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_cert_addr : forall n c, hw_cert_addr (lscan_iter n c) = hw_cert_addr c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_active_module : forall n c, hw_active_module (lscan_iter n c) = hw_active_module c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_mstatus : forall n c, hw_mstatus (lscan_iter n c) = hw_mstatus c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_mcycle_lo : forall n c, hw_mcycle_lo (lscan_iter n c) = hw_mcycle_lo c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_mcycle_hi : forall n c, hw_mcycle_hi (lscan_iter n c) = hw_mcycle_hi c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_minstret_lo : forall n c, hw_minstret_lo (lscan_iter n c) = hw_minstret_lo c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_minstret_hi : forall n c, hw_minstret_hi (lscan_iter n c) = hw_minstret_hi c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_trap_vector : forall n c, hw_trap_vector (lscan_iter n c) = hw_trap_vector c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_certified : forall n c, hw_certified (lscan_iter n c) = hw_certified c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_lassert_kind : forall n c, hw_lassert_kind (lscan_iter n c) = hw_lassert_kind c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_lassert_fbase : forall n c, hw_lassert_fbase (lscan_iter n c) = hw_lassert_fbase c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_lassert_cbase : forall n c, hw_lassert_cbase (lscan_iter n c) = hw_lassert_cbase c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_lassert_flen : forall n c, hw_lassert_flen (lscan_iter n c) = hw_lassert_flen c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_lassert_nvars : forall n c, hw_lassert_nvars (lscan_iter n c) = hw_lassert_nvars c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_lassert_cptr : forall n c, hw_lassert_cptr (lscan_iter n c) = hw_lassert_cptr c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_lassert_fbuf : forall n c, hw_lassert_fbuf (lscan_iter n c) = hw_lassert_fbuf c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_lassert_cbuf : forall n c, hw_lassert_cbuf (lscan_iter n c) = hw_lassert_cbuf c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_chsh_phase : forall n c, hw_chsh_phase (lscan_iter n c) = hw_chsh_phase c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_chsh_n00 : forall n c, hw_chsh_n00 (lscan_iter n c) = hw_chsh_n00 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_chsh_n01 : forall n c, hw_chsh_n01 (lscan_iter n c) = hw_chsh_n01 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_chsh_n10 : forall n c, hw_chsh_n10 (lscan_iter n c) = hw_chsh_n10 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_chsh_n11 : forall n c, hw_chsh_n11 (lscan_iter n c) = hw_chsh_n11 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_chsh_d00 : forall n c, hw_chsh_d00 (lscan_iter n c) = hw_chsh_d00 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_chsh_d01 : forall n c, hw_chsh_d01 (lscan_iter n c) = hw_chsh_d01 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_chsh_d10 : forall n c, hw_chsh_d10 (lscan_iter n c) = hw_chsh_d10 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_chsh_d11 : forall n c, hw_chsh_d11 (lscan_iter n c) = hw_chsh_d11 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_chsh_sign00 : forall n c, hw_chsh_sign00 (lscan_iter n c) = hw_chsh_sign00 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_chsh_sign01 : forall n c, hw_chsh_sign01 (lscan_iter n c) = hw_chsh_sign01 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_chsh_sign10 : forall n c, hw_chsh_sign10 (lscan_iter n c) = hw_chsh_sign10 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_chsh_sign11 : forall n c, hw_chsh_sign11 (lscan_iter n c) = hw_chsh_sign11 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_chsh_n00sq : forall n c, hw_chsh_n00sq (lscan_iter n c) = hw_chsh_n00sq c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_chsh_n01sq : forall n c, hw_chsh_n01sq (lscan_iter n c) = hw_chsh_n01sq c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_chsh_n10sq : forall n c, hw_chsh_n10sq (lscan_iter n c) = hw_chsh_n10sq c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_chsh_n11sq : forall n c, hw_chsh_n11sq (lscan_iter n c) = hw_chsh_n11sq c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_chsh_d00sq : forall n c, hw_chsh_d00sq (lscan_iter n c) = hw_chsh_d00sq c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_chsh_d01sq : forall n c, hw_chsh_d01sq (lscan_iter n c) = hw_chsh_d01sq c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_chsh_d10sq : forall n c, hw_chsh_d10sq (lscan_iter n c) = hw_chsh_d10sq c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_chsh_d11sq : forall n c, hw_chsh_d11sq (lscan_iter n c) = hw_chsh_d11sq c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_chsh_A_pos : forall n c, hw_chsh_A_pos (lscan_iter n c) = hw_chsh_A_pos c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_chsh_A_neg_a : forall n c, hw_chsh_A_neg_a (lscan_iter n c) = hw_chsh_A_neg_a c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_chsh_A_neg_b : forall n c, hw_chsh_A_neg_b (lscan_iter n c) = hw_chsh_A_neg_b c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_chsh_B_pos : forall n c, hw_chsh_B_pos (lscan_iter n c) = hw_chsh_B_pos c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_chsh_B_neg_a : forall n c, hw_chsh_B_neg_a (lscan_iter n c) = hw_chsh_B_neg_a c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_chsh_B_neg_b : forall n c, hw_chsh_B_neg_b (lscan_iter n c) = hw_chsh_B_neg_b c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_chsh_d00d01 : forall n c, hw_chsh_d00d01 (lscan_iter n c) = hw_chsh_d00d01 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_chsh_n10n11 : forall n c, hw_chsh_n10n11 (lscan_iter n c) = hw_chsh_n10n11 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_chsh_d10d11 : forall n c, hw_chsh_d10d11 (lscan_iter n c) = hw_chsh_d10d11 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_chsh_n00n01 : forall n c, hw_chsh_n00n01 (lscan_iter n c) = hw_chsh_n00n01 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_chsh_abs_C1 : forall n c, hw_chsh_abs_C1 (lscan_iter n c) = hw_chsh_abs_C1 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_chsh_abs_C2 : forall n c, hw_chsh_abs_C2 (lscan_iter n c) = hw_chsh_abs_C2 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_chsh_C_sq : forall n c, hw_chsh_C_sq (lscan_iter n c) = hw_chsh_C_sq c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_chsh_A_times_B : forall n c, hw_chsh_A_times_B (lscan_iter n c) = hw_chsh_A_times_B c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_chsh_check_result : forall n c, hw_chsh_check_result (lscan_iter n c) = hw_chsh_check_result c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_bus_load_instr_addr : forall n c, hw_bus_load_instr_addr (lscan_iter n c) = hw_bus_load_instr_addr c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_bus_load_instr_data : forall n c, hw_bus_load_instr_data (lscan_iter n c) = hw_bus_load_instr_data c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_bus_load_instr_kick : forall n c, hw_bus_load_instr_kick (lscan_iter n c) = hw_bus_load_instr_kick c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_mu_tensor : forall n c, hw_mu_tensor (lscan_iter n c) = hw_mu_tensor c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_module_tensors : forall n c, hw_module_tensors (lscan_iter n c) = hw_module_tensors c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_csr_status : forall n c, hw_csr_status (lscan_iter n c) = hw_csr_status c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_csr_heap_base : forall n c, hw_csr_heap_base (lscan_iter n c) = hw_csr_heap_base c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_ptTable : forall n c, hw_ptTable (lscan_iter n c) = hw_ptTable c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_pt_next_id : forall n c, hw_pt_next_id (lscan_iter n c) = hw_pt_next_id c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_morph_src_table : forall n c, hw_morph_src_table (lscan_iter n c) = hw_morph_src_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_morph_dst_table : forall n c, hw_morph_dst_table (lscan_iter n c) = hw_morph_dst_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_morph_coupling_desc_table : forall n c, hw_morph_coupling_desc_table (lscan_iter n c) = hw_morph_coupling_desc_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_morph_valid_table : forall n c, hw_morph_valid_table (lscan_iter n c) = hw_morph_valid_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_morph_identity_table : forall n c, hw_morph_identity_table (lscan_iter n c) = hw_morph_identity_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_morph_next_id : forall n c, hw_morph_next_id (lscan_iter n c) = hw_morph_next_id c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_coupling_desc_base_table : forall n c, hw_coupling_desc_base_table (lscan_iter n c) = hw_coupling_desc_base_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_coupling_desc_count_table : forall n c, hw_coupling_desc_count_table (lscan_iter n c) = hw_coupling_desc_count_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_coupling_desc_valid_table : forall n c, hw_coupling_desc_valid_table (lscan_iter n c) = hw_coupling_desc_valid_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_coupling_desc_label_table : forall n c, hw_coupling_desc_label_table (lscan_iter n c) = hw_coupling_desc_label_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_coupling_desc_label_len_table : forall n c, hw_coupling_desc_label_len_table (lscan_iter n c) = hw_coupling_desc_label_len_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_coupling_desc_next_id : forall n c, hw_coupling_desc_next_id (lscan_iter n c) = hw_coupling_desc_next_id c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_coupling_pair_src_table : forall n c, hw_coupling_pair_src_table (lscan_iter n c) = hw_coupling_pair_src_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_coupling_pair_dst_table : forall n c, hw_coupling_pair_dst_table (lscan_iter n c) = hw_coupling_pair_dst_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_coupling_pair_valid_table : forall n c, hw_coupling_pair_valid_table (lscan_iter n c) = hw_coupling_pair_valid_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_coupling_pair_next_id : forall n c, hw_coupling_pair_next_id (lscan_iter n c) = hw_coupling_pair_next_id c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_mc_phase : forall n c, hw_mc_phase (lscan_iter n c) = hw_mc_phase c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_mc_op : forall n c, hw_mc_op (lscan_iter n c) = hw_mc_op c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_mc_mem_base : forall n c, hw_mc_mem_base (lscan_iter n c) = hw_mc_mem_base c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_mc_pair_count : forall n c, hw_mc_pair_count (lscan_iter n c) = hw_mc_pair_count c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_mc_read_ptr : forall n c, hw_mc_read_ptr (lscan_iter n c) = hw_mc_read_ptr c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_mc_src1_base : forall n c, hw_mc_src1_base (lscan_iter n c) = hw_mc_src1_base c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_mc_src1_count : forall n c, hw_mc_src1_count (lscan_iter n c) = hw_mc_src1_count c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_mc_src2_base : forall n c, hw_mc_src2_base (lscan_iter n c) = hw_mc_src2_base c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_mc_src2_count : forall n c, hw_mc_src2_count (lscan_iter n c) = hw_mc_src2_count c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_mc_i : forall n c, hw_mc_i (lscan_iter n c) = hw_mc_i c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_mc_j : forall n c, hw_mc_j (lscan_iter n c) = hw_mc_j c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_mc_is_id1 : forall n c, hw_mc_is_id1 (lscan_iter n c) = hw_mc_is_id1 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_mc_is_id2 : forall n c, hw_mc_is_id2 (lscan_iter n c) = hw_mc_is_id2 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_mc_write_base : forall n c, hw_mc_write_base (lscan_iter n c) = hw_mc_write_base c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_mc_write_ptr : forall n c, hw_mc_write_ptr (lscan_iter n c) = hw_mc_write_ptr c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_mc_norm_ptr : forall n c, hw_mc_norm_ptr (lscan_iter n c) = hw_mc_norm_ptr c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_mc_duplicate : forall n c, hw_mc_duplicate (lscan_iter n c) = hw_mc_duplicate c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_mc_dst_reg : forall n c, hw_mc_dst_reg (lscan_iter n c) = hw_mc_dst_reg c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_mc_morph_slot : forall n c, hw_mc_morph_slot (lscan_iter n c) = hw_mc_morph_slot c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_mc_new_src_mod : forall n c, hw_mc_new_src_mod (lscan_iter n c) = hw_mc_new_src_mod c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_mc_new_dst_mod : forall n c, hw_mc_new_dst_mod (lscan_iter n c) = hw_mc_new_dst_mod c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_mc_cost : forall n c, hw_mc_cost (lscan_iter n c) = hw_mc_cost c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_formula_desc_base_table : forall n c, hw_formula_desc_base_table (lscan_iter n c) = hw_formula_desc_base_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_formula_desc_count_table : forall n c, hw_formula_desc_count_table (lscan_iter n c) = hw_formula_desc_count_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_formula_desc_valid_table : forall n c, hw_formula_desc_valid_table (lscan_iter n c) = hw_formula_desc_valid_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_formula_desc_next_id : forall n c, hw_formula_desc_next_id (lscan_iter n c) = hw_formula_desc_next_id c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_cert_desc_base_table : forall n c, hw_cert_desc_base_table (lscan_iter n c) = hw_cert_desc_base_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_cert_desc_count_table : forall n c, hw_cert_desc_count_table (lscan_iter n c) = hw_cert_desc_count_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_cert_desc_valid_table : forall n c, hw_cert_desc_valid_table (lscan_iter n c) = hw_cert_desc_valid_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_cert_desc_next_id : forall n c, hw_cert_desc_next_id (lscan_iter n c) = hw_cert_desc_next_id c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_desc_meta_subtype_table : forall n c, hw_desc_meta_subtype_table (lscan_iter n c) = hw_desc_meta_subtype_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_desc_meta_kind_table : forall n c, hw_desc_meta_kind_table (lscan_iter n c) = hw_desc_meta_kind_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_desc_meta_inline_len_table : forall n c, hw_desc_meta_inline_len_table (lscan_iter n c) = hw_desc_meta_inline_len_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_desc_meta_aux_table : forall n c, hw_desc_meta_aux_table (lscan_iter n c) = hw_desc_meta_aux_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_desc_meta_valid_table : forall n c, hw_desc_meta_valid_table (lscan_iter n c) = hw_desc_meta_valid_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_desc_meta_next_id : forall n c, hw_desc_meta_next_id (lscan_iter n c) = hw_desc_meta_next_id c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_wc_same_00 : forall n c, hw_wc_same_00 (lscan_iter n c) = hw_wc_same_00 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_wc_diff_00 : forall n c, hw_wc_diff_00 (lscan_iter n c) = hw_wc_diff_00 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_wc_same_01 : forall n c, hw_wc_same_01 (lscan_iter n c) = hw_wc_same_01 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_wc_diff_01 : forall n c, hw_wc_diff_01 (lscan_iter n c) = hw_wc_diff_01 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_wc_same_10 : forall n c, hw_wc_same_10 (lscan_iter n c) = hw_wc_same_10 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_wc_diff_10 : forall n c, hw_wc_diff_10 (lscan_iter n c) = hw_wc_diff_10 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_wc_same_11 : forall n c, hw_wc_same_11 (lscan_iter n c) = hw_wc_same_11 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.
Lemma lscan_iter_keeps_wc_diff_11 : forall n c, hw_wc_diff_11 (lscan_iter n c) = hw_wc_diff_11 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [lscan_iter]; rewrite IH; reflexivity]. Qed.

Lemma lscan_mu_fail_congr : forall c d,
  hw_mu c = hw_mu d -> hw_lassert_flen c = hw_lassert_flen d -> hw_lassert_cptr c = hw_lassert_cptr d ->
  lscan_mu_fail c = lscan_mu_fail d.
Proof.
  intros c d H1 H2 H3. unfold lscan_mu_fail, lscan_flen_x8, lscan_cost_v. cbn [evalExpr]. rewrite H1, H2, H3. reflexivity.
Qed.

Lemma lscan_mu_success_fail : forall c, lscan_mu_success c = lscan_mu_fail c.
Proof. reflexivity. Qed.

Lemma gm_congr : forall c d, hw_mem c = hw_mem d -> hw_lassert_cbase c = hw_lassert_cbase d -> forall v, gm c v = gm d v.
Proof. intros c d H1 H2 v. unfold gm, mem_at. rewrite H1, H2. reflexivity. Qed.

Lemma gc_congr : forall c d, hw_mem c = hw_mem d -> hw_lassert_cbase c = hw_lassert_cbase d ->
  hw_lassert_nvars c = hw_lassert_nvars d -> forall v, gc c v = gc d v.
Proof. intros c d H1 H2 H3 v. unfold gc, mem_at. rewrite H1, H2, H3. reflexivity. Qed.

Theorem lscan_loop : forall ws c r,
  hw_lassert_phase c = WO~0~1~0 ->
  (forall j, j < List.length ws -> mem_at c (wordToNat (hw_lassert_fptr c) + j) = List.nth j ws 0) ->
  wordToNat (hw_lassert_fptr c) + List.length ws < pow2 32 ->
  1 <= wordToNat (hw_lassert_clen c) ->
  hw_scan (gm c) (gc c) ws (wordToNat (hw_lassert_clen c)) (hw_lassert_clause_sat c)
    (hw_lassert_counter_clause_sat c) (hw_lassert_counter_seen_fail c) = Some r ->
  exists n, n <= List.length ws /\ 1 <= n /\
    (forall m, m < n -> hw_lassert_phase (lscan_iter m c) = WO~0~1~0) /\
    hw_lassert_phase (lscan_iter n c) = WO~0~0~0 /\
    hw_pc (lscan_iter n c) = (if r then wplus (hw_pc c) (natToWord WordSz 1) else hw_trap_vector c) /\
    hw_mu (lscan_iter n c) = lscan_mu_fail c /\
    hw_err (lscan_iter n c) = (if r then hw_err c else true) /\
    hw_error_code (lscan_iter n c) = (if r then hw_error_code c else ERR_LOGIC_VAL).
Proof.
  induction ws as [|w ws IH]; intros c r Hp Hw Hf Hc Hs; [discriminate|].
  assert (Lw : lw c = w).
  { rewrite lscan_literal_mem. specialize (Hw 0 ltac:(cbn [List.length]; lia)). rewrite Nat.add_0_r in Hw. exact Hw. }
  cbn [hw_scan] in Hs.
  destruct (Nat.eqb_spec w 0) as [Ez|Ez].
  - rewrite Ez in Lw. rewrite ?Ez in Hs. cbn [Nat.eqb] in Hs. destruct (hw_lassert_clause_sat c) eqn:Es; cbn [negb] in Hs.
    + destruct (Nat.leb_spec (wordToNat (hw_lassert_clen c)) 1) as [Ll|Ll].
      * inversion Hs; subst r.
        assert (Hl : Nat.ltb 1 (wordToNat (hw_lassert_clen c)) = false) by (apply Nat.ltb_ge; lia).
        destruct (lscan_step_last c Lw Es Hl) as [P [Pc [M [E C]]]].
        exists 1. split; [cbn; lia|]. split; [lia|]. split.
        { intros m Hm. assert (m = 0) by lia. subst m. exact Hp. }
        cbn [lscan_iter]. rewrite P, Pc, M, E, C, lscan_mu_success_fail. repeat split; reflexivity.
      * assert (Hl : Nat.ltb 1 (wordToNat (hw_lassert_clen c)) = true) by (apply Nat.ltb_lt; lia).
        destruct (lscan_step_next_clause c Lw Es Hl) as [P [F [Cl [S1 [S2 [S3 [Pc [M [E C]]]]]]]]].
        set (c1 := lscan_next c) in *.
        assert (Wc1 : wordToNat (hw_lassert_clen c1) = wordToNat (hw_lassert_clen c) - 1).
        { rewrite Cl, wordToNat_wminus_le', wordToNat_word1_32; [reflexivity|]. rewrite wordToNat_word1_32. lia. }
        assert (Fc1 : wordToNat (hw_lassert_fptr c1) = S (wordToNat (hw_lassert_fptr c))).
        { rewrite F. apply wordToNat_wplus_one_bounded. cbn [List.length] in Hf.
          change (pow2 WordSz) with (pow2 32). lia. }
        destruct (IH c1 r) as [n [Hn [H1 [Hph [HP [HPc [HM [HE HC]]]]]]]].
        { exact P. }
        { intros j Hj. rewrite Fc1. replace (S (wordToNat (hw_lassert_fptr c)) + j) with (wordToNat (hw_lassert_fptr c) + S j) by lia.
          unfold mem_at. subst c1. change (hw_mem (lscan_next c)) with (hw_mem c).
          exact (Hw (S j) ltac:(cbn [List.length]; lia)). }
        { rewrite Fc1. cbn [List.length] in Hf. lia. }
        { rewrite Wc1. lia. }
        { rewrite Wc1, S1, S2, S3.
          change (gm c1) with (gm c). change (gc c1) with (gc c). exact Hs. }
        exists (S n). split; [cbn [List.length]; lia|]. split; [lia|]. split.
        { intros m Hm. destruct m as [|m]; [exact Hp|]. cbn [lscan_iter]. fold c1. apply Hph. lia. }
        cbn [lscan_iter]. fold c1. rewrite HP, HPc, HM, HE, HC, Pc, E, C.
        rewrite (lscan_mu_fail_congr c1 c M eq_refl eq_refl).
        subst c1. change (hw_trap_vector (lscan_next c)) with (hw_trap_vector c).
        repeat split; reflexivity.
    + inversion Hs; subst r.
      destruct (lscan_step_unsat c Lw Es) as [P [Pc [M [E C]]]].
      exists 1. split; [cbn; lia|]. split; [lia|]. split.
      { intros m Hm. assert (m = 0) by lia. subst m. exact Hp. }
      cbn [lscan_iter]. rewrite P, Pc, M, E, C. repeat split; reflexivity.
  - assert (Nz : lw c <> 0) by (rewrite Lw; exact Ez).
    destruct (lscan_step_literal c Nz) as [P [F [Cl [S1 [S2 [S3 [Pc [M [E C]]]]]]]]].
    set (c1 := lscan_next c) in *.
    assert (Fc1 : wordToNat (hw_lassert_fptr c1) = S (wordToNat (hw_lassert_fptr c))).
    { rewrite F. apply wordToNat_wplus_one_bounded. cbn [List.length] in Hf.
          change (pow2 WordSz) with (pow2 32). lia. }
    destruct (IH c1 r) as [n [Hn [H1 [Hph [HP [HPc [HM [HE HC]]]]]]]].
    { exact P. }
    { intros j Hj. rewrite Fc1. replace (S (wordToNat (hw_lassert_fptr c)) + j) with (wordToNat (hw_lassert_fptr c) + S j) by lia.
      unfold mem_at. subst c1. change (hw_mem (lscan_next c)) with (hw_mem c).
      exact (Hw (S j) ltac:(cbn [List.length]; lia)). }
    { rewrite Fc1. cbn [List.length] in Hf. lia. }
    { rewrite Cl. exact Hc. }
    { rewrite Cl, S1, S2, S3, Lw.
      change (gm c1) with (gm c). change (gc c1) with (gc c). exact Hs. }
    exists (S n). split; [cbn [List.length]; lia|]. split; [lia|]. split.
    { intros m Hm. destruct m as [|m]; [exact Hp|]. cbn [lscan_iter]. fold c1. apply Hph. lia. }
    cbn [lscan_iter]. fold c1. rewrite HP, HPc, HM, HE, HC, Pc, E, C.
    rewrite (lscan_mu_fail_congr c1 c M eq_refl eq_refl).
    subst c1. change (hw_trap_vector (lscan_next c)) with (hw_trap_vector c).
    repeat split; reflexivity.
Qed.
