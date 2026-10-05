Lemma cg_set2_rf : forall (w w' : env nat nat) (f g : nat -> nat) src dst,
  (forall y, w y = f y) ->
  (forall y, w' y = set_env eq_nat_dec (set_env eq_nat_dec w src 0) dst (w src) y) ->
  src <> dst -> g dst = f src -> g src = 0 ->
  (forall y, y <> src -> y <> dst -> g y = f y) ->
  forall y, w' y = g y.
Proof.
  intros w w' f g src dst Hw Hw' Hsd Hd Hs Ho y. rewrite Hw'. unfold set_env.
  destruct (eq_nat_dec dst y) as [<- | H1]; [rewrite Hw; symmetry; exact Hd |].
  destruct (eq_nat_dec src y) as [<- | H2]; [symmetry; exact Hs |].
  rewrite Ho by auto. apply Hw.
Qed.

Ltac cg_set2 He He' :=
  apply (cg_set2_rf _ _ _ _ _ _ He He'); [lia | cg_rf_tac | cg_rf_tac | intros; cg_rf_tac].

(* ================================================================= *)
(* From HEAD to CHK: one driven move.                                  *)
(* ================================================================= *)

Lemma cg_x_move : forall s i vE e aux,
  cg_eqv e (cg_rf (sc s) 0 0 0 0 0 vE 0) -> pm_next M s = Some i ->
  exists e', cg_eqv e' (cg_rf (sc (cstep s i)) 0 0 (ccost i) 0 0 vE 0) /\
    Xp (2, (e, aux)) (cg_CHK, (e', aux)).
Proof.
  intros s i vE e aux He Hn.
  (* NEXT: H := 1 + code of the move *)
  assert (Hv : cg_next_val M s = S (ic i)) by (unfold cg_next_val; rewrite Hn; reflexivity).
  pose proof (cg_next_spec pc s) as Hrel. rewrite Hv in Hrel.
  destruct (proj1 (cg_Pn_spec (sc s ## vec_nil) e (cg_eqv_spare _ _ _ _ _ _ _ _ He)
                     (cg_in1 e 0 (sc s) ltac:(cg_get He))) _ Hrel) as (e1 & He1 & Hc1).
  assert (E1 : cg_eqv e1 (cg_rf (sc s) 0 (S (ic i)) 0 0 0 vE 0)) by (intros y; cg_set He He1).
  assert (H1 : Xc (2, (e, aux)) (2 + length cg_Pn, (e1, aux))).
  { replace (2 + length cg_Pn) with (length cg_Pn + 2) by lia.
    exact (cg_x_block 2 cg_Pn _ _ _ _ aux cg_sc_next Hc1). }
  (* DEC H HALTB *)
  set (e2 := set_env eq_nat_dec e1 2 (ic i)).
  assert (E2 : cg_eqv e2 (cg_rf (sc s) 0 (ic i) 0 0 0 vE 0))
    by (intros y; cg_set E1 (fun y : nat => eq_refl (e2 y))).
  assert (H2 : Xp (2 + length cg_Pn, (e1, aux)) (3 + length cg_Pn, (e2, aux))).
  { replace (3 + length cg_Pn) with (1 + (2 + length cg_Pn)) by lia.
    apply cg_x_decS with (x := 2) (j := cg_HALTB); [exact cg_sc_dech | cg_get E1]. }
  (* H to I *)
  destruct (cg_x_transfert (3 + length cg_Pn) 2 1 e2 aux ltac:(lia) ltac:(lia) ltac:(lia)
              cg_sc_tr1 ltac:(cg_get E2) ltac:(cg_get E2)) as (e3 & He3 & H3).
  assert (E3 : cg_eqv e3 (cg_rf (sc s) (ic i) 0 0 0 0 vE 0)) by (intros y; cg_set2 E2 He3).
  (* STEP: S' := code of the next state *)
  pose proof (cg_step_spec pc s i) as Hrs.
  destruct (proj1 (cg_Ps_spec (sc s ## ic i ## vec_nil) e3 (cg_eqv_spare _ _ _ _ _ _ _ _ E3)
                     (cg_in2 e3 (sc s) (ic i) ltac:(cg_get E3) ltac:(cg_get E3))) _ Hrs)
    as (e4 & He4 & Hc4).
  assert (E4 : cg_eqv e4 (cg_rf (sc s) (ic i) 0 0 (sc (cstep s i)) 0 vE 0))
    by (intros y; cg_set E3 He4).
  assert (H4 : Xc (cg_a_step, (e3, aux)) (cg_a_cost, (e4, aux))).
  { unfold cg_a_cost. replace (cg_a_step + length cg_Ps) with (length cg_Ps + cg_a_step) by lia.
    exact (cg_x_block _ cg_Ps _ _ _ _ aux cg_sc_step Hc4). }
  (* COST: C := cost of the move *)
  pose proof (cg_cost_spec pc i) as Hrc.
  destruct (proj1 (cg_Pc_spec (ic i ## vec_nil) e4 (cg_eqv_spare _ _ _ _ _ _ _ _ E4)
                     (cg_in1 e4 1 (ic i) ltac:(cg_get E4))) _ Hrc) as (e5 & He5 & Hc5).
  assert (E5 : cg_eqv e5 (cg_rf (sc s) (ic i) 0 (ccost i) (sc (cstep s i)) 0 vE 0))
    by (intros y; cg_set E4 He5).
  assert (H5 : Xc (cg_a_cost, (e4, aux)) (cg_a_erI, (e5, aux))).
  { unfold cg_a_erI. replace (cg_a_cost + length cg_Pc) with (length cg_Pc + cg_a_cost) by lia.
    exact (cg_x_block _ cg_Pc _ _ _ _ aux cg_sc_cost Hc5). }
  (* erase I, erase S, S' to S, JMP CHK *)
  destruct (cg_x_erase cg_a_erI 1 e5 aux ltac:(lia) cg_sc_erI ltac:(cg_get E5)) as (e6 & He6 & H6).
  assert (E6 : cg_eqv e6 (cg_rf (sc s) 0 0 (ccost i) (sc (cstep s i)) 0 vE 0))
    by (intros y; cg_set E5 He6).
  destruct (cg_x_erase (cg_a_erI + 2) 0 e6 aux ltac:(lia) cg_sc_erS ltac:(cg_get E6))
    as (e7 & He7 & H7).
  assert (E7 : cg_eqv e7 (cg_rf 0 0 0 (ccost i) (sc (cstep s i)) 0 vE 0))
    by (intros y; cg_set E6 He7).
  destruct (cg_x_transfert (cg_a_erI + 4) 4 0 e7 aux ltac:(lia) ltac:(lia) ltac:(lia)
              cg_sc_tr2 ltac:(cg_get E7) ltac:(cg_get E7)) as (e8 & He8 & H8).
  assert (E8 : cg_eqv e8 (cg_rf (sc (cstep s i)) 0 0 (ccost i) 0 0 vE 0))
    by (intros y; cg_set2 E7 He8).
  assert (H9 : Xp (cg_a_erI + 7, (e8, aux)) (cg_CHK, (e8, aux)))
    by (apply cg_x_dec0 with (x := 8); [exact cg_sc_jmp1 | cg_get E8]).
  exists e8. split; [exact E8 |].
  replace (2 + cg_a_erI) with (cg_a_erI + 2) in H6 by lia.
  replace (2 + (cg_a_erI + 2)) with (cg_a_erI + 4) in H7 by lia.
  replace (3 + (cg_a_erI + 4)) with (cg_a_erI + 7) in H8 by lia.
  replace (3 + (3 + length cg_Pn)) with cg_a_step in H3 by (unfold cg_a_step; lia).
  eapply sss_compute_progress_trans; [exact H1 |].
  eapply sss_progress_trans; [exact H2 |].
  eapply sss_progress_compute_trans; [exact H3 |].
  eapply sss_compute_trans; [exact H4 |].
  eapply sss_compute_progress_trans; [exact H5 |].
  eapply sss_progress_trans; [exact H6 |].
  eapply sss_progress_trans; [exact H7 |].
  eapply sss_progress_trans; [exact H8 | exact H9].
Qed.

(* From HEAD, when the driver halts: to HALTB with the registers kept. *)
Lemma cg_x_halt : forall s vE e aux,
  cg_eqv e (cg_rf (sc s) 0 0 0 0 0 vE 0) -> pm_next M s = None ->
  exists e', cg_eqv e' (cg_rf (sc s) 0 0 0 0 0 vE 0) /\
    Xp (2, (e, aux)) (cg_HALTB, (e', aux)).
Proof.
  intros s vE e aux He Hn.
  assert (Hv : cg_next_val M s = 0) by (unfold cg_next_val; rewrite Hn; reflexivity).
  pose proof (cg_next_spec pc s) as Hrel. rewrite Hv in Hrel.
  destruct (proj1 (cg_Pn_spec (sc s ## vec_nil) e (cg_eqv_spare _ _ _ _ _ _ _ _ He)
                     (cg_in1 e 0 (sc s) ltac:(cg_get He))) _ Hrel) as (e1 & He1 & Hc1).
  assert (E1 : cg_eqv e1 (cg_rf (sc s) 0 0 0 0 0 vE 0)) by (intros y; cg_set He He1).
  exists e1. split; [exact E1 |].
  eapply sss_compute_progress_trans.
  { replace (length cg_Pn + 2) with (2 + length cg_Pn) in Hc1 by lia.
    exact (cg_x_block 2 cg_Pn _ _ _ _ aux cg_sc_next Hc1). }
  apply cg_x_dec0 with (x := 2); [exact cg_sc_dech | cg_get E1].
Qed.

(* ================================================================= *)
(* From CHK: the reading, counted.                                     *)
(* ================================================================= *)

Lemma cg_x_read : forall s c vE e aux,
  cg_eqv e (cg_rf (sc s) 0 0 c 0 0 vE 0) ->
  exists t w1, cg_eqv w1 (cg_rf (sc s) 0 0 c 0 (if rd s then 1 else 0) vE t) /\
    Xp (cg_CHK, (e, aux)) (cg_a_tail, (w1, aux)) /\
    (forall ex, cg_eqv ex (cg_rf (sc s) 0 0 c 0 0 vE t) ->
       cg_ueval (URun cg_r) (cg_gk cg_k ex) = rd s).
Proof.
  intros s c vE e aux He.
  destruct (cg_x_erase cg_CHK cg_T e aux ltac:(generalize cg_T_ge; lia) cg_sc_erT ltac:(cg_get He))
    as (e1 & He1 & H1).
  assert (E1 : cg_eqv e1 (cg_rf (sc s) 0 0 c 0 0 vE 0)) by (intros y; cg_set He He1).
  pose proof (cg_read_spec pc (sc s)) as Hrel. rewrite cg_read_val_code in Hrel.
  destruct (proj1 (cg_Pr_spec (sc s ## vec_nil) e1 (cg_eqv_spare _ _ _ _ _ _ _ _ E1)
                     (cg_in1 e1 0 (sc s) ltac:(cg_get E1))) _ Hrel) as (e2 & He2 & [t Ht]).
  assert (Hout : out_code (length cg_Pr + cg_ig) (cg_ig, cg_Pr))
    by (simpl; unfold code_end; simpl; lia).
  destruct (cg_read_T_spec cg_T cg_Pr cg_ig cg_a_read t e1 _ e2 e1 cg_T_fresh Ht Hout
              ltac:(cg_get E1) (fun _ _ => eq_refl)) as (w1 & [Hc _] & HT & Hw1).
  assert (W1 : cg_eqv w1 (cg_rf (sc s) 0 0 c 0 (if rd s then 1 else 0) vE t)).
  { intros y. destruct (Nat.eq_dec y cg_T) as [-> | Hne].
    - rewrite HT. cg_rf_tac.
    - rewrite (Hw1 y Hne). change (e2 y) with (get_env e2 y). rewrite He2.
      unfold get_env, set_env. destruct (eq_nat_dec 5 y) as [<- | Hne5]; [cg_rf_tac |].
      rewrite E1. cg_rf_tac. }
  exists t, w1. split; [exact W1 |]. split.
  - eapply sss_progress_compute_trans; [exact H1 |].
    replace (2 + cg_CHK) with cg_a_read by (unfold cg_a_read, cg_CHK; lia).
    exact (cg_x_block _ _ _ _ _ _ aux cg_sc_read Hc).
  - intros ex Hex.
    assert (Hz : forall y, cg_k <= y -> ex y = 0) by (exact (cg_eqv_zero_high _ _ _ _ _ _ _ _ _ Hex)).
    cbn [cg_ueval]. unfold cg_r. rewrite cg_rdec_renc. unfold cg_run_check.
    rewrite (cg_expo_gk_zero cg_k ex cg_T Hz).
    replace (ex cg_T) with t by (symmetry; cg_get Hex).
    assert (Hpt : forall x, get_env (cg_env_chk 16 (cg_gk cg_k ex)) x = get_env e1 x).
    { intros x. rewrite (cg_env_chk_gk cg_k ex 16 x Hz). rewrite cg_get_env, E1.
      destruct (Nat.ltb_spec x 16); [rewrite Hex; cg_rf_tac | cg_rf_tac]. }
    destruct (cg_mme_run_ext t (cg_ig, cg_Pr) cg_ig _ _ Hpt) as [Hf Hs].
    rewrite (cg_mme_run_fuel_complete _ _ _ _ Ht Hout t (le_n t)) in Hf, Hs.
    simpl in Hf. rewrite Hf.
    replace (cg_out_codeb (cg_ig, cg_Pr) (length cg_Pr + cg_ig)) with true
      by (symmetry; apply cg_out_codeb_spec; exact Hout).
    rewrite Hs. simpl snd. rewrite He2. unfold get_env, set_env.
    destruct (eq_nat_dec 5 5) as [_ | C]; [| congruence].
    destruct (rd s); reflexivity.
Qed.

(* ================================================================= *)
(* After the reading.                                                  *)
(* ================================================================= *)

Lemma cg_x_noraise : forall vS c vE t w mu ct ea,
  cg_eqv w (cg_rf vS 0 0 c 0 0 vE t) ->
  exists e', cg_eqv e' (cg_rf vS 0 0 0 0 0 vE 0) /\
    Xp (cg_NORAISE, (w, cg_mkaux mu ct ea)) (2, (e', cg_mkaux (mu + c) ct ea)).
Proof.
  intros vS c vE t w mu ct ea Hw.
  destruct (cg_x_erase cg_NORAISE cg_T w (cg_mkaux mu ct ea) ltac:(generalize cg_T_ge; lia)
              cg_sc_erT2 ltac:(cg_get Hw)) as (w1 & Hw1 & H1).
  assert (W1 : cg_eqv w1 (cg_rf vS 0 0 c 0 0 vE 0)) by (intros y; cg_set Hw Hw1).
  destruct (cg_x_payloop c vS vE w1 mu ct ea W1) as (e' & He' & H2).
  exists e'. split; [exact He' |].
  replace (2 + cg_NORAISE) with cg_PL in H1 by (unfold cg_PL, cg_NORAISE; lia).
  eapply sss_progress_trans; [exact H1 | exact H2].
Qed.

(* At the first raise: from the end of the reading to NEW. *)
Lemma cg_x_tail_new : forall vS c t w aux,
  cg_eqv w (cg_rf vS 0 0 c 0 1 0 t) ->
  exists ex, cg_eqv ex (cg_rf vS 0 0 c 0 0 0 t) /\
    Xp (cg_a_tail, (w, aux)) (cg_NEW, (ex, aux)).
Proof.
  intros vS c t w aux Hw.
  set (w1 := set_env eq_nat_dec w 5 0).
  assert (W1 : cg_eqv w1 (cg_rf vS 0 0 c 0 0 0 t))
    by (intros y; cg_set Hw (fun y : nat => eq_refl (w1 y))).
  exists w1. split; [exact W1 |].
  eapply sss_progress_trans.
  { apply cg_x_decS with (x := 5) (j := cg_NORAISE); [exact cg_sc_decB | cg_get Hw]. }
  replace (1 + cg_a_tail) with (cg_a_tail + 1) by lia.
  apply cg_x_dec0 with (x := 7); [exact cg_sc_decE | cg_get W1].
Qed.

Lemma cg_x_tail : forall s c l t w1 mu,
  cg_eqv w1 (cg_rf (sc s) 0 0 c 0 (if rd s then 1 else 0) (if l then 1 else 0) t) ->
  (forall ex, cg_eqv ex (cg_rf (sc s) 0 0 c 0 0 (if l then 1 else 0) t) ->
     cg_ueval (URun cg_r) (cg_gk cg_k ex) = rd s) ->
  exists e', cg_eqv e' (cg_rf (sc s) 0 0 0 0 0 (if l || rd s then 1 else 0) 0) /\
    Xp (cg_a_tail, (w1, cg_mkaux mu l l))
       (2, (e', cg_mkaux (mu + cg_chk_pay l (rd s) c) (l || rd s) (l || rd s))).
Proof.
  intros s c l t w1 mu Hw Hchk. unfold cg_chk_pay.
  destruct (rd s) eqn:Rd; destruct l; cbv beta iota delta [orb andb negb] in *.
  - (* latch up, reading yes *)
    set (w2 := set_env eq_nat_dec w1 5 0).
    assert (W2 : cg_eqv w2 (cg_rf (sc s) 0 0 c 0 0 1 t))
      by (intros y; cg_set Hw (fun y : nat => eq_refl (w2 y))).
    set (w3 := set_env eq_nat_dec w2 7 0).
    assert (W3 : cg_eqv w3 (cg_rf (sc s) 0 0 c 0 0 0 t))
      by (intros y; cg_set W2 (fun y : nat => eq_refl (w3 y))).
    set (w4 := set_env eq_nat_dec w3 7 (S (w3 7))).
    assert (W4 : cg_eqv w4 (cg_rf (sc s) 0 0 c 0 0 1 t)).
    { intros y. assert (E : w3 7 = 0) by (cg_get W3).
      apply (cg_set_rf _ _ _ _ _ _ W3 (fun y : nat => eq_refl (w4 y)));
        [rewrite E; cg_rf_tac | intros; cg_rf_tac]. }
    destruct (cg_x_noraise (sc s) c 1 t w4 mu true true W4) as (e' & He' & Hn).
    exists e'. split; [exact He' |].
    eapply sss_progress_trans.
    { apply cg_x_decS with (x := 5) (j := cg_NORAISE); [exact cg_sc_decB | cg_get Hw]. }
    eapply sss_progress_trans.
    { replace (1 + cg_a_tail) with (cg_a_tail + 1) by lia.
      apply cg_x_decS with (x := 7) (j := cg_NEW); [exact cg_sc_decE | cg_get W2]. }
    eapply sss_progress_trans.
    { replace (1 + (cg_a_tail + 1)) with (cg_a_tail + 2) by lia.
      apply cg_x_inc. exact cg_sc_incE1. }
    eapply sss_progress_trans; [| exact Hn].
    replace (1 + (cg_a_tail + 2)) with (cg_a_tail + 3) by lia.
    apply cg_x_dec0 with (x := 8); [exact cg_sc_jmp2 | cg_get W4].
  - (* first raise *)
    destruct (cg_x_tail_new (sc s) c t w1 (cg_mkaux mu false false) Hw) as (ex & Hex & H1).
    pose proof (Hchk ex Hex) as Hck.
    set (x1 := set_env eq_nat_dec ex 7 (S (ex 7))).
    assert (X1 : cg_eqv x1 (cg_rf (sc s) 0 0 c 0 0 1 t)).
    { intros y. assert (E : ex 7 = 0) by (cg_get Hex).
      apply (cg_set_rf _ _ _ _ _ _ Hex (fun y : nat => eq_refl (x1 y)));
        [rewrite E; cg_rf_tac | intros; cg_rf_tac]. }
    destruct (cg_x_dec_next (cg_NEW + 2) 3 x1 (cg_earn (cg_mkaux mu false false)) ltac:(
                replace (1 + (cg_NEW + 2)) with (cg_NEW + 3) by lia; exact cg_sc_decC1))
      as (x2 & Hx2 & H4).
    assert (X2 : cg_eqv x2 (cg_rf (sc s) 0 0 (c - 1) 0 0 1 t)).
    { intros y. assert (E : x1 3 = c) by (cg_get X1). rewrite E in Hx2. cg_set X1 Hx2. }
    destruct (cg_x_dec_next (cg_NEW + 3) 3 x2 (cg_earn (cg_mkaux mu false false)) ltac:(
                replace (1 + (cg_NEW + 3)) with (cg_NEW + 4) by lia; exact cg_sc_decC2))
      as (x3 & Hx3 & H5).
    assert (X3 : cg_eqv x3 (cg_rf (sc s) 0 0 (c - 1 - 1) 0 0 1 t)).
    { intros y. assert (E : x2 3 = c - 1) by (cg_get X2). rewrite E in Hx3. cg_set X2 Hx3. }
    destruct (cg_x_dec_next (cg_NEW + 4) 3 x3 (cg_earn (cg_mkaux mu false false)) ltac:(
                replace (1 + (cg_NEW + 4)) with (cg_NEW + 5) by lia; exact cg_sc_decC3))
      as (x4 & Hx4 & H6).
    assert (X4 : cg_eqv x4 (cg_rf (sc s) 0 0 (c - 1 - 1 - 1) 0 0 1 t)).
    { intros y. assert (E : x3 3 = c - 1 - 1) by (cg_get X3). rewrite E in Hx4. cg_set X3 Hx4. }
    destruct (cg_x_noraise (sc s) (c - 1 - 1 - 1) 1 t x4 (mu + 3) true true X4)
      as (e' & He' & Hn).
    exists e'. split; [exact He' |].
    eapply sss_progress_trans; [exact H1 |].
    eapply sss_progress_trans.
    { apply cg_x_earn; [exact cg_sc_earn | exact Hck | reflexivity]. }
    eapply sss_progress_trans.
    { replace (S cg_NEW) with (cg_NEW + 1) by lia. apply cg_x_inc. exact cg_sc_incE2. }
    replace (1 + (cg_NEW + 1)) with (cg_NEW + 2) by lia.
    replace (1 + (cg_NEW + 2)) with (cg_NEW + 3) in H4 by lia.
    replace (1 + (cg_NEW + 3)) with (cg_NEW + 4) in H5 by lia.
    replace (1 + (cg_NEW + 4)) with cg_NORAISE in H6 by (unfold cg_NORAISE, cg_NEW; lia).
    eapply sss_progress_trans; [exact H4 |].
    eapply sss_progress_trans; [exact H5 |].
    eapply sss_progress_trans; [exact H6 |].
    replace (mu + (3 + (c - 3))) with (mu + 3 + (c - 1 - 1 - 1)) by lia. exact Hn.
  - (* latch up, reading no *)
    destruct (cg_x_noraise (sc s) c 1 t w1 mu true true Hw) as (e' & He' & Hn).
    exists e'. split; [exact He' |].
    eapply sss_progress_trans; [| exact Hn].
    apply cg_x_dec0 with (x := 5); [exact cg_sc_decB | cg_get Hw].
  - (* latch down, reading no *)
    destruct (cg_x_noraise (sc s) c 0 t w1 mu false false Hw) as (e' & He' & Hn).
    exists e'. split; [exact He' |].
    eapply sss_progress_trans; [| exact Hn].
    apply cg_x_dec0 with (x := 5); [exact cg_sc_decB | cg_get Hw].
Qed.

Lemma cg_x_check : forall s c l mu e,
  cg_eqv e (cg_rf (sc s) 0 0 c 0 0 (if l then 1 else 0) 0) ->
  exists e', cg_eqv e' (cg_rf (sc s) 0 0 0 0 0 (if l || rd s then 1 else 0) 0) /\
    Xp (cg_CHK, (e, cg_mkaux mu l l))
       (2, (e', cg_mkaux (mu + cg_chk_pay l (rd s) c) (l || rd s) (l || rd s))).
Proof.
  intros s c l mu e He.
  destruct (cg_x_read s c _ e (cg_mkaux mu l l) He) as (t & w1 & Hw1 & H1 & Hchk).
  destruct (cg_x_tail s c l t w1 mu Hw1 Hchk) as (e' & He' & H2).
  exists e'. split; [exact He' | eapply sss_progress_trans; [exact H1 | exact H2]].
Qed.

(* From CHK at the first raise, to NEW, where the fixed checker accepts. *)
Lemma cg_x_to_new : forall s c e aux,
  cg_eqv e (cg_rf (sc s) 0 0 c 0 0 0 0) -> rd s = true ->
  exists ex t, cg_eqv ex (cg_rf (sc s) 0 0 c 0 0 0 t) /\
    Xp (cg_CHK, (e, aux)) (cg_NEW, (ex, aux)) /\
    cg_ueval (URun cg_r) (cg_gk cg_k ex) = true.
Proof.
  intros s c e aux He Rd.
  destruct (cg_x_read s c 0 e aux He) as (t & w1 & Hw1 & H1 & Hchk).
  rewrite Rd in Hw1.
  destruct (cg_x_tail_new (sc s) c t w1 aux Hw1) as (ex & Hex & H2).
  exists ex, t. split; [exact Hex |]. split; [eapply sss_progress_trans; [exact H1 | exact H2] |].
  rewrite <- Rd. apply Hchk. exact Hex.
Qed.

