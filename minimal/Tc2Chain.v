(** Tc2Chain.v: the chain of stages along the run of one input, and the
    impossibility of multiplying every input by a number coprime to all
    small numbers.

    Part 1: outputs of runs, the interface of the stage lemma in the two
    orientations (counter B large directly, counter A large through the swap
    of the counters).

    Dependencies: Tc2Am.v, Tc2Forced.v, Tc2Stage.v. No axioms and no unfinished proofs. *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is about abstract two-counter machines with a finite control, the shape
   the two-counter machine of EarnedCore.v takes once its finite part is the
   control (Tc2Embed.v). The machine's link to the abstract record (a
   CertificationSystem with the trace cost floor, and a Thiele-complete
   machine) lives in EarnedCoreLinks.v and ThieleComplete.v. *)


From Coq Require Import List Arith Lia Bool ZArith.
Import ListNotations.
Require Import Minimal.Tc2Am Minimal.Tc2Forced Minimal.Tc2Stage.
Set Default Goal Selector "!".

(* the output of a run: counter A when the machine has stopped *)
Definition ch_outs (M : tc2_am) (k : tc2_cfg M) (y : nat) : Prop :=
  exists n, am_hlt M (am_run M n k) /\ am_a M (am_run M n k) = y.

Lemma ch_outs_unique : forall M k y y', ch_outs M k y -> ch_outs M k y' -> y = y'.
Proof.
  intros M k y y' [n [Hn Hy]] [m [Hm Hy']].
  destruct (Nat.le_ge_cases n m) as [H | H].
  - rewrite (am_run_after M n m k H Hn) in Hy'. rewrite <- Hy, <- Hy'. reflexivity.
  - rewrite (am_run_after M m n k H Hm) in Hy. rewrite <- Hy, <- Hy'. reflexivity.
Qed.

Lemma ch_outs_fwd : forall M T k y, ch_outs M k y -> ch_outs M (am_run M T k) y.
Proof.
  intros M T k y [n [Hn Hy]]. destruct (Nat.le_ge_cases T n) as [H | H].
  - exists (n - T). rewrite <- am_run_add. replace (T + (n - T)) with n by lia. split; assumption.
  - exists 0. simpl. rewrite (am_run_after M n T k H Hn). split; assumption.
Qed.

Lemma ch_outs_bwd : forall M T k y, ch_outs M (am_run M T k) y -> ch_outs M k y.
Proof.
  intros M T k y [n [Hn Hy]]. exists (T + n). rewrite am_run_add. split; assumption.
Qed.

(* a stage ends no later than the machine stops *)
Lemma ch_stage_le : forall M (g : tc2_cfg M -> nat) T n k,
  (forall t, t < T -> am_B M <= g (am_run M t k)) -> g (am_run M T k) < am_B M ->
  am_hlt M (am_run M n k) -> T <= n.
Proof.
  intros M g T n k H1 H2 H3. destruct (le_lt_dec T n) as [H | H]; [exact H |].
  exfalso. rewrite (am_run_after M n T k ltac:(lia) H3) in H2.
  pose proof (H1 n H). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* the stage lemma for both counters                                   *)
(* ------------------------------------------------------------------ *)

Theorem sl_both : forall M, exists th Xl, am_B M <= th /\
  (forall q0 s0 pi, In q0 (am_lq M) -> s0 < am_B M -> pi < 2 ->
     st_any M q0 s0 pi th Xl (length (fs_lA M))) /\
  (forall q0 s0 pi, In q0 (am_lq M) -> s0 < am_B M -> pi < 2 ->
     st_any (am_swp M) q0 s0 pi th Xl (length (fs_lA M))).
Proof.
  intro M.
  destruct (sl_all M) as (th1 & Xl1 & H1). destruct (sl_all (am_swp M)) as (th2 & Xl2 & H2).
  exists (Nat.max (Nat.max th1 th2) (am_B M)), (Nat.max Xl1 Xl2). split; [apply Nat.le_max_r |]. split.
  - intros q0 s0 pi Hq Hs Hp. eapply st_any_mono; [exact (H1 q0 s0 pi Hq Hs Hp) | | apply Nat.le_max_l].
    etransitivity; apply Nat.le_max_l.
  - intros q0 s0 pi Hq Hs Hp. eapply st_any_mono; [exact (H2 q0 s0 pi Hq Hs Hp) | | apply Nat.le_max_r].
    etransitivity; [apply Nat.le_max_r | apply Nat.le_max_l].
Qed.

(* the interface, counter B large *)
Definition if_leaf (N : tc2_am) (k : tc2_cfg N) (Xl : nat) : Prop :=
  exists H qH xH (D : Z), xH <= Xl /\
    forall j, exists y, Z.of_nat y = (Z.of_nat (am_b N k + 2 * j) + D)%Z /\
      am_run N H (am_shB N (2 * j) k) = (qH, xH, y) /\ am_hlt N (qH, xH, y).

Definition if_next (N : tc2_am) (k : tc2_cfg N) (K : nat) : Prop :=
  exists T k' m2 g2, 1 <= T /\ am_run N T k = k' /\ am_b N k' = am_B N - 1 /\ In (am_q N k') (am_lq N) /\
    (forall t, t < T -> am_B N <= am_b N (am_run N t k)) /\
    0 < m2 /\ 2 * m2 <= K /\ 0 < g2 /\ 2 * g2 <= K /\
    forall j, exists Tj, am_run N Tj (am_shB N (2 * m2 * j) k) = am_shA N (2 * g2 * j) k'.

Definition if_bdd (N : tc2_am) (k : tc2_cfg N) (th : nat) : Prop :=
  exists T k', am_run N T k = k' /\ am_b N k' = am_B N - 1 /\ am_a N k' <= th /\ In (am_q N k') (am_lq N) /\
    (forall t, t < T -> am_B N <= am_b N (am_run N t k)).

Definition if_nh (N : tc2_am) (k : tc2_cfg N) : Prop := forall n, ~ am_hlt N (am_run N n k).

Definition iface (N : tc2_am) (k : tc2_cfg N) (th Xl K : nat) : Prop :=
  if_leaf N k Xl \/ if_next N k K \/ if_bdd N k th \/ if_nh N k.

Lemma st_next_iter : forall M q0 s0 pi th p g2 m2,
  (forall v, th <= v -> fs_par v = pi ->
     (exists T q x, st_fp M q0 s0 v T q x) /\
     (forall T q x, st_fp M q0 s0 v T q x -> st_fp M q0 s0 (v + 2 * m2) (T + p) q (x + 2 * g2))) ->
  forall v T q x j, th <= v -> fs_par v = pi -> st_fp M q0 s0 v T q x ->
    st_fp M q0 s0 (v + 2 * m2 * j) (T + p * j) q (x + 2 * g2 * j).
Proof.
  intros M q0 s0 pi th p g2 m2 Hn v T q x j Hv Hpar Hfp.
  induction j as [| j IH].
  - rewrite Nat.mul_0_r, Nat.mul_0_r, Nat.mul_0_r, !Nat.add_0_r. exact Hfp.
  - assert (Hpj : fs_par (v + 2 * m2 * j) = pi).
    { rewrite <- Hpar. replace (v + 2 * m2 * j) with (v + (m2 * j) * 2) by lia.
      unfold fs_par. apply Nat.Div0.mod_add. }
    destruct (Hn (v + 2 * m2 * j) ltac:(lia) Hpj) as [_ H2].
    pose proof (H2 _ _ _ IH) as H3.
    replace (v + 2 * m2 * S j) with (v + 2 * m2 * j + 2 * m2) by lia.
    replace (T + p * S j) with (T + p * j + p) by lia.
    replace (x + 2 * g2 * S j) with (x + 2 * g2 * j + 2 * g2) by lia. exact H3.
Qed.

Lemma iface_of_any : forall N th Xl K,
  am_B N <= th ->
  (forall q0 s0 pi, In q0 (am_lq N) -> s0 < am_B N -> pi < 2 -> st_any N q0 s0 pi th Xl K) ->
  forall k, am_a N k < am_B N -> In (am_q N k) (am_lq N) -> th <= am_b N k -> iface N k th Xl K.
Proof.
  intros N th Xl K HBth Hany [[q s] v] Hs Hq Hv. unfold am_a, am_b, am_q in *. cbn [fst snd] in *.
  assert (Hp2 : fs_par v < 2) by apply fs_par_lt.
  assert (Hpar : forall j, fs_par (v + 2 * j) = fs_par v) by (intro j; apply fs_par_add2).
  destruct (Hany q s (fs_par v) Hq Hs Hp2) as [Hl | [Hn | [Hb | Hh]]].
  - left. destruct Hl as (H & qH & xH & D & Hx & Hall). exists H, qH, xH, D. split; [exact Hx |].
    intro j. unfold am_b. cbn [snd]. destruct (Hall (v + 2 * j) ltac:(lia) (Hpar j)) as (y & Hy & Hrun & Hhlt).
    exists y. split; [exact Hy |]. split; [exact Hrun | exact Hhlt].
  - right; left. destruct Hn as (p & g2 & m2 & Hp & HpK & Hg & Hgp & Hm & Hmp & Hall).
    destruct (Hall v Hv eq_refl) as [(T & q1 & x1 & Hfp) Hsh].
    assert (Hfp' := Hfp). destruct Hfp as [Hrun Hmin].
    assert (HT : 1 <= T).
    { destruct T as [| T']; [| lia]. exfalso. simpl in Hrun. injection Hrun as _ _ Hb. lia. }
    exists T, (q1, x1, am_B N - 1), m2, g2.
    assert (Hq1 : In q1 (am_lq N)).
    { pose proof (am_run_q N T (q, s, v) Hq) as H. rewrite Hrun in H. exact H. }
    refine (conj HT (conj Hrun (conj eq_refl (conj Hq1 (conj Hmin (conj Hm (conj _ (conj Hg (conj _ _)))))))));
      try lia.
    intro j. exists (T + p * j).
    pose proof (st_next_iter N q s (fs_par v) th p g2 m2 Hall v T q1 x1 j Hv eq_refl Hfp') as [Hr _].
    cbn [am_shB am_shA]. exact Hr.
  - right; right; left. destruct (Hb v Hv eq_refl) as (T & q1 & x1 & Hfp & Hx). destruct Hfp as [Hrun Hmin].
    exists T, (q1, x1, am_B N - 1). 
    assert (Hq1 : In q1 (am_lq N)).
    { pose proof (am_run_q N T (q, s, v) Hq) as H. rewrite Hrun in H. exact H. }
    refine (conj Hrun (conj eq_refl (conj Hx (conj Hq1 Hmin)))).
  - right; right; right. intro n. apply (Hh v Hv eq_refl n).
Qed.

Print Assumptions iface_of_any.

(* ------------------------------------------------------------------ *)
(* counter A large: through the swap of the counters                   *)
(* ------------------------------------------------------------------ *)

Lemma am_usw_sw : forall M k, am_usw M (am_sw M k) = k.
Proof. intros M [[q a] b]. reflexivity. Qed.

Lemma am_sw_usw : forall M k, am_sw M (am_usw M k) = k.
Proof. intros M [[q a] b]. reflexivity. Qed.

Lemma am_b_sw : forall M k, am_b (am_swp M) (am_sw M k) = am_a M k.
Proof. intros M [[q a] b]. reflexivity. Qed.
Lemma am_a_sw : forall M k, am_a (am_swp M) (am_sw M k) = am_b M k.
Proof. intros M [[q a] b]. reflexivity. Qed.

Lemma am_swp_shA : forall M d k, am_shA (am_swp M) d (am_sw M k) = am_sw M (am_shB M d k).
Proof. intros M d [[q a] b]. reflexivity. Qed.

Lemma am_swp_shB : forall M d k, am_shB (am_swp M) d (am_sw M k) = am_sw M (am_shA M d k).
Proof. intros M d [[q a] b]. reflexivity. Qed.

Lemma am_shA_0 : forall M k, am_shA M 0 k = k.
Proof. intros M [[q a] b]. cbn [am_shA]. rewrite Nat.add_0_r. reflexivity. Qed.

Lemma am_shB_0 : forall M k, am_shB M 0 k = k.
Proof. intros M [[q a] b]. cbn [am_shB]. rewrite Nat.add_0_r. reflexivity. Qed.

Lemma am_run_usw : forall M n k, am_run M n (am_usw M k) = am_usw M (am_run (am_swp M) n k).
Proof.
  intros M n k. rewrite <- (am_sw_usw M k) at 2. rewrite am_sw_run. rewrite am_usw_sw. reflexivity.
Qed.

Lemma am_sw_inj : forall M (k k' : tc2_cfg M), am_sw M k = am_sw M k' -> k = k'.
Proof. intros M k k' H. rewrite <- (am_usw_sw M k), H, am_usw_sw. reflexivity. Qed.

(* the leaf with counter A large: the output grows with the input *)
Definition ifA_leaf (M : tc2_am) (k : tc2_cfg M) : Prop :=
  exists y, forall j, ch_outs M (am_shA M (2 * j) k) (y + 2 * j).

Definition ifA_next (M : tc2_am) (k : tc2_cfg M) (K : nat) : Prop :=
  exists T k1 m2 g2, 1 <= T /\ am_run M T k = k1 /\ am_a M k1 = am_B M - 1 /\ In (am_q M k1) (am_lq M) /\
    (forall t, t < T -> am_B M <= am_a M (am_run M t k)) /\
    0 < m2 /\ 2 * m2 <= K /\ 0 < g2 /\ 2 * g2 <= K /\
    forall j, exists Tj, am_run M Tj (am_shA M (2 * m2 * j) k) = am_shB M (2 * g2 * j) k1.

Definition ifA_bdd (M : tc2_am) (k : tc2_cfg M) (th : nat) : Prop :=
  exists T k1, am_run M T k = k1 /\ am_a M k1 = am_B M - 1 /\ am_b M k1 <= th /\ In (am_q M k1) (am_lq M) /\
    (forall t, t < T -> am_B M <= am_a M (am_run M t k)).

Definition ifA_nh (M : tc2_am) (k : tc2_cfg M) : Prop := forall n, ~ am_hlt M (am_run M n k).

Lemma iface_A : forall M th Xl K,
  am_B M <= th ->
  (forall q0 s0 pi, In q0 (am_lq M) -> s0 < am_B M -> pi < 2 -> st_any (am_swp M) q0 s0 pi th Xl K) ->
  forall k, am_b M k < am_B M -> In (am_q M k) (am_lq M) -> th <= am_a M k ->
    ifA_leaf M k \/ ifA_next M k K \/ ifA_bdd M k th \/ ifA_nh M k.
Proof.
  intros M th Xl K HB Hany k Hs Hq Hv.
  destruct k as [[q a] b]. unfold am_a, am_b, am_q in *. cbn [fst snd] in *.
  assert (Hs' : am_a (am_swp M) (am_sw M (q, a, b)) < am_B (am_swp M)) by exact Hs.
  assert (Hv' : th <= am_b (am_swp M) (am_sw M (q, a, b))) by exact Hv.
  destruct (iface_of_any (am_swp M) th Xl K HB Hany (am_sw M (q, a, b)) Hs' Hq Hv') as [Hl | [Hn | [Hb | Hh]]].
  - left. destruct Hl as (H & qH & xH & D & Hx & Hall).
    assert (Hy : forall j, exists y, Z.of_nat y = (Z.of_nat (a + 2 * j) + D)%Z /\ ch_outs M (am_shA M (2 * j) (q, a, b)) y).
    { intro j. destruct (Hall j) as (y & Hy & Hrun & Hhlt). exists y. split; [exact Hy |].
      exists H. rewrite am_swp_shB in Hrun. rewrite am_sw_run in Hrun.
      apply (f_equal (am_usw M)) in Hrun. rewrite am_usw_sw in Hrun. rewrite Hrun.
      split; [apply am_sw_hlt; exact Hhlt | reflexivity]. }
    destruct (Hy 0) as (y0 & Hy0 & Ho0).
    exists y0. intro j. destruct (Hy j) as (yj & Hyj & Hoj).
    assert (Hj : yj = y0 + 2 * j) by lia. rewrite <- Hj. exact Hoj.
  - right; left. destruct Hn as (T & k' & m2 & g2 & HT & Hrun & Hb1 & Hq1 & Hmin & Hm & Hmk & Hg & Hgk & Hall).
    exists T, (am_usw M k'), m2, g2.
    assert (Hr : am_run M T (q, a, b) = am_usw M k').
    { rewrite <- Hrun. replace (q, a, b) with (am_usw M (am_sw M (q, a, b))) by (apply am_usw_sw).
      rewrite <- am_run_usw. rewrite am_usw_sw. reflexivity. }
    destruct k' as [[q' a'] b']. unfold am_b, am_a, am_q in Hb1, Hq1. cbn [fst snd] in Hb1, Hq1.
    refine (conj HT (conj Hr (conj _ (conj Hq1 (conj _ (conj Hm (conj Hmk (conj Hg (conj Hgk _)))))))));
      [exact Hb1 | | ].
    + intros t Ht. specialize (Hmin t Ht). rewrite am_sw_run, am_b_sw in Hmin. exact Hmin.
    + intro j. destruct (Hall j) as [Tj HTj]. exists Tj.
      rewrite am_swp_shB in HTj. rewrite am_sw_run in HTj.
      replace (am_shA (am_swp M) (2 * g2 * j) (q', a', b')) with
        (am_sw M (am_shB M (2 * g2 * j) (am_usw M (q', a', b')))) in HTj by reflexivity.
      apply am_sw_inj in HTj. exact HTj.
  - right; right; left. destruct Hb as (T & k' & Hrun & Hb1 & Ha1 & Hq1 & Hmin).
    exists T, (am_usw M k').
    assert (Hr : am_run M T (q, a, b) = am_usw M k').
    { rewrite <- Hrun. replace (q, a, b) with (am_usw M (am_sw M (q, a, b))) by (apply am_usw_sw).
      rewrite <- am_run_usw. rewrite am_usw_sw. reflexivity. }
    destruct k' as [[q' a'] b']. unfold am_b, am_a, am_q in Hb1, Ha1, Hq1. cbn [fst snd] in Hb1, Ha1, Hq1.
    refine (conj Hr (conj Hb1 (conj Ha1 (conj Hq1 _)))).
    intros t Ht. specialize (Hmin t Ht). rewrite am_sw_run, am_b_sw in Hmin. exact Hmin.
  - right; right; right. intro n. intro Hhlt. apply (Hh n).
    rewrite am_sw_run. apply am_sw_hlt. exact Hhlt.
Qed.

Print Assumptions iface_A.

(* ------------------------------------------------------------------ *)
(* the chain                                                           *)
(* ------------------------------------------------------------------ *)

Lemma ifB_leaf_out : forall M Xl k, if_leaf M k Xl -> exists xo, xo <= Xl /\ ch_outs M k xo.
Proof.
  intros M Xl k (H & qH & xH & D & Hx & Hall). destruct (Hall 0) as (y & _ & Hrun & Hhlt).
  rewrite am_shB_0 in Hrun. exists xH. split; [exact Hx |]. exists H. rewrite Hrun. split; [exact Hhlt | reflexivity].
Qed.

Fixpoint ch_prod (l : list nat) : nat := match l with [] => 1 | x :: l' => x * ch_prod l' end.

Definition ch_F (M : tc2_am) (th : nat) (k : tc2_cfg M) : Prop :=
  In (am_q M k) (am_lq M) /\
  ((am_a M k < am_B M /\ am_b M k <= th) \/ (am_b M k < am_B M /\ am_a M k <= th)).

Definition ch_good (M : tc2_am) (th : nat) (k : tc2_cfg M) : Prop := forall t, ~ ch_F M th (am_run M t k).

Definition ch_concl (M : tc2_am) (K : nat) (k : tc2_cfg M) (y0 : nat) : Prop :=
  exists ms ns mD, (forall m, In m ms -> 1 <= m /\ m <= K) /\ (forall n, In n ns -> 1 <= n /\ n <= K) /\ 1 <= mD /\
    forall j, ch_outs M (am_shA M (j * ch_prod ms * mD) k) (y0 + j * ch_prod ns * mD).

Lemma ch_good_run : forall M th T k, ch_good M th k -> ch_good M th (am_run M T k).
Proof. intros M th T k H t. rewrite <- am_run_add. apply H. Qed.

Lemma chain : forall M th Xl K,
  am_B M <= th ->
  (forall q0 s0 pi, In q0 (am_lq M) -> s0 < am_B M -> pi < 2 -> st_any M q0 s0 pi th Xl K) ->
  (forall q0 s0 pi, In q0 (am_lq M) -> s0 < am_B M -> pi < 2 -> st_any (am_swp M) q0 s0 pi th Xl K) ->
  forall n k y0, am_hlt M (am_run M n k) -> ch_outs M k y0 -> Xl < y0 ->
    am_b M k < am_B M -> In (am_q M k) (am_lq M) -> ch_good M th k -> ch_concl M K k y0.
Proof.
  intros M th Xl K HB HanyB HanyA n. induction n as [n IH] using lt_wf_ind.
  intros k y0 Hhlt Hout Hy Hs Hq Hgood.
  assert (Hth : th < am_a M k).
  { destruct (le_lt_dec (am_a M k) th) as [Hle | Hlt]; [| exact Hlt]. exfalso.
    apply (Hgood 0). unfold ch_F. simpl am_run. split; [exact Hq | right; split; assumption]. }
  destruct (iface_A M th Xl K HB HanyA k Hs Hq (Nat.lt_le_incl _ _ Hth)) as [Hl | [Hn | [Hb | Hh]]].
  - destruct Hl as [y Hy']. 
    assert (Hyy : y = y0).
    { pose proof (Hy' 0) as H0. rewrite Nat.mul_0_r, am_shA_0, Nat.add_0_r in H0. exact (ch_outs_unique M k y y0 H0 Hout). }
    subst y. exists [], [], 2. refine (conj _ (conj _ (conj _ _))).
    + intros m Hm. contradiction.
    + intros m Hm. contradiction.
    + lia.
    + intro j. cbn [ch_prod]. replace (j * 1 * 2) with (2 * j) by lia. exact (Hy' j).
  - destruct Hn as (T1 & k1 & m2 & g2 & HT1 & Hrun1 & Ha1 & Hq1 & Hmin1 & Hm & Hmk & Hg & Hgk & Hsh1).
    assert (Hgood1 : ch_good M th k1) by (rewrite <- Hrun1; apply ch_good_run; exact Hgood).
    assert (Hout1 : ch_outs M k1 y0) by (rewrite <- Hrun1; apply ch_outs_fwd; exact Hout).
    assert (HB1 : 1 <= am_B M) by apply am_B1.
    assert (Hn1 : T1 <= n).
    { apply (ch_stage_le M (am_a M) T1 n k Hmin1 ltac:(rewrite Hrun1, Ha1; lia) Hhlt). }
    assert (Hth1 : th < am_b M k1).
    { destruct (le_lt_dec (am_b M k1) th) as [Hle | Hlt]; [| exact Hlt]. exfalso.
      apply (Hgood1 0). unfold ch_F. simpl am_run. split; [exact Hq1 | left; split; [rewrite Ha1; lia | exact Hle]]. }
    assert (Hhlt1 : am_hlt M (am_run M (n - T1) k1)).
    { rewrite <- Hrun1, <- am_run_add. replace (T1 + (n - T1)) with n by lia. exact Hhlt. }
    destruct (iface_of_any M th Xl K HB HanyB k1 ltac:(rewrite Ha1; lia) Hq1 (Nat.lt_le_incl _ _ Hth1))
      as [Hl2 | [Hn2 | [Hb2 | Hh2]]].
    + exfalso. destruct (ifB_leaf_out M Xl k1 Hl2) as (xo & Hxo & Hxout).
      rewrite (ch_outs_unique M k1 y0 xo Hout1 Hxout) in Hy. lia.
    + destruct Hn2 as (T2 & k2 & m2' & g2' & HT2 & Hrun2 & Hb2 & Hq2 & Hmin2 & Hm' & Hmk' & Hg' & Hgk' & Hsh2).
      assert (Hgood2 : ch_good M th k2) by (rewrite <- Hrun2; apply ch_good_run; exact Hgood1).
      assert (Hout2 : ch_outs M k2 y0) by (rewrite <- Hrun2; apply ch_outs_fwd; exact Hout1).
      assert (Hn2' : T2 <= n - T1).
      { apply (ch_stage_le M (am_b M) T2 (n - T1) k1 Hmin2 ltac:(rewrite Hrun2, Hb2; lia) Hhlt1). }
      assert (Hhlt2 : am_hlt M (am_run M (n - T1 - T2) k2)).
      { rewrite <- Hrun2, <- am_run_add. replace (T2 + (n - T1 - T2)) with (n - T1) by lia. exact Hhlt1. }
      destruct (IH (n - T1 - T2) ltac:(lia) k2 y0 Hhlt2 Hout2 Hy ltac:(rewrite Hb2; lia) Hq2 Hgood2)
        as (ms' & ns' & mD' & Hms' & Hns' & HmD' & Hsh').
      exists (2 * m2 :: 2 * m2' :: ms'), (2 * g2 :: 2 * g2' :: ns'), mD'.
      refine (conj _ (conj _ (conj HmD' _))).
      * intros m [<- | [<- | Hin]]; [lia | lia | exact (Hms' m Hin)].
      * intros m [<- | [<- | Hin]]; [lia | lia | exact (Hns' m Hin)].
      * intro j. cbn [ch_prod].
        set (P' := ch_prod ms') in *. set (Q' := ch_prod ns') in *.
        set (J1 := j * (2 * m2' * P') * mD').
        set (J2 := 2 * g2 * j * P' * mD').
        destruct (Hsh1 J1) as [T1j H1j]. destruct (Hsh2 J2) as [T2j H2j].
        assert (Hamt : 2 * g2 * J1 = 2 * m2' * J2) by (unfold J1, J2; ring).
        rewrite Hamt in H1j.
        assert (Hshape : j * (2 * m2 * (2 * m2' * P')) * mD' = 2 * m2 * J1) by (unfold J1; ring).
        assert (Hshape2 : 2 * g2' * J2 = (2 * g2 * (2 * g2' * j)) * P' * mD') by (unfold J2; ring).
        assert (Hval : y0 + j * (2 * g2 * (2 * g2' * Q')) * mD' = y0 + (2 * g2 * (2 * g2' * j)) * Q' * mD') by ring.
        rewrite Hshape, Hval.
        specialize (Hsh' (2 * g2 * (2 * g2' * j))). rewrite <- Hshape2 in Hsh'.
        rewrite <- H2j in Hsh'. apply ch_outs_bwd in Hsh'. rewrite <- H1j in Hsh'. apply ch_outs_bwd in Hsh'.
        exact Hsh'.
    + exfalso. destruct Hb2 as (T2 & k2 & Hrun2 & Hb2 & Ha2 & Hq2 & _).
      apply (Hgood1 T2). unfold ch_F. rewrite Hrun2. split; [exact Hq2 | right; split; [rewrite Hb2; lia | exact Ha2]].
    + exfalso. apply (Hh2 (n - T1)). exact Hhlt1.
  - exfalso. destruct Hb as (T & k1 & Hrun & Ha1 & Hb1 & Hq1 & _).
    apply (Hgood T). unfold ch_F. rewrite Hrun. split; [exact Hq1 | left; split; [rewrite Ha1; pose proof (am_B1 M); lia | exact Hb1]].
  - exfalso. exact (Hh n Hhlt).
Qed.

Print Assumptions chain.

(* ------------------------------------------------------------------ *)
(* good inputs: the run never enters the finite set of small stage starts *)
(* ------------------------------------------------------------------ *)

Definition ch_Flist (M : tc2_am) (th : nat) : list (tc2_cfg M) :=
  list_prod (list_prod (am_lq M) (seq 0 (am_B M))) (seq 0 (S th)) ++
  list_prod (list_prod (am_lq M) (seq 0 (S th))) (seq 0 (am_B M)).

Lemma ch_F_in : forall M th k, ch_F M th k -> In k (ch_Flist M th).
Proof.
  intros M th [[q a] b] [Hq Hd]. unfold am_q, am_a, am_b in *. cbn [fst snd] in *.
  destruct Hd as [[H1 H2] | [H1 H2]].
  - unfold ch_Flist. apply in_or_app. left. apply in_prod_iff. split.
    + apply in_prod_iff. split; [exact Hq | apply in_seq; lia].
    + apply in_seq; lia.
  - unfold ch_Flist. apply in_or_app. right. apply in_prod_iff. split.
    + apply in_prod_iff. split; [exact Hq | apply in_seq; lia].
    + apply in_seq; lia.
Qed.

Lemma ch_F_dec : forall M th k, {ch_F M th k} + {~ ch_F M th k}.
Proof.
  intros M th k. unfold ch_F.
  destruct (in_dec (am_eq M) (am_q M k) (am_lq M)) as [Hq | Hq]; [| right; intros [H _]; exact (Hq H)].
  destruct (lt_dec (am_a M k) (am_B M)) as [Ha | Ha]; destruct (le_dec (am_b M k) th) as [Hb | Hb];
    destruct (lt_dec (am_b M k) (am_B M)) as [Hc | Hc]; destruct (le_dec (am_a M k) th) as [Hd | Hd];
    first [left; split; [exact Hq | first [left; split; assumption | right; split; assumption]] |
           right; intros [_ [[H1 H2] | [H1 H2]]]; contradiction].
Qed.

Section Good.
Variable M : tc2_am.
Variable q0 : am_Q M.
Variable c : nat.
Hypothesis hc : 1 <= c.
Hypothesis htot : forall x, exists n, am_hlt M (am_run M n (q0, x, 0)) /\ am_a M (am_run M n (q0, x, 0)) = c * x.

Lemma ch_outs_start : forall x, ch_outs M (q0, x, 0) (c * x).
Proof. intro x. destruct (htot x) as (n & H1 & H2). exists n. split; assumption. Qed.

Lemma ch_collision : forall x x' n m, am_run M n (q0, x, 0) = am_run M m (q0, x', 0) -> x = x'.
Proof.
  intros x x' n m H.
  pose proof (ch_outs_fwd M n _ _ (ch_outs_start x)) as H1.
  pose proof (ch_outs_fwd M m _ _ (ch_outs_start x')) as H2.
  rewrite H in H1. pose proof (ch_outs_unique M _ _ _ H1 H2) as H3. nia.
Qed.

Lemma good_exists : forall th x0, exists x, x0 <= x /\ ch_good M th (q0, x, 0).
Proof.
  intros th x0.
  set (Fl := ch_Flist M th).
  assert (Claim : forall n, (exists r, r < n /\ ch_good M th (q0, x0 + r, 0)) \/
    (exists l : list (tc2_cfg M), length l = n /\ NoDup l /\ incl l Fl /\
       forall k, In k l -> exists r t, r < n /\ am_run M t (q0, x0 + r, 0) = k)).
  { intro n. induction n as [| n IH].
    - right. exists []. refine (conj eq_refl (conj (NoDup_nil _) (conj (incl_nil_l _) _))). intros k Hk. contradiction.
    - destruct IH as [(r & Hr & Hg) | (l & Hl1 & Hl2 & Hl3 & Hl4)].
      + left. exists r. split; [lia | exact Hg].
      + destruct (htot (x0 + n)) as (H & Hh & _).
        destruct (tc2_bex_dec (fun t => ch_F M th (am_run M t (q0, x0 + n, 0)))
                    (fun t => ch_F_dec M th _) H) as [Hbad | Hok].
        * right. destruct Hbad as (t & _ & Ht). set (cc := am_run M t (q0, x0 + n, 0)) in *.
          assert (Hnot : ~ In cc l).
          { intro Hin. destruct (Hl4 cc Hin) as (r & t' & Hr & Heq).
            pose proof (ch_collision (x0 + r) (x0 + n) t' t Heq) as Hx. lia. }
          exists (cc :: l). repeat split.
          -- simpl. lia.
          -- constructor; assumption.
          -- intros k [<- | Hk]; [apply ch_F_in; exact Ht | apply Hl3; exact Hk].
          -- intros k [<- | Hk]; [exists n, t; split; [lia | reflexivity] |].
             destruct (Hl4 k Hk) as (r & t' & Hr & Heq). exists r, t'. split; [lia | exact Heq].
        * left. exists n. split; [lia |]. intros t Ht.
          destruct (le_lt_dec t H) as [Hle | Hlt]; [exact (Hok t Hle Ht) |].
          rewrite (am_run_after M H t _ ltac:(lia) Hh) in Ht. exact (Hok H (le_n H) Ht). }
  destruct (Claim (S (length Fl))) as [(r & Hr & Hg) | (l & Hl1 & Hl2 & Hl3 & _)].
  - exists (x0 + r). split; [lia | exact Hg].
  - exfalso. pose proof (NoDup_incl_length Hl2 Hl3). lia.
Qed.

End Good.

Lemma coprime_mul : forall c a b, Nat.gcd c a = 1 -> Nat.gcd c b = 1 -> Nat.gcd c (a * b) = 1.
Proof.
  intros c a b Ha Hb.
  set (g := Nat.gcd c (a * b)).
  assert (Hgc : Nat.divide g c) by apply Nat.gcd_divide_l.
  assert (Hgab : Nat.divide g (a * b)) by apply Nat.gcd_divide_r.
  assert (Hga : Nat.gcd g a = 1).
  { apply Nat.divide_1_r. rewrite <- Ha. apply Nat.gcd_greatest.
    - eapply Nat.divide_trans; [apply Nat.gcd_divide_l | exact Hgc].
    - apply Nat.gcd_divide_r. }
  assert (Hgb : Nat.divide g b) by (apply (Nat.gauss g a b Hgab Hga)).
  apply Nat.divide_1_r. rewrite <- Hb. apply Nat.gcd_greatest; assumption.
Qed.

Lemma ch_prod_coprime : forall c K ns,
  (forall k, 1 <= k -> k <= K -> Nat.gcd c k = 1) ->
  (forall n, In n ns -> 1 <= n /\ n <= K) -> Nat.gcd c (ch_prod ns) = 1.
Proof.
  intros c K ns Hc. induction ns as [| n ns IH]; intro Hn.
  - cbn [ch_prod]. apply Nat.divide_1_r. apply Nat.gcd_divide_r.
  - cbn [ch_prod]. apply coprime_mul.
    + destruct (Hn n (or_introl eq_refl)) as [H1 H2]. apply Hc; assumption.
    + apply IH. intros m Hm. apply Hn. right. exact Hm.
Qed.

(* no tame machine multiplies every input by a number coprime to all the small numbers *)
Theorem am_no_multiplier : forall M q0 c,
  In q0 (am_lq M) -> 2 <= c ->
  (forall k, 1 <= k -> k <= length (fs_lA M) -> Nat.gcd c k = 1) ->
  (forall x, exists n, am_hlt M (am_run M n (q0, x, 0)) /\ am_a M (am_run M n (q0, x, 0)) = c * x) ->
  False.
Proof.
  intros M q0 c Hq Hc2 Hcop Htot.
  destruct (sl_both M) as (th & Xl & HB & Hany1 & Hany2).
  destruct (good_exists M q0 c ltac:(lia) Htot th (Xl + 1)) as (x & Hx & Hgood).
  pose proof (am_B1 M) as HB1.
  destruct (Htot x) as (n & Hhlt & Hy).
  assert (Hout : ch_outs M (q0, x, 0) (c * x)) by (exists n; split; assumption).
  assert (Hbig : Xl < c * x) by nia.
  destruct (chain M th Xl (length (fs_lA M)) HB Hany1 Hany2 n (q0, x, 0) (c * x) Hhlt Hout Hbig
              ltac:(cbn; lia) Hq Hgood) as (ms & ns & mD & Hms & Hns & HmD & Hsh).
  specialize (Hsh 1).
  assert (Hshift : am_shA M (1 * ch_prod ms * mD) (q0, x, 0) = (q0, x + 1 * ch_prod ms * mD, 0)) by reflexivity.
  rewrite Hshift in Hsh.
  pose proof (ch_outs_start M q0 c Htot (x + 1 * ch_prod ms * mD)) as Hout2.
  pose proof (ch_outs_unique M _ _ _ Hsh Hout2) as Heq.
  assert (HQ : ch_prod ns = c * ch_prod ms).
  { assert (Hm : mD * ch_prod ns = mD * (c * ch_prod ms)) by nia.
    apply (Nat.mul_cancel_l _ _ mD); [lia | exact Hm]. }
  pose proof (ch_prod_coprime c (length (fs_lA M)) ns Hcop Hns) as Hg1.
  rewrite HQ, Nat.gcd_mul_diag_l in Hg1. lia.
Qed.

Print Assumptions am_no_multiplier.
