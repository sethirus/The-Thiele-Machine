(** Tc2Stage.v: the stage lemma.

    A stage starts in a configuration (q, s, v) of a tame machine in which
    counter A is small (s is below the threshold) and counter B is large. The
    stage ends when counter B first falls below the threshold; at that
    moment counter B equals the threshold minus one, and counter A holds a
    number that is the start of the next stage (with the roles of the two
    counters exchanged).

    The stage lemma says that, for large v, exactly one of four things
    happens, and that in the third and fourth cases the stage is exactly
    affine on residue classes:

      leaf        the machine stops during the stage, in a configuration
                  that is the same for every large v except that counter B
                  is v plus a constant;
      next        counter B reaches the wall; if v grows by m (an even
                  number at most the period bound) the stage takes p more
                  steps and the new counter A grows by g (also even, at most
                  p): the map v -> new counter A is v -> g * (v - r) / m + c
                  on each residue class of v modulo m;
      bounded     counter B reaches the wall with counter A bounded;
      never       the machine never stops from any large v.

    Dependencies: Tc2Am.v, Tc2Forced.v. No axioms and no unfinished proofs.            *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is about abstract two-counter machines with a finite control, the shape
   the two-counter machine of EarnedCore.v takes once its finite part is the
   control (Tc2Embed.v). The machine's link to the abstract record (a
   CertificationSystem with the trace cost floor, and a Thiele-complete
   machine) lives in EarnedCoreLinks.v and ThieleComplete.v. *)


From Coq Require Import List Arith Lia Bool ZArith.
Import ListNotations.
Require Import Minimal.Tc2Am Minimal.Tc2Forced.
Set Default Goal Selector "!".

(* the real run is a forced step as long as B is at or above the threshold *)
Lemma real_none : forall M q x y p, am_nx M q x (fs_yrep M p) = None ->
  am_B M <= y -> fs_par y = p -> p < 2 -> am_nx M q x y = None.
Proof.
  intros M q x y p H HB Hp Hp2.
  pose proof (fs_yrep_ge M p) as Hge. pose proof (fs_yrep_le M p) as Hle.
  pose proof (fs_yrep_mod M p Hp2) as Hm.
  pose proof (fs_par_spec y) as H1. pose proof (fs_par_spec (fs_yrep M p)) as H2.
  assert (Hd : exists d, y = fs_yrep M p + 2 * d).
  { exists (y / 2 - fs_yrep M p / 2). rewrite Hp in H1. rewrite Hm in H2. lia. }
  destruct Hd as [d Hd]. rewrite Hd. rewrite (am_tameB M q x (fs_yrep M p) d Hge). rewrite H. reflexivity.
Qed.

Lemma real_some : forall M q x y p q' x' y', am_nx M q x (fs_yrep M p) = Some (q', x', y') ->
  am_B M <= y -> fs_par y = p -> p < 2 -> am_nx M q x y <> None.
Proof.
  intros M q x y p q' x' y' H HB Hp Hp2 Hc.
  pose proof (fs_yrep_ge M p) as Hge. pose proof (fs_yrep_le M p) as Hle.
  pose proof (fs_yrep_mod M p Hp2) as Hm.
  pose proof (fs_par_spec y) as H1. pose proof (fs_par_spec (fs_yrep M p)) as H2.
  assert (Hd : exists d, y = fs_yrep M p + 2 * d).
  { exists (y / 2 - fs_yrep M p / 2). rewrite Hp in H1. rewrite Hm in H2. lia. }
  destruct Hd as [d Hd]. rewrite Hd in Hc. rewrite (am_tameB M q x (fs_yrep M p) d Hge) in Hc. rewrite H in Hc. discriminate.
Qed.

(* the first passage of counter B below the threshold, from the stage start (q0, s0, v) *)
Definition st_fp (M : tc2_am) (q0 : am_Q M) (s0 v T : nat) (q : am_Q M) (x : nat) : Prop :=
  am_run M T (q0, s0, v) = (q, x, am_B M - 1) /\
  forall t, t < T -> am_B M <= am_b M (am_run M t (q0, s0, v)).

Lemma st_fp_unique : forall M q0 s0 v T T' q x q' x',
  st_fp M q0 s0 v T q x -> st_fp M q0 s0 v T' q' x' -> T = T' /\ q = q' /\ x = x'.
Proof.
  intros M q0 s0 v T T' q x q' x' [H1 H2] [H3 H4].
  assert (HT : T = T').
  { destruct (Nat.lt_trichotomy T T') as [Hlt | [Heq | Hgt]]; [| exact Heq |].
    - exfalso. specialize (H4 T Hlt). rewrite H1 in H4. unfold am_b in H4. cbn [snd] in H4.
      pose proof (am_B1 M). lia.
    - exfalso. specialize (H2 T' Hgt). rewrite H3 in H2. unfold am_b in H2. cbn [snd] in H2.
      pose proof (am_B1 M). lia. }
  subst T'. rewrite H1 in H3. inversion H3. subst. auto.
Qed.

(* what a stage can do, for a type (q0, s0, pi), beyond the thresholds th and Xl *)
Definition st_leaf (M : tc2_am) (q0 : am_Q M) (s0 pi th Xl : nat) : Prop :=
  exists H qH xH (D : Z), xH <= Xl /\
    forall v, th <= v -> fs_par v = pi ->
      exists y, Z.of_nat y = (Z.of_nat v + D)%Z /\ am_run M H (q0, s0, v) = (qH, xH, y) /\ am_hlt M (qH, xH, y).

Definition st_next (M : tc2_am) (q0 : am_Q M) (s0 pi th K : nat) : Prop :=
  exists p g2 m2, 0 < p /\ p <= K /\ 0 < g2 /\ 2 * g2 <= p /\ 0 < m2 /\ 2 * m2 <= p /\
    forall v, th <= v -> fs_par v = pi ->
      (exists T q x, st_fp M q0 s0 v T q x) /\
      (forall T q x, st_fp M q0 s0 v T q x -> st_fp M q0 s0 (v + 2 * m2) (T + p) q (x + 2 * g2)).

Definition st_bdd (M : tc2_am) (q0 : am_Q M) (s0 pi th : nat) : Prop :=
  forall v, th <= v -> fs_par v = pi -> exists T q x, st_fp M q0 s0 v T q x /\ x <= th.

Definition st_nh (M : tc2_am) (q0 : am_Q M) (s0 pi th : nat) : Prop :=
  forall v, th <= v -> fs_par v = pi -> forall n, ~ am_hlt M (am_run M n (q0, s0, v)).

Definition st_any (M : tc2_am) (q0 : am_Q M) (s0 pi th Xl K : nat) : Prop :=
  st_leaf M q0 s0 pi th Xl \/ st_next M q0 s0 pi th K \/ st_bdd M q0 s0 pi th \/ st_nh M q0 s0 pi th.

Lemma st_any_mono : forall M q0 s0 pi th Xl K th' Xl', st_any M q0 s0 pi th Xl K -> th <= th' -> Xl <= Xl' ->
  st_any M q0 s0 pi th' Xl' K.
Proof.
  intros M q0 s0 pi th Xl K th' Xl' [H | [H | [H | H]]] H1 H2; [left | right; left | right; right; left | right; right; right].
  - destruct H as (HH & qH & xH & D & Hx & Hv). exists HH, qH, xH, D. split; [lia |]. intros v Hv' Hp. apply Hv; [lia | exact Hp].
  - destruct H as (p & g2 & m2 & H). exists p, g2, m2. destruct H as (A1 & A2 & A3 & A4 & A5 & A6 & A7).
    refine (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 (conj A6 _)))))). intros v Hv Hp. apply A7; [lia | exact Hp].
  - intros v Hv Hp. destruct (H v ltac:(lia) Hp) as (T & q & x & Hf & Hx). exists T, q, x. split; [exact Hf | lia].
  - intros v Hv Hp. apply H; [lia | exact Hp].
Qed.

(* ------------------------------------------------------------------ *)
(* consequences of a pump                                              *)
(* ------------------------------------------------------------------ *)

Lemma fs_shA_add : forall M a b (s : fcfg M), fs_shA M a (fs_shA M b s) = fs_shA M (b + a) s.
Proof. intros M a b [[q x] p]. cbn [fs_shA]. f_equal. f_equal. lia. Qed.

Lemma fo_d_diff : forall M s0 a k,
  (- Z.of_nat k <= fo_d M s0 (a + k) - fo_d M s0 a <= Z.of_nat k)%Z.
Proof.
  intros M s0 a k. induction k as [| k IH]; [rewrite Nat.add_0_r; simpl; lia |].
  replace (a + S k) with (S (a + k)) by lia.
  destruct (fo_step M s0 (a + k)) as [_ H]. lia.
Qed.

Section Pump.
Variable M : tc2_am.
Variable s0 : fcfg M.
Variables i p g2 : nat.
Variable d : Z.
Hypothesis hpump : fs_pump M s0 i p g2 d.
Local Notation Sx t := (fo_s M s0 t).
Local Notation Xx t := (fx M (fo_s M s0 t)).
Local Notation Dx t := (fo_d M s0 t).
Local Notation Bt := (am_B M).

Lemma pump_D : forall r t, i <= t -> (Dx (t + r * p) = Dx t + Z.of_nat r * d)%Z.
Proof.
  intros r t Ht. induction r as [| r IH].
  - rewrite Nat.mul_0_l, Nat.add_0_r. simpl. lia.
  - destruct hpump as (_ & _ & H3 & _).
    replace (t + S r * p) with ((t + r * p) + p) by (simpl; ring).
    destruct (H3 (t + r * p) ltac:(lia)) as [_ H]. rewrite H, IH. lia.
Qed.

Lemma pump_S : forall r t, i <= t -> Sx (t + r * p) = fs_shA M (2 * (r * g2)) (Sx t).
Proof.
  intros r t Ht. induction r as [| r IH].
  - rewrite Nat.mul_0_l, Nat.add_0_r. destruct (Sx t) as [[q x] pp]. cbn [fs_shA]. rewrite Nat.mul_0_r, Nat.add_0_r. reflexivity.
  - destruct hpump as (_ & _ & H3 & _).
    replace (t + S r * p) with ((t + r * p) + p) by (simpl; ring).
    destruct (H3 (t + r * p) ltac:(lia)) as [H _]. rewrite H, IH, fs_shA_add.
    f_equal. replace (S r * g2) with (r * g2 + g2) by (simpl; ring). lia.
Qed.

Lemma pump_D_even : fp M s0 < 2 -> exists d2 : Z, d = (2 * d2)%Z.
Proof.
  intro hp0.
  destruct hpump as (Hp & _ & H3 & _).
  destruct (H3 i (le_n i)) as [H HD].
  assert (Hpar : fp M (Sx (i + p)) = fp M (Sx i)) by (rewrite H, fp_shA; reflexivity).
  destruct (fo_par M s0 i hp0) as [k1 Hk1]. destruct (fo_par M s0 (i + p) hp0) as [k2 Hk2].
  rewrite Hpar in Hk2. exists (k1 - k2)%Z. lia.
Qed.

End Pump.

Definition fs_fpf (M : tc2_am) (s0 : fcfg M) (v T : nat) : Prop :=
  (forall t, t < T -> (Z.of_nat (am_B M) <= Z.of_nat v + fo_d M s0 t)%Z) /\
  (Z.of_nat v + fo_d M s0 T = Z.of_nat (am_B M) - 1)%Z.

Section Pump2.
Variable M : tc2_am.
Variable s0 : fcfg M.
Variables i p g2 : nat.
Variable d : Z.
Hypothesis hpump : fs_pump M s0 i p g2 d.
Hypothesis hneg : (d < 0)%Z.
Local Notation Sx t := (fo_s M s0 t).
Local Notation Xx t := (fx M (fo_s M s0 t)).
Local Notation Dx t := (fo_d M s0 t).
Local Notation Bt := (am_B M).

Lemma fp_exist : forall v, Bt <= v -> exists T, fs_fpf M s0 v T.
Proof.
  intros v Hv.
  set (P := fun t => (Z.of_nat v + Dx t < Z.of_nat Bt)%Z).
  assert (Pd : forall n, {P n} + {~ P n}) by (intro n; unfold P; apply Z_lt_dec).
  assert (Hex : exists t, P t).
  { exists (i + (v + i) * p). unfold P. rewrite (pump_D M s0 i p g2 d hpump (v + i) i (le_n i)).
    pose proof (fo_d_bound M s0 i) as Hb. pose proof (am_B1 M) as HB1.
    assert (Hmul : (Z.of_nat (v + i) * d <= - Z.of_nat (v + i))%Z) by nia.
    lia. }
  destruct (tc2_least P Pd Hex) as (T & HT & Hmin).
  destruct T as [| T'].
  - exfalso. unfold P in HT. rewrite fo_d_0 in HT. pose proof (am_B1 M). lia.
  - exists (S T'). split.
    + intros t Ht. specialize (Hmin t Ht). unfold P in Hmin. lia.
    + specialize (Hmin T' (Nat.lt_succ_diag_r T')). unfold P in *.
      destruct (fo_step M s0 T') as [_ Hs]. lia.
Qed.

Lemma fp_T_ge : forall v T, fs_fpf M s0 v T -> v + 1 <= T + Bt.
Proof.
  intros v T [_ H]. pose proof (fo_d_bound M s0 T). lia.
Qed.

Lemma fp_shift : forall v T m, Z.of_nat m = (- d)%Z -> Bt + i + p <= v -> fs_fpf M s0 v T ->
  fs_fpf M s0 (v + m) (T + p).
Proof.
  intros v T m Hm Hv [H1 H2].
  pose proof (fp_T_ge v T (conj H1 H2)) as HT.
  destruct hpump as (Hp & _ & H3 & _).
  assert (HDT : (Dx (T + p) = Dx T + d)%Z).
  { destruct (H3 T ltac:(lia)) as [_ H]. exact H. }
  split.
  - intros t Ht.
    destruct (le_lt_dec (i + p) t) as [Hge | Hlt].
    + assert (HDu : (Dx t = Dx (t - p) + d)%Z).
      { destruct (H3 (t - p) ltac:(lia)) as [_ H]. replace (t - p + p) with t in H by lia. exact H. }
      specialize (H1 (t - p) ltac:(lia)). rewrite Nat2Z.inj_add. lia.
    + pose proof (fo_d_bound M s0 t) as Hb. pose proof (am_B1 M). rewrite Nat2Z.inj_add. lia.
  - rewrite Nat2Z.inj_add. lia.
Qed.

End Pump2.

Lemma fs_start_eq : forall M q0 s0 pi v, fs_par v = pi -> fs_start M q0 s0 v = (q0, s0, pi).
Proof. intros M q0 s0 pi v H. unfold fs_start. rewrite H. reflexivity. Qed.

(* a forced first passage is a real first passage *)
Lemma st_fp_of_fpf : forall M q0 s0 pi v T, fs_par v = pi ->
  fs_fpf M (q0, s0, pi) v T ->
  st_fp M q0 s0 v T (fq M (fo_s M (q0, s0, pi) T)) (fx M (fo_s M (q0, s0, pi) T)).
Proof.
  intros M q0 s0 pi v T Hpar [H1 H2].
  pose proof (fs_start_eq M q0 s0 pi v Hpar) as Hst.
  assert (Hc : forall n, n <= T -> (forall t, t < n -> (Z.of_nat (am_B M) <= Z.of_nat v + fo_d M (fs_start M q0 s0 v) t)%Z) ->
     exists y, Z.of_nat y = (Z.of_nat v + fo_d M (q0, s0, pi) n)%Z /\
       am_run M n (q0, s0, v) = (fq M (fo_s M (q0, s0, pi) n), fx M (fo_s M (q0, s0, pi) n), y)).
  { intros n Hn Hh. pose proof (fs_corr M q0 s0 v n Hh) as (y & Hy & Hrun & _).
    rewrite Hst in Hy, Hrun. exists y. split; assumption. }
  assert (Hh : forall n, n <= T -> forall t, t < n -> (Z.of_nat (am_B M) <= Z.of_nat v + fo_d M (fs_start M q0 s0 v) t)%Z).
  { intros n Hn t Ht. rewrite Hst. apply H1. lia. }
  split.
  - destruct (Hc T (le_n T) (Hh T (le_n T))) as (y & Hy & Hrun). rewrite Hrun.
    pose proof (am_B1 M). f_equal. f_equal. lia.
  - intros t Ht. destruct (Hc t ltac:(lia) (Hh t ltac:(lia))) as (y & Hy & Hrun). rewrite Hrun. unfold am_b. cbn [snd].
    pose proof (H1 t Ht). lia.
Qed.

Lemma fs_nx_none_inv : forall M s, fs_nx M s = None -> am_nx M (fq M s) (fx M s) (fs_yrep M (fp M s)) = None.
Proof.
  intros M [[q x] p] H. unfold fs_nx in H. cbn [fq fx fp fst snd].
  destruct (am_nx M q x (fs_yrep M p)) as [[[q' x'] y'] |]; [discriminate | reflexivity].
Qed.

Lemma fs_nx_some_inv : forall M s, fs_nx M s <> None ->
  exists q' x' y', am_nx M (fq M s) (fx M s) (fs_yrep M (fp M s)) = Some (q', x', y').
Proof.
  intros M [[q x] p] H. unfold fs_nx in H. cbn [fq fx fp fst snd].
  destruct (am_nx M q x (fs_yrep M p)) as [[[q' x'] y'] |]; [eauto | exfalso; apply H; reflexivity].
Qed.

(* the leaf: the machine stops after the first halting time of the forced run *)
Lemma st_leaf_of_halt : forall M q0 s0 pi H,
  fp M (q0, s0, pi) < 2 ->
  fs_nx M (fo_s M (q0, s0, pi) H) = None ->
  st_leaf M q0 s0 pi (H + am_B M + 1) (fx M (fo_s M (q0, s0, pi) H)).
Proof.
  intros M q0 s0 pi H Hp2 Hnone.
  exists H, (fq M (fo_s M (q0, s0, pi) H)), (fx M (fo_s M (q0, s0, pi) H)), (fo_d M (q0, s0, pi) H).
  split; [lia |]. intros v Hv Hpar.
  pose proof (fs_start_eq M q0 s0 pi v Hpar) as Hst.
  assert (Hh : forall t, t < H -> (Z.of_nat (am_B M) <= Z.of_nat v + fo_d M (fs_start M q0 s0 v) t)%Z).
  { intros t Ht. rewrite Hst. pose proof (fo_d_bound M (q0, s0, pi) t). lia. }
  destruct (fs_corr M q0 s0 v H Hh) as (y & Hy & Hrun & Hp).
  rewrite Hst in Hy, Hrun, Hp. exists y. split; [exact Hy |]. split; [exact Hrun |].
  pose proof (fo_d_bound M (q0, s0, pi) H) as Hb.
  pose proof (fs_nx_none_inv M _ Hnone) as Hn.
  pose proof (fo_p_lt M (q0, s0, pi) H Hp2) as Hp2'.
  unfold am_hlt. cbn [fst snd]. rewrite Hp in Hn, Hp2'.
  apply (real_none M _ _ y (fs_par y)); [exact Hn | lia | reflexivity | exact Hp2'].
Qed.

(* a pump that does not descend never lets the machine stop *)
Lemma st_nh_of_pump : forall M q0 s0 pi i p g2 d,
  fs_pump M (q0, s0, pi) i p g2 d -> (0 <= d)%Z -> fp M (q0, s0, pi) < 2 ->
  st_nh M q0 s0 pi (am_B M + i + p).
Proof.
  intros M q0 s0 pi i p g2 d Hpump Hd Hp2 v Hv Hpar n Hhlt.
  assert (HDlow : forall t, (- Z.of_nat (i + p) <= fo_d M (q0, s0, pi) t)%Z).
  { intro t. induction t as [t IH] using lt_wf_ind.
    destruct (le_lt_dec (i + p) t) as [Hge | Hlt].
    - destruct Hpump as (Hp & _ & H3 & _).
      destruct (H3 (t - p) ltac:(lia)) as [_ H]. replace (t - p + p) with t in H by lia. rewrite H.
      specialize (IH (t - p) ltac:(lia)). lia.
    - pose proof (fo_d_bound M (q0, s0, pi) t). lia. }
  pose proof (fs_start_eq M q0 s0 pi v Hpar) as Hst.
  assert (Hh : forall t, t < n -> (Z.of_nat (am_B M) <= Z.of_nat v + fo_d M (fs_start M q0 s0 v) t)%Z).
  { intros t Ht. rewrite Hst. specialize (HDlow t). lia. }
  destruct (fs_corr M q0 s0 v n Hh) as (y & Hy & Hrun & Hp).
  rewrite Hst in Hy, Hrun, Hp. rewrite Hrun in Hhlt. unfold am_hlt in Hhlt. cbn [fst snd] in Hhlt.
  destruct Hpump as (Hpp & Hnh & _).
  destruct (fs_nx_some_inv M _ (Hnh n)) as (q' & x' & y' & Hs).
  pose proof (fo_p_lt M (q0, s0, pi) n Hp2) as Hp2'.
  rewrite Hp in Hs, Hp2'.
  specialize (HDlow n).
  eapply real_some; [exact Hs | | reflexivity | exact Hp2'|exact Hhlt]. lia.
Qed.

Lemma bounded_range : forall (f : nat -> nat) n, exists Mx, forall u, u < n -> f u <= Mx.
Proof.
  intros f n. induction n as [| n IH].
  - exists 0. intros u Hu. lia.
  - destruct IH as [Mx H]. exists (Nat.max Mx (f n)). intros u Hu.
    destruct (Nat.eq_dec u n) as [-> | Hne]; [apply Nat.le_max_r |].
    pose proof (H u ltac:(lia)). pose proof (Nat.le_max_l Mx (f n)). lia.
Qed.

(* an exact period keeps counter A bounded *)
Lemma pump0_bounded : forall M s0 i p d, fs_pump M s0 i p 0 d -> exists Xm, forall t, fx M (fo_s M s0 t) <= Xm.
Proof.
  intros M s0 i p d Hpump.
  destruct (bounded_range (fun t => fx M (fo_s M s0 t)) (i + p)) as [Xm HX]. exists Xm.
  intro t. induction t as [t IH] using lt_wf_ind.
  destruct (le_lt_dec (i + p) t) as [Hge | Hlt].
  - destruct Hpump as (Hp & _ & H3 & _). destruct (H3 (t - p) ltac:(lia)) as [H _].
    replace (t - p + p) with t in H by lia. rewrite H, fs_shA_0. apply IH. lia.
  - apply HX. exact Hlt.
Qed.

Lemma st_bdd_of_pump : forall M q0 s0 pi i p d,
  fs_pump M (q0, s0, pi) i p 0 d -> (d < 0)%Z ->
  exists th, st_bdd M q0 s0 pi th.
Proof.
  intros M q0 s0 pi i p d Hpump Hd.
  destruct (pump0_bounded M _ i p d Hpump) as [Xm HX].
  exists (am_B M + i + p + Xm). intros v Hv Hpar.
  destruct (fp_exist M (q0, s0, pi) i p 0 d Hpump Hd v ltac:(lia)) as [T HT].
  exists T, (fq M (fo_s M (q0, s0, pi) T)), (fx M (fo_s M (q0, s0, pi) T)). split.
  - apply st_fp_of_fpf; assumption.
  - specialize (HX T). lia.
Qed.

Lemma fo_x_from : forall M s0 a k, fx M (fo_s M s0 (a + k)) <= fx M (fo_s M s0 a) + k.
Proof.
  intros M s0 a k. induction k as [| k IH]; [rewrite Nat.add_0_r; lia |].
  replace (a + S k) with (S (a + k)) by lia.
  destruct (fo_step M s0 (a + k)) as [[H | [H | H]] _]; lia.
Qed.

Lemma st_next_of_pump : forall M q0 s0 pi i p g2 d K,
  fp M (q0, s0, pi) < 2 ->
  fs_pump M (q0, s0, pi) i p g2 d -> (d < 0)%Z -> 0 < g2 -> p <= K ->
  st_next M q0 s0 pi (am_B M + i + p) K.
Proof.
  intros M q0 s0 pi i p g2 d K Hp2 Hpump Hd Hg HK.
  destruct (pump_D_even M _ i p g2 d Hpump Hp2) as [d2 Hd2].
  assert (Hdp : (- Z.of_nat p <= d)%Z).
  { destruct Hpump as (_ & _ & H3 & _). destruct (H3 i (le_n i)) as [_ H].
    pose proof (fo_d_diff M (q0, s0, pi) i p). lia. }
  assert (Hxp : 2 * g2 <= p).
  { destruct Hpump as (_ & _ & H3 & _). destruct (H3 i (le_n i)) as [H _].
    pose proof (fo_x_from M (q0, s0, pi) i p) as Hx.
    assert (Hxi : fx M (fo_s M (q0, s0, pi) (i + p)) = fx M (fo_s M (q0, s0, pi) i) + 2 * g2) by (rewrite H, fx_shA; reflexivity).
    lia. }
  assert (Hpos : 0 < p) by (destruct Hpump as (H & _); exact H).
  (* SAFE: the context gives 0 <= - d2, so Z.to_nat is exact here and clamps nothing. *)
  assert (Hm2 : Z.of_nat (Z.to_nat (- d2)) = (- d2)%Z) by (apply Z2Nat.id; lia).
  set (m2 := Z.to_nat (- d2)) in *.
  assert (Hm2p : 0 < m2) by lia.
  assert (Hm2q : 2 * m2 <= p) by lia.
  exists p, g2, m2. refine (conj Hpos (conj HK (conj Hg (conj Hxp (conj Hm2p (conj Hm2q _)))))).
  intros v Hv Hpar.
  destruct (fp_exist M (q0, s0, pi) i p g2 d Hpump Hd v ltac:(lia)) as [T0 HT0].
  pose proof (st_fp_of_fpf M q0 s0 pi v T0 Hpar HT0) as Hlink.
  split.
  - exists T0, (fq M (fo_s M (q0, s0, pi) T0)), (fx M (fo_s M (q0, s0, pi) T0)). exact Hlink.
  - intros T q x Hfp.
    destruct (st_fp_unique M q0 s0 v T T0 q x _ _ Hfp Hlink) as (E1 & E2 & E3).
    subst T0. subst q x.
    assert (HmZ : Z.of_nat (2 * m2) = (- d)%Z) by lia.
    pose proof (fp_shift M (q0, s0, pi) i p g2 d Hpump Hd v T (2 * m2) HmZ ltac:(lia) HT0) as Hsh.
    assert (Hpar2 : fs_par (v + 2 * m2) = pi) by (rewrite fs_par_add2; exact Hpar).
    pose proof (st_fp_of_fpf M q0 s0 pi (v + 2 * m2) (T + p) Hpar2 Hsh) as Hlink2.
    pose proof (fp_T_ge M (q0, s0, pi) v T HT0) as HTge.
    destruct Hpump as (_ & _ & H3 & _). destruct (H3 T ltac:(lia)) as [HS _].
    rewrite HS, fq_shA, fx_shA in Hlink2. exact Hlink2.
Qed.

Theorem sl_type : forall M q0 s0 pi, In q0 (am_lq M) -> s0 < am_B M -> pi < 2 ->
  exists th Xl, st_any M q0 s0 pi th Xl (length (fs_lA M)).
Proof.
  intros M q0 s0 pi Hq Hs Hp.
  destruct (orb_class M (q0, s0, pi) Hq Hp Hs) as [(H & Hh & _) | (i & p & g2 & d & Hpump)].
  - exists (H + am_B M + 1), (fx M (fo_s M (q0, s0, pi) H)). left. apply st_leaf_of_halt; [exact Hp | exact Hh].
  - destruct (Z_lt_dec d 0) as [Hd | Hd].
    + destruct (Nat.eq_dec g2 0) as [-> | Hg].
      * destruct (st_bdd_of_pump M q0 s0 pi i p d Hpump Hd) as [th Hb].
        exists th, 0. right; right; left. exact Hb.
      * exists (am_B M + i + p), 0. right; left.
        destruct Hpump as (Hp0 & Hnh & Hper & Hg').
        apply (st_next_of_pump M q0 s0 pi i p g2 d _ Hp (conj Hp0 (conj Hnh (conj Hper Hg'))) Hd ltac:(lia)).
        destruct Hg' as [H0 | (_ & Hpk & _)]; [lia | exact Hpk].
    + exists (am_B M + i + p), 0. right; right; right.
      apply (st_nh_of_pump M q0 s0 pi i p g2 d Hpump ltac:(lia) Hp).
Qed.

Definition st_types (M : tc2_am) : list (am_Q M * nat * nat) :=
  list_prod (list_prod (am_lq M) (seq 0 (am_B M))) [0; 1].

Lemma st_all_list : forall M (l : list (am_Q M * nat * nat)),
  (forall q0 s0 pi, In (q0, s0, pi) l -> In q0 (am_lq M) /\ s0 < am_B M /\ pi < 2) ->
  exists th Xl, forall q0 s0 pi, In (q0, s0, pi) l -> st_any M q0 s0 pi th Xl (length (fs_lA M)).
Proof.
  intros M l. induction l as [| [[q1 s1] p1] l IH]; intro Hv.
  - exists 0, 0. intros q0 s0 pi H. contradiction.
  - destruct (IH (fun q0 s0 pi H => Hv q0 s0 pi (or_intror H))) as (th2 & Xl2 & H2).
    destruct (Hv q1 s1 p1 (or_introl eq_refl)) as (V1 & V2 & V3).
    destruct (sl_type M q1 s1 p1 V1 V2 V3) as (th1 & Xl1 & H1).
    exists (Nat.max th1 th2), (Nat.max Xl1 Xl2). intros q0 s0 pi [Heq | Hin].
    + injection Heq as <- <- <-. eapply st_any_mono; [exact H1 | apply Nat.le_max_l | apply Nat.le_max_l].
    + eapply st_any_mono; [apply H2; exact Hin | apply Nat.le_max_r | apply Nat.le_max_r].
Qed.

(* the stage lemma for all types at once *)
Theorem sl_all : forall M, exists th Xl, forall q0 s0 pi,
  In q0 (am_lq M) -> s0 < am_B M -> pi < 2 ->
  st_any M q0 s0 pi th Xl (length (fs_lA M)).
Proof.
  intro M.
  destruct (st_all_list M (st_types M)) as (th & Xl & H).
  - intros q0 s0 pi Hin. unfold st_types in Hin. apply in_prod_iff in Hin. destruct Hin as [Hin Hp].
    apply in_prod_iff in Hin. destruct Hin as [Hq Hs]. apply in_seq in Hs.
    repeat split; [exact Hq | lia | destruct Hp as [<- | [<- | []]]; lia].
  - exists th, Xl. intros q0 s0 pi Hq Hs Hp. apply H. unfold st_types. apply in_prod_iff. split.
    + apply in_prod_iff. split; [exact Hq | apply in_seq; lia].
    + destruct pi as [| [| pi]]; [left; reflexivity | right; left; reflexivity | lia].
Qed.

Print Assumptions sl_all.
