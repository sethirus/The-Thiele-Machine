(** NecEChsh.v: the CHSH check over the reals, at its limits.

    The book's theorems "The integer check implies the pinned matrix is
    PSD", "PSD forces the Tsirelson bound", "The check is exact" and the
    derivation appendix. This file shows:

    1. A passing tally never reaches the bound: S^2 < 8 strictly
       [nec_e_check_strict], because its score is a fraction and S^2 = 8
       would make the square root of 8 a fraction. And no smaller bound
       holds: for every eps > 0 a passing tally has S^2 > 8 - eps
       [nec_e_check_sharp]. So 2 sqrt 2 is the least upper bound of the
       scores the check accepts, and it is not attained.
    2. The pinned PSD condition and the completion set do reach it: the
       point (c, c, c, -c) with c = 1 / sqrt 2 is pinned PSD and elliptope
       realizable with S^2 = 8 [nec_e_pinned_tsirelson_tight].
    3. The sampling half of the meaning is needed: the empty tally has a
       PSD pinned matrix and fails the check [nec_e_sampled_needed]. Each
       of the seven integer facts is needed: its witness tally fails the
       meaning [nec_e_facts_needed_for_meaning].
    4. The positivity premises of the denominator-clearing lemma are
       needed [nec_e_clear_needs_positive].
    5. Zero marginals are needed for "PSD iff contractive": with marginals,
       a deterministic plan's full matrix is PSD with non-contractive
       correlators, and a contractive table has a non-PSD full matrix
       [nec_e_marginals_psd_not_contractive,
       nec_e_marginals_contractive_not_psd].
    6. The three contraction conditions are independent
       [nec_e_contractive_independent].
    7. Each row bound of the row form of Tsirelson's bound is needed
       [nec_e_row_bounds_needed].
    8. Every deterministic plan fails the pinned PSD test
       [nec_e_deterministic_not_pinned_psd].
    9. The 2x2 test is an equivalence [nec_e_psd2_iff]; the converse of the
       discriminant lemma is false [nec_e_discriminant_converse_false].
   10. The zero-moment check's bound |S| <= 2 is attained by a passing
       record [nec_e_gzero_tight].
   11. A raised flag needs the clean start [nec_e_flag_needs_clean].
   12. The check with a tolerance eps = p / q: at eps = 0 it is the exact
       check [nec_e_tol_check_zero]; a pass means the correlator matrix
       has operator norm at most 1 + eps [nec_e_tol_check_norm] and
       S^2 <= 8 (1 + eps)^2 [nec_e_tol_check_bound]; a noisy tally near the
       Tsirelson point fails the exact check and passes at eps = 1/10
       [nec_e_tol_check_accepts_noisy_tsirelson].

    These results use the real numbers; their assumptions are the
    standard library's classical-real axioms, as for the repo's CHSH files. *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is the CHSH check over the real numbers (it imports the machine-free
   quantum files only). Its link to the abstract record (the machine of
   SmallChshMachine.v as a CertificationSystem, with the floor of 3 for a
   certified run) lives in SmallChshLinks.v. *)

From Coq Require Import List Arith Lia Bool Reals Lra Psatz ZArith.
Import ListNotations.
Require Coq.Vectors.Fin.
From Kernel Require Import ConstructivePSD NPAMomentMatrix TsirelsonFromAlgebra
  SmallChshCheck CHSHColumnCheck ElliptopeCompletion QuantumPartitionPSD_1AB SmallChshMachine.
Require Minimal.EarnedMulti.
From Kernel Require Import NecEChshInt.
Module MM := Minimal.EarnedMulti.

Local Open Scope R_scope.

(* ================================================================= *)
(* 0. Square roots of 8 are not fractions.                              *)
(* ================================================================= *)

Lemma nec_e_sq2_descent : forall n (a b : Z),
  (Z.abs_nat b < n)%nat -> (a * a = 2 * (b * b))%Z -> b = 0%Z.
Proof.
  induction n as [| n IH]; intros a b Hb H; [lia |].
  assert (Ha : Z.even a = true).
  { assert (E : Z.even (a * a) = true) by (rewrite H, Z.even_mul; reflexivity).
    rewrite Z.even_mul, orb_diag in E. exact E. }
  apply Z.even_spec in Ha as [c Hc]. subst a.
  assert (Hb2 : (b * b = 2 * (c * c))%Z) by lia.
  assert (Hbe : Z.even b = true).
  { assert (E : Z.even (b * b) = true) by (rewrite Hb2, Z.even_mul; reflexivity).
    rewrite Z.even_mul, orb_diag in E. exact E. }
  apply Z.even_spec in Hbe as [d Hd]. subst b.
  assert (Hcd : (c * c = 2 * (d * d))%Z) by lia.
  destruct (Z.eq_dec d 0) as [-> | Hd0]; [lia |].
  exfalso. apply Hd0. apply (IH c d); [| exact Hcd]. lia.
Qed.

Lemma nec_e_no_sqrt8 : forall a b : Z, (a * a = 8 * (b * b))%Z -> b = 0%Z.
Proof.
  intros a b H.
  assert (H2 : (a * a = 2 * ((2 * b) * (2 * b)))%Z) by lia.
  pose proof (nec_e_sq2_descent (S (Z.abs_nat (2 * b))) a (2 * b) ltac:(lia) H2). lia.
Qed.

(* ================================================================= *)
(* 1. A passing tally stays strictly below 8.                          *)
(* ================================================================= *)

Lemma nec_e_corr_frac : forall s d, (0 < s + d)%nat ->
  small_chsh_corr s d = IZR (Z.of_nat s - Z.of_nat d) / IZR (Z.of_nat (s + d)).
Proof.
  intros s d H. unfold small_chsh_corr.
  destruct (Nat.eqb (s + d) 0) eqn:E; [apply Nat.eqb_eq in E; lia |].
  rewrite minus_IZR, <- !INR_IZR_INZ. reflexivity.
Qed.

Theorem nec_e_check_strict : forall t,
  small_chsh_check t = true -> small_chsh_score t * small_chsh_score t < 8.
Proof.
  intros t H.
  destruct (small_chsh_check_tsirelson t H) as [Hle _].
  destruct (proj1 (small_chsh_check_iff t) H) as [[P0 [P1 [P2 P3]]] _].
  destruct (Rle_lt_or_eq_dec _ _ Hle) as [Hlt | Heq]; [exact Hlt | exfalso].
  unfold small_chsh_score, CHSH_value, small_chsh_e00, small_chsh_e01,
    small_chsh_e10, small_chsh_e11 in Heq.
  rewrite !nec_e_corr_frac in Heq by assumption.
  destruct t as [s0 d0 s1 d1 s2 d2 s3 d3]; simpl in *.
  set (x0 := (Z.of_nat s0 - Z.of_nat d0)%Z) in *. set (m0 := Z.of_nat (s0 + d0)) in *.
  set (x1 := (Z.of_nat s1 - Z.of_nat d1)%Z) in *. set (m1 := Z.of_nat (s1 + d1)) in *.
  set (x2 := (Z.of_nat s2 - Z.of_nat d2)%Z) in *. set (m2 := Z.of_nat (s2 + d2)) in *.
  set (x3 := (Z.of_nat s3 - Z.of_nat d3)%Z) in *. set (m3 := Z.of_nat (s3 + d3)) in *.
  assert (Q0 : (0 < m0)%Z) by (unfold m0; lia). assert (Q1 : (0 < m1)%Z) by (unfold m1; lia).
  assert (Q2 : (0 < m2)%Z) by (unfold m2; lia). assert (Q3 : (0 < m3)%Z) by (unfold m3; lia).
  assert (R0 : IZR m0 <> 0) by (apply not_0_IZR; lia).
  assert (R1 : IZR m1 <> 0) by (apply not_0_IZR; lia).
  assert (R2 : IZR m2 <> 0) by (apply not_0_IZR; lia).
  assert (R3 : IZR m3 <> 0) by (apply not_0_IZR; lia).
  set (K := (x0 * m1 * m2 * m3 + m0 * x1 * m2 * m3 + m0 * m1 * x2 * m3 - m0 * m1 * m2 * x3)%Z).
  set (P := (m0 * m1 * m2 * m3)%Z).
  assert (HK : IZR K = (IZR x0 / IZR m0 + IZR x1 / IZR m1 + IZR x2 / IZR m2 - IZR x3 / IZR m3)
                        * IZR P).
  { unfold K, P. rewrite minus_IZR, !plus_IZR, !mult_IZR. field. auto. }
  assert (HKP : IZR (K * K) = IZR (8 * (P * P))).
  { rewrite !mult_IZR, HK. rewrite <- Heq. ring. }
  apply eq_IZR in HKP. apply nec_e_no_sqrt8 in HKP. unfold P in HKP. nia.
Qed.

(* So a passing tally never has S^2 = 8, nor |S| = 2 sqrt 2. *)
Corollary nec_e_check_never_tsirelson : forall t,
  small_chsh_check t = true ->
  small_chsh_score t * small_chsh_score t <> 8 /\ Rabs (small_chsh_score t) < 2 * sqrt 2.
Proof.
  intros t H. pose proof (nec_e_check_strict t H) as Hs. split; [lra |].
  assert (Hsq : 2 * sqrt 2 * (2 * sqrt 2) = 8)
    by (replace (2 * sqrt 2 * (2 * sqrt 2)) with (4 * (sqrt 2 * sqrt 2)) by ring;
        rewrite sqrt_sqrt by lra; ring).
  assert (Hp : 0 < sqrt 2) by (apply sqrt_lt_R0; lra).
  destruct (Rlt_or_le (Rabs (small_chsh_score t)) (2 * sqrt 2)) as [Hl | Hl]; [exact Hl |].
  exfalso. assert (Ha : Rabs (small_chsh_score t) * Rabs (small_chsh_score t) >= 8) by nra.
  rewrite <- Rabs_mult, Rabs_right in Ha by nra. lra.
Qed.

(* ================================================================= *)
(* 2. No smaller bound: passing tallies come as close to 8 as wanted.  *)
(* ================================================================= *)

(* The tally with correlators n/q, n/q, n/q, -n/q. *)
Definition nec_e_near (n q : nat) : small_chsh_tally :=
  small_chsh_mk (q + n) (q - n) (q + n) (q - n) (q + n) (q - n) (q - n) (q + n).

Lemma nec_e_near_check : forall n q, (n <= q)%nat -> (1 <= q)%nat -> (2 * n * n <= q * q)%nat ->
  small_chsh_check (nec_e_near n q) = true.
Proof.
  intros n q Hnq Hq H2.
  apply nec_e_check_iff_facts. intros k Hk.
  unfold nec_e_fact, nec_e_near, small_chsh_d, small_chsh_n. simpl.
  rewrite !Nat2Z.inj_add, !Nat2Z.inj_sub by exact Hnq.
  set (Q := Z.of_nat q). set (N := Z.of_nat n).
  assert (HQ : (1 <= Q)%Z) by (unfold Q; lia).
  assert (HN : (0 <= N <= Q)%Z) by (unfold N, Q; lia).
  assert (H2Z : (2 * N * N <= Q * Q)%Z) by (unfold N, Q; nia).
  destruct k as [| [| [| [| [| [| [| k]]]]]]]; try lia.
  - apply Z.leb_le.
    match goal with |- (0 <= ?e)%Z =>
      replace e with (16 * (Q * Q) * (Q * Q - 2 * N * N))%Z by ring end.
    apply Z.mul_nonneg_nonneg; nia.
  - apply Z.leb_le.
    match goal with |- (0 <= ?e)%Z =>
      replace e with (16 * (Q * Q) * (Q * Q - 2 * N * N))%Z by ring end.
    apply Z.mul_nonneg_nonneg; nia.
  - apply Z.leb_le.
    match goal with |- (?c <= ?ab)%Z =>
      replace c with 0%Z by ring;
      replace ab with ((16 * (Q * Q) * (Q * Q - 2 * N * N)) * (16 * (Q * Q) * (Q * Q - 2 * N * N)))%Z
        by ring end.
    apply Z.square_nonneg.
Qed.

Lemma nec_e_near_score : forall n q, (n <= q)%nat -> (1 <= q)%nat ->
  small_chsh_score (nec_e_near n q) = 4 * INR n / INR q.
Proof.
  intros n q Hnq Hq.
  assert (HQ : 0 < INR q) by (apply lt_0_INR; lia).
  unfold small_chsh_score, CHSH_value, small_chsh_e00, small_chsh_e01, small_chsh_e10,
    small_chsh_e11, small_chsh_corr, nec_e_near. simpl.
  replace (q + n + (q - n))%nat with (2 * q)%nat by lia.
  replace (q - n + (q + n))%nat with (2 * q)%nat by lia.
  destruct (Nat.eqb (2 * q) 0) eqn:E; [apply Nat.eqb_eq in E; lia |].
  rewrite !plus_INR, minus_INR by exact Hnq. rewrite mult_INR. simpl (INR 2). field. lra.
Qed.

Theorem nec_e_check_sharp : forall eps, 0 < eps ->
  exists t, small_chsh_check t = true /\ 8 - eps < small_chsh_score t * small_chsh_score t.
Proof.
  intros eps Heps.
  destruct (archimed (20 / eps)) as [Hup _].
  assert (Hpos : 0 < 20 / eps) by (apply Rdiv_lt_0_compat; lra).
  set (z := up (20 / eps)) in *.
  assert (Hz : (0 < z)%Z) by (apply lt_IZR; lra).
  (* SAFE: Hz says 0 < z, so Z.to_nat z is exact and clamps nothing. *)
  set (n := S (Z.to_nat z)).
  set (q := S (Nat.sqrt (2 * n * n))).
  assert (Hn1 : (1 <= n)%nat) by (unfold n; lia).
  assert (Hsq : (Nat.sqrt (2 * n * n) * Nat.sqrt (2 * n * n) <= 2 * n * n)%nat)
    by (pose proof (Nat.sqrt_spec (2 * n * n) ltac:(lia)) as [H1 _]; exact H1).
  assert (Hsq2 : (2 * n * n < q * q)%nat)
    by (unfold q; pose proof (Nat.sqrt_spec (2 * n * n) ltac:(lia)) as [_ H2]; simpl in H2 |- *; lia).
  assert (Hr : (Nat.sqrt (2 * n * n) <= 2 * n)%nat) by nia.
  assert (Hq2 : (q * q <= 2 * n * n + 4 * n + 1)%nat) by (unfold q; nia).
  assert (Hnq : (n <= q)%nat) by nia.
  assert (Hq1 : (1 <= q)%nat) by (unfold q; lia).
  exists (nec_e_near n q). split; [apply nec_e_near_check; lia |].
  rewrite nec_e_near_score by assumption.
  set (N := INR n) in *. set (Q := INR q) in *.
  assert (HN : 1 <= N) by (unfold N; apply (le_INR 1); exact Hn1).
  assert (HQ : 0 < Q) by (unfold Q; apply lt_0_INR; lia).
  assert (HQ2 : Q * Q <= 2 * N * N + 4 * N + 1).
  { pose proof (le_INR _ _ Hq2) as H. rewrite !plus_INR, !mult_INR in H.
    replace (INR 2) with 2 in H by (simpl; ring).
    replace (INR 4) with 4 in H by (simpl; ring).
    replace (INR 1) with 1 in H by reflexivity.
    change (INR n) with N in H. change (INR q) with Q in H. lra. }
  assert (HepsN : 20 < eps * N).
  { assert (HNz : IZR z < N).
    { unfold N, n. rewrite S_INR, INR_IZR_INZ, Z2Nat.id by lia. lra. }
    assert (H20 : 20 = eps * (20 / eps)) by (field; lra).
    rewrite H20. apply Rmult_lt_compat_l; lra. }
  replace (4 * N / Q * (4 * N / Q)) with (16 * (N * N) / (Q * Q)) by (field; lra).
  apply (Rmult_lt_reg_r (Q * Q)); [nra |].
  unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r by nra.
  destruct (Rle_or_lt 8 eps) as [Hbig | Hsmall].
  - assert (0 < N * N) by nra. nra.
  - assert (Hm : (8 - eps) * (Q * Q) <= (8 - eps) * (2 * N * N + 4 * N + 1))
      by (apply Rmult_le_compat_l; lra).
    assert (Hk : eps * (2 * N * N + 4 * N + 1) > 32 * N + 8) by nra.
    nra.
Qed.

(* ================================================================= *)
(* 3. The pinned PSD condition reaches the bound.                      *)
(* ================================================================= *)

Theorem nec_e_pinned_tsirelson_tight :
  let c := / sqrt 2 in
  npa_psd (zero_marginal_npa c c c (- c)) /\
  elliptope_realizable c c c (- c) /\
  CHSH_value c c c (- c) * CHSH_value c c c (- c) = 8 /\
  chsh_S c c c (- c) * chsh_S c c c (- c) = 8.
Proof.
  intro c.
  assert (Hs : 0 < sqrt 2) by (apply sqrt_lt_R0; lra).
  assert (Hss : sqrt 2 * sqrt 2 = 2) by (apply sqrt_sqrt; lra).
  assert (Hc2 : c * c = / 2) by (unfold c; rewrite <- Rinv_mult, Hss; reflexivity).
  assert (Hpsd : npa_psd (zero_marginal_npa c c c (- c))).
  { apply small_chsh_psd_iff_contractive. unfold small_chsh_contractive.
    split; [nra |]. split; [nra |]. nra. }
  split; [exact Hpsd |]. split; [apply zero_marginal_implies_elliptope, Hpsd |].
  unfold CHSH_value, chsh_S. split; nra.
Qed.

(* ================================================================= *)
(* 4. Every pair sampled is needed; each fact is needed.               *)
(* ================================================================= *)

Definition nec_e_empty : small_chsh_tally := small_chsh_mk 0 0 0 0 0 0 0 0.

Theorem nec_e_sampled_needed :
  small_chsh_psd nec_e_empty /\ ~ small_chsh_sampled nec_e_empty /\
  small_chsh_check nec_e_empty = false /\ ~ small_chsh_meaning nec_e_empty.
Proof.
  assert (Hpsd : small_chsh_psd nec_e_empty).
  { unfold small_chsh_psd. apply small_chsh_psd_iff_contractive.
    unfold small_chsh_e00, small_chsh_e01, small_chsh_e10, small_chsh_e11, small_chsh_corr,
      small_chsh_contractive. simpl. lra. }
  split; [exact Hpsd |]. split; [intros [H _]; simpl in H; lia |].
  split; [reflexivity |]. intros [[H _] _]. simpl in H. lia.
Qed.

Theorem nec_e_facts_needed_for_meaning : forall k, (k < 7)%nat ->
  nec_e_fact k (nec_e_wit k) = false /\
  (forall j, (j < 7)%nat -> j <> k -> nec_e_fact j (nec_e_wit k) = true) /\
  ~ small_chsh_meaning (nec_e_wit k).
Proof.
  intros k Hk. destruct (nec_e_check_facts_irredundant k Hk) as [H1 [H2 H3]].
  split; [exact H1 |]. split; [exact H2 |].
  intro Hm. apply small_chsh_check_iff in Hm. congruence.
Qed.

(* ================================================================= *)
(* 5. The positivity premises of the denominator clearing.             *)
(* ================================================================= *)

(* With N00 = 0 (the other three positive), D00 / N00 is 0 in Coq's
   reals, the correlators (0, 0, 0, 0) are a contraction, and the integer
   facts fail: the equivalence breaks. *)
Theorem nec_e_clear_needs_positive :
  let N00 := 0%Z in let N01 := 1%Z in let N10 := 1%Z in let N11 := 1%Z in
  let D00 := 2%Z in let D01 := 0%Z in let D10 := 0%Z in let D11 := 0%Z in
  let A := (N00 * N00 * (N10 * N10) - D00 * D00 * (N10 * N10) - D10 * D10 * (N00 * N00))%Z in
  let B := (N01 * N01 * (N11 * N11) - D01 * D01 * (N11 * N11) - D11 * D11 * (N01 * N01))%Z in
  let C := (D00 * D01 * N10 * N11 + D10 * D11 * N00 * N01)%Z in
  (0 < N01)%Z /\ (0 < N10)%Z /\ (0 < N11)%Z /\
  ~ ((0 <= A)%Z /\ (0 <= B)%Z /\ (C * C <= A * B)%Z) /\
  small_chsh_contractive (IZR D00 / IZR N00) (IZR D01 / IZR N01)
                         (IZR D10 / IZR N10) (IZR D11 / IZR N11).
Proof.
  intros. split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
  split; [unfold A; simpl; lia |].
  unfold small_chsh_contractive, N00, N01, N10, N11, D00, D01, D10, D11.
  unfold Rdiv. rewrite Rinv_0. lra.
Qed.

(* ================================================================= *)
(* 6. Zero marginals are needed for "PSD iff contractive".             *)
(* ================================================================= *)

(* The full moment matrix of the deterministic plan "every answer is +1":
   every entry 1. *)
Definition nec_e_ones_npa : NPAMomentMatrix := {|
  npa_EA0 := 1; npa_EA1 := 1; npa_EB0 := 1; npa_EB1 := 1;
  npa_E00 := 1; npa_E01 := 1; npa_E10 := 1; npa_E11 := 1;
  npa_rho_AA := 1; npa_rho_BB := 1 |}.

Theorem nec_e_marginals_psd_not_contractive :
  npa_psd nec_e_ones_npa /\ ~ small_chsh_contractive 1 1 1 1.
Proof.
  split.
  - split; [apply npa_to_matrix_symmetric |].
    intro v. unfold quad5, sum_fin5, nat_matrix_to_fin5, npa_to_matrix, nec_e_ones_npa. simpl.
    set (v0 := v Fin.F1). set (v1 := v (Fin.FS Fin.F1)).
    set (v2 := v (Fin.FS (Fin.FS Fin.F1))). set (v3 := v (Fin.FS (Fin.FS (Fin.FS Fin.F1)))).
    set (v4 := v (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))).
    assert (H : 0 <= (v0 + v1 + v2 + v3 + v4) * (v0 + v1 + v2 + v3 + v4)) by apply Rle_0_sqr.
    nra.
  - unfold small_chsh_contractive. lra.
Qed.

(* A matrix with marginal <A0> = 1 and E00 = 1/2, everything else 0: the
   correlators are a contraction and the matrix is not PSD. *)
Definition nec_e_marg_npa : NPAMomentMatrix := {|
  npa_EA0 := 1; npa_EA1 := 0; npa_EB0 := 0; npa_EB1 := 0;
  npa_E00 := 1 / 2; npa_E01 := 0; npa_E10 := 0; npa_E11 := 0;
  npa_rho_AA := 0; npa_rho_BB := 0 |}.

Theorem nec_e_marginals_contractive_not_psd :
  small_chsh_contractive (1 / 2) 0 0 0 /\ ~ npa_psd nec_e_marg_npa.
Proof.
  split; [unfold small_chsh_contractive; lra |].
  intros [_ H].
  set (v := fun i : Fin.t 5 => match proj1_sig (Fin.to_nat i) with
                               | 0%nat => -2 | 1%nat => 2 | 3%nat => -1 | _ => 0 end).
  specialize (H v). revert H.
  unfold quad5, sum_fin5, nat_matrix_to_fin5, npa_to_matrix, nec_e_marg_npa, v. simpl. lra.
Qed.

(* ================================================================= *)
(* 7. The three contraction conditions are independent.                *)
(* ================================================================= *)

Theorem nec_e_contractive_independent :
  (* first column too long, the rest holds *)
  (1 - 1 * 1 - (-3/4) * (-3/4) < 0 /\ 1 - (3/5) * (3/5) - (4/5) * (4/5) >= 0 /\
   (1 - 1 * 1 - (-3/4) * (-3/4)) * (1 - (3/5) * (3/5) - (4/5) * (4/5))
     - (1 * (3/5) + (-3/4) * (4/5)) * (1 * (3/5) + (-3/4) * (4/5)) >= 0 /\
   ~ npa_psd (zero_marginal_npa 1 (3/5) (-3/4) (4/5))) /\
  (* second column too long, the rest holds *)
  (1 - (3/5) * (3/5) - (4/5) * (4/5) >= 0 /\ 1 - 1 * 1 - (-3/4) * (-3/4) < 0 /\
   (1 - (3/5) * (3/5) - (4/5) * (4/5)) * (1 - 1 * 1 - (-3/4) * (-3/4))
     - ((3/5) * 1 + (4/5) * (-3/4)) * ((3/5) * 1 + (4/5) * (-3/4)) >= 0 /\
   ~ npa_psd (zero_marginal_npa (3/5) 1 (4/5) (-3/4))) /\
  (* both columns fit, they overlap too much *)
  (1 - (3/5) * (3/5) - (3/5) * (3/5) >= 0 /\
   (1 - (3/5) * (3/5) - (3/5) * (3/5)) * (1 - (3/5) * (3/5) - (3/5) * (3/5))
     - ((3/5) * (3/5) + (3/5) * (3/5)) * ((3/5) * (3/5) + (3/5) * (3/5)) < 0 /\
   ~ npa_psd (zero_marginal_npa (3/5) (3/5) (3/5) (3/5))).
Proof.
  split; [| split].
  - split; [lra |]. split; [lra |]. split; [lra |].
    intro H. apply small_chsh_psd_iff_contractive in H. unfold small_chsh_contractive in H. lra.
  - split; [lra |]. split; [lra |]. split; [lra |].
    intro H. apply small_chsh_psd_iff_contractive in H. unfold small_chsh_contractive in H. lra.
  - split; [lra |]. split; [lra |].
    intro H. apply small_chsh_psd_iff_contractive in H. unfold small_chsh_contractive in H. lra.
Qed.

(* ================================================================= *)
(* 8. Each row bound is needed.                                        *)
(* ================================================================= *)

Theorem nec_e_row_bounds_needed :
  (1 * 1 + 0 * 0 <= 1 /\ ~ (2 * 2 + (-2) * (-2) <= 1) /\
   CHSH_value 1 0 2 (-2) * CHSH_value 1 0 2 (-2) > 8) /\
  (~ (2 * 2 + 2 * 2 <= 1) /\ 1 * 1 + 0 * 0 <= 1 /\
   CHSH_value 2 2 1 0 * CHSH_value 2 2 1 0 > 8).
Proof. unfold CHSH_value. repeat split; lra. Qed.

(* ================================================================= *)
(* 9. Every deterministic plan fails the pinned PSD test.              *)
(* ================================================================= *)

Theorem nec_e_deterministic_not_pinned_psd : forall a0 a1 b0 b1 : R,
  a0 * a0 = 1 -> a1 * a1 = 1 -> b0 * b0 = 1 -> b1 * b1 = 1 ->
  ~ npa_psd (zero_marginal_npa (a0 * b0) (a0 * b1) (a1 * b0) (a1 * b1)).
Proof.
  intros a0 a1 b0 b1 H0 H1 H2 H3 H.
  apply small_chsh_psd_iff_contractive in H. destruct H as [Hp _].
  assert (E : 1 - a0 * b0 * (a0 * b0) - a1 * b0 * (a1 * b0) = -1).
  { replace (a0 * b0 * (a0 * b0)) with ((a0 * a0) * (b0 * b0)) by ring.
    replace (a1 * b0 * (a1 * b0)) with ((a1 * a1) * (b0 * b0)) by ring.
    rewrite H0, H1, H2. ring. }
  lra.
Qed.

(* ================================================================= *)
(* 10. The 2x2 test is an equivalence; the discriminant lemma is not.  *)
(* ================================================================= *)

Theorem nec_e_psd2_iff : forall a b d,
  (a >= 0 /\ d >= 0 /\ a * d - b * b >= 0) <->
  (forall u w, a * u * u + 2 * b * u * w + d * w * w >= 0).
Proof.
  intros a b d. split.
  - intros [Ha [Hd Hdet]] u w. apply small_chsh_psd2_form_nonneg; assumption.
  - intro H.
    assert (Ha : a >= 0) by (specialize (H 1 0); lra).
    assert (Hd : d >= 0) by (specialize (H 0 1); lra).
    split; [exact Ha |]. split; [exact Hd |].
    destruct (Req_dec a 0) as [Ha0 | Ha0].
    + subst a. destruct (Req_dec b 0) as [Hb0 | Hb0]; [subst b; lra |].
      exfalso. specialize (H (- (d + 1) / (2 * b)) 1).
      replace (0 * (- (d + 1) / (2 * b)) * (- (d + 1) / (2 * b)) +
               2 * b * (- (d + 1) / (2 * b)) * 1 + d * 1 * 1) with (-1) in H
        by (field; exact Hb0).
      lra.
    + specialize (H (- b) a).
      assert (Hpos : a > 0) by lra.
      assert (E : a * - b * - b + 2 * b * - b * a + d * a * a = a * (a * d - b * b)) by ring.
      rewrite E in H.
      destruct (Rge_or_gt (a * d - b * b) 0) as [Hge | Hlt]; [exact Hge |].
      exfalso. assert (a * (a * d - b * b) < 0) by nra. lra.
Qed.

Theorem nec_e_discriminant_converse_false :
  let a := -1 in let b := 0 in let c := -1 in
  b * b <= a * c /\ ~ (forall t, a + 2 * b * t + c * t * t >= 0).
Proof.
  intros a b c. split; [unfold a, b, c; lra |].
  intro H. specialize (H 0). unfold a, b, c in H. lra.
Qed.

(* ================================================================= *)
(* 11. The zero-moment check reaches |S| = 2.                          *)
(* ================================================================= *)

Definition nec_e_half_wc : WitnessCounts :=
  {| wc_same_00 := 3; wc_diff_00 := 1; wc_same_01 := 3; wc_diff_01 := 1;
     wc_same_10 := 3; wc_diff_10 := 1; wc_same_11 := 1; wc_diff_11 := 3 |}.

Lemma nec_e_sbc_31 : state_bucket_correlation 3 1 = 1 / 2.
Proof. unfold state_bucket_correlation. simpl. field. Qed.

Lemma nec_e_sbc_13 : state_bucket_correlation 1 3 = - (1 / 2).
Proof. unfold state_bucket_correlation. simpl. field. Qed.

Theorem nec_e_gzero_tight :
  column_contractive_check_q1ab nec_e_half_wc = true /\
  let e00 := state_bucket_correlation 3 1 in
  let e01 := state_bucket_correlation 3 1 in
  let e10 := state_bucket_correlation 3 1 in
  let e11 := state_bucket_correlation 1 3 in
  e00 * e00 + e01 * e01 + e10 * e10 + e11 * e11 = 1 /\
  Rabs (e00 + e01 + e10 - e11) = 2.
Proof.
  split; [vm_compute; reflexivity |].
  cbv zeta. rewrite nec_e_sbc_31, nec_e_sbc_13. split; [lra |].
  replace (1 / 2 + 1 / 2 + 1 / 2 - - (1 / 2)) with 2 by lra. apply Rabs_right. lra.
Qed.

(* ================================================================= *)
(* 12. A raised flag needs the clean start.                            *)
(* ================================================================= *)

(* A start that reads no but has a commitment on the channel already,
   with every counter holding the all-ones plan's tally, which fails the
   check. CERTIFY alone raises the flag. *)
Definition nec_e_dirty_core : @MM.core small_chsh_prop :=
  MM.mkcore (fun _ => small_chsh_code small_chsh_tally_all_ones) (fun _ => 0%nat) 1%nat []
            (Some (MM.mkfact small_chsh_PCHSH 0%nat 0%nat)) false.
Definition nec_e_dirty_chsh : @MM.state small_chsh_prop := MM.mkst nec_e_dirty_core 0%nat false.

Theorem nec_e_flag_needs_clean :
  ~ MM.clean_start nec_e_dirty_chsh /\
  MM.cert nec_e_dirty_chsh = false /\
  MM.cert (MM.run small_chsh_prop_eqb small_chsh_eval [MM.CERTIFY] nec_e_dirty_chsh) = true /\
  (forall c, small_chsh_check (small_chsh_tally_of (MM.vals (MM.core_of nec_e_dirty_chsh) c)) = false) /\
  ~ (exists pre1 c mid1 mid2 post,
       [MM.CERTIFY] = pre1 ++ MM.CHECK small_chsh_PCHSH c :: mid1
                      ++ MM.COMMIT small_chsh_PCHSH c :: mid2 ++ MM.CERTIFY :: post).
Proof.
  split; [intros [_ [H _]]; discriminate H |].
  split; [reflexivity |]. split; [reflexivity |].
  split; [intro c; simpl; rewrite small_chsh_tally_of_code; vm_compute; reflexivity |].
  intros [pre1 [c [mid1 [mid2 [post H]]]]].
  apply (f_equal (@length _)) in H. rewrite app_length in H. simpl in H.
  rewrite app_length in H. simpl in H. rewrite app_length in H. simpl in H. lia.
Qed.

(* ================================================================= *)
(* 13. The full 1+AB check needs no positivity premise.                *)
(* ================================================================= *)

(* The check tests the nine positivity facts itself, so the theorem holds
   with them left off. *)
Theorem nec_e_g12345_stronger :
  forall D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z,
  q1ab_g12345_check_z_kernel D00 N00 D01 N01 D10 N10 D11 N11
                             Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 = true ->
  q1ab_g12345_minors_witness
    (IZR D00 / IZR N00) (IZR D01 / IZR N01) (IZR D10 / IZR N10) (IZR D11 / IZR N11)
    (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2) (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4)
    (IZR Ng5 / IZR Dg5) /\
  PSD9 (q1ab_moment_matrix
    (IZR D00 / IZR N00) (IZR D01 / IZR N01) (IZR D10 / IZR N10) (IZR D11 / IZR N11)
    (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2) (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4)
    (IZR Ng5 / IZR Dg5)).
Proof.
  intros D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 H.
  pose proof H as H'. unfold q1ab_g12345_check_z_kernel in H'.
  rewrite !Bool.andb_true_iff in H'.
  repeat match type of H' with ?A /\ _ => destruct H' as [H' _] end.
  assert (Hw : q1ab_g12345_minors_witness
    (IZR D00 / IZR N00) (IZR D01 / IZR N01) (IZR D10 / IZR N10) (IZR D11 / IZR N11)
    (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2) (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4)
    (IZR Ng5 / IZR Dg5)).
  { pose proof H as H2. unfold q1ab_g12345_check_z_kernel in H2.
    rewrite !Bool.andb_true_iff in H2.
    repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
    apply q1ab_g12345_caller_witness_z_abs_sound; try (apply Z.ltb_lt; assumption). exact H. }
  split; [exact Hw | apply q1ab_g12345_minors_witness_implies_psd9, Hw].
Qed.

Print Assumptions nec_e_g12345_stronger.
Print Assumptions nec_e_check_strict.
Print Assumptions nec_e_check_never_tsirelson.
Print Assumptions nec_e_check_sharp.
Print Assumptions nec_e_pinned_tsirelson_tight.
Print Assumptions nec_e_sampled_needed.
Print Assumptions nec_e_facts_needed_for_meaning.
Print Assumptions nec_e_clear_needs_positive.
Print Assumptions nec_e_marginals_psd_not_contractive.
Print Assumptions nec_e_marginals_contractive_not_psd.
Print Assumptions nec_e_contractive_independent.
Print Assumptions nec_e_row_bounds_needed.
Print Assumptions nec_e_deterministic_not_pinned_psd.
Print Assumptions nec_e_psd2_iff.
Print Assumptions nec_e_discriminant_converse_false.
Print Assumptions nec_e_gzero_tight.
Print Assumptions nec_e_flag_needs_clean.

(* ================================================================= *)
(* 12. The check with a tolerance.                                    *)
(* ================================================================= *)

(** The seven integer facts say the 2x2 correlator matrix
    E = [[E00, E01], [E10, E11]] has operator norm at most 1, and the
    Tsirelson point sits on that edge: there E^T E is the identity. So honest
    play aimed at it lands outside about as often as inside on each of the
    edge's directions, and fails the exact check most of the time. The
    tolerance check, for eps = p / q with p >= 0 and q > 0, replaces the 1 by
    (1 + eps)^2 = K / Q, where K = (q + p)^2 and Q = q^2, and clears the
    denominators the same way. At eps = 0 it is the exact check
    ([nec_e_tol_check_zero]). A pass means the operator norm is at most
    1 + eps ([nec_e_tol_check_norm]) and S^2 <= 8 (1 + eps)^2
    ([nec_e_tol_check_bound]). *)
Definition nec_e_tol_check (p q : Z) (wc : WitnessCounts) : bool :=
  let d00 := chsh_d_z wc.(wc_same_00) wc.(wc_diff_00) in
  let n00 := chsh_n_z wc.(wc_same_00) wc.(wc_diff_00) in
  let d01 := chsh_d_z wc.(wc_same_01) wc.(wc_diff_01) in
  let n01 := chsh_n_z wc.(wc_same_01) wc.(wc_diff_01) in
  let d10 := chsh_d_z wc.(wc_same_10) wc.(wc_diff_10) in
  let n10 := chsh_n_z wc.(wc_same_10) wc.(wc_diff_10) in
  let d11 := chsh_d_z wc.(wc_same_11) wc.(wc_diff_11) in
  let n11 := chsh_n_z wc.(wc_same_11) wc.(wc_diff_11) in
  let K := ((q + p) * (q + p))%Z in
  let Q := (q * q)%Z in
  let A := (K * (n00 * n00 * (n10 * n10)) - Q * (d00 * d00 * (n10 * n10))
            - Q * (d10 * d10 * (n00 * n00)))%Z in
  let B := (K * (n01 * n01 * (n11 * n11)) - Q * (d01 * d01 * (n11 * n11))
            - Q * (d11 * d11 * (n01 * n01)))%Z in
  let C := (d00 * d01 * n10 * n11 + d10 * d11 * n00 * n01)%Z in
  andb (Z.ltb 0 q)
  (andb (Z.leb 0 p)
  (andb (Z.ltb 0 n00)
  (andb (Z.ltb 0 n01)
  (andb (Z.ltb 0 n10)
  (andb (Z.ltb 0 n11)
  (andb (Z.leb 0 A)
  (andb (Z.leb 0 B)
        (Z.leb (Q * Q * (C * C)) (A * B))))))))).

(** At eps = 0 the tolerance check is the exact check. *)
Theorem nec_e_tol_check_zero : forall wc,
  nec_e_tol_check 0 1 wc = column_contractive_check_witness wc.
Proof.
  intro wc. unfold nec_e_tol_check, column_contractive_check_witness. cbv zeta.
  rewrite ?Z.add_0_r, ?Z.mul_1_l. reflexivity.
Qed.

(** Clearing the denominators, over the reals. *)
Lemma nec_e_tol_clear : forall rK rQ n00 n01 n10 n11 d00 d01 d10 d11 : R,
  0 < rQ -> 0 < n00 -> 0 < n01 -> 0 < n10 -> 0 < n11 ->
  let A := rK * (n00 * n00 * (n10 * n10)) - rQ * (d00 * d00 * (n10 * n10))
           - rQ * (d10 * d10 * (n00 * n00)) in
  let B := rK * (n01 * n01 * (n11 * n11)) - rQ * (d01 * d01 * (n11 * n11))
           - rQ * (d11 * d11 * (n01 * n01)) in
  let C := d00 * d01 * n10 * n11 + d10 * d11 * n00 * n01 in
  0 <= A -> 0 <= B -> rQ * rQ * (C * C) <= A * B ->
  let r := rK / rQ in
  let e00 := d00 / n00 in let e01 := d01 / n01 in
  let e10 := d10 / n10 in let e11 := d11 / n11 in
  0 <= r - e00 * e00 - e10 * e10 /\ 0 <= r - e01 * e01 - e11 * e11 /\
  (e00 * e01 + e10 * e11) * (e00 * e01 + e10 * e11)
    <= (r - e00 * e00 - e10 * e10) * (r - e01 * e01 - e11 * e11).
Proof.
  intros rK rQ n00 n01 n10 n11 d00 d01 d10 d11 HQ H00 H01 H10 H11 A B C HA HB HC r e00 e01 e10 e11.
  assert (EA : r - e00 * e00 - e10 * e10 = A / (rQ * (n00 * n00 * (n10 * n10)))).
  { unfold r, e00, e10, A. field; repeat split; lra. }
  assert (EB : r - e01 * e01 - e11 * e11 = B / (rQ * (n01 * n01 * (n11 * n11)))).
  { unfold r, e01, e11, B. field; repeat split; lra. }
  assert (EC : e00 * e01 + e10 * e11 = C / (n00 * n01 * n10 * n11)).
  { unfold e00, e01, e10, e11, C. field; repeat split; lra. }
  assert (P1 : 0 < rQ * (n00 * n00 * (n10 * n10))) by (apply Rmult_lt_0_compat; [lra | apply Rmult_lt_0_compat; apply Rmult_lt_0_compat; lra]).
  assert (P2 : 0 < rQ * (n01 * n01 * (n11 * n11))) by (apply Rmult_lt_0_compat; [lra | apply Rmult_lt_0_compat; apply Rmult_lt_0_compat; lra]).
  assert (P3 : 0 < n00 * n01 * n10 * n11) by (repeat apply Rmult_lt_0_compat; lra).
  rewrite EA, EB, EC.
  split; [| split].
  - unfold Rdiv. apply Rmult_le_pos; [exact HA | left; apply Rinv_0_lt_compat; exact P1].
  - unfold Rdiv. apply Rmult_le_pos; [exact HB | left; apply Rinv_0_lt_compat; exact P2].
  - replace (A / (rQ * (n00 * n00 * (n10 * n10))) * (B / (rQ * (n01 * n01 * (n11 * n11)))))
      with (A * B / ((rQ * (n00 * n01 * n10 * n11)) * (rQ * (n00 * n01 * n10 * n11))))
      by (field; lra).
    replace (C / (n00 * n01 * n10 * n11) * (C / (n00 * n01 * n10 * n11)))
      with (rQ * rQ * (C * C) / ((rQ * (n00 * n01 * n10 * n11)) * (rQ * (n00 * n01 * n10 * n11))))
      by (field; lra).
    unfold Rdiv. apply Rmult_le_compat_r; [| exact HC].
    left. apply Rinv_0_lt_compat. apply Rmult_lt_0_compat; apply Rmult_lt_0_compat; lra.
Qed.

(** The tolerance inequalities on the correlators, with r = (1 + p/q)^2. *)
Definition nec_e_tol_contractive (r e00 e01 e10 e11 : R) : Prop :=
  0 <= r - e00 * e00 - e10 * e10 /\ 0 <= r - e01 * e01 - e11 * e11 /\
  (e00 * e01 + e10 * e11) * (e00 * e01 + e10 * e11)
    <= (r - e00 * e00 - e10 * e10) * (r - e01 * e01 - e11 * e11).

Theorem nec_e_tol_check_sound : forall p q wc,
  nec_e_tol_check p q wc = true ->
  (0 < q)%Z /\ (0 <= p)%Z /\
  nec_e_tol_contractive ((1 + IZR p / IZR q) * (1 + IZR p / IZR q))
    (state_bucket_correlation wc.(wc_same_00) wc.(wc_diff_00))
    (state_bucket_correlation wc.(wc_same_01) wc.(wc_diff_01))
    (state_bucket_correlation wc.(wc_same_10) wc.(wc_diff_10))
    (state_bucket_correlation wc.(wc_same_11) wc.(wc_diff_11)).
Proof.
  intros p q wc H. unfold nec_e_tol_check in H. cbv zeta in H.
  apply Bool.andb_true_iff in H; destruct H as [Hq H].
  apply Bool.andb_true_iff in H; destruct H as [Hp H].
  apply Bool.andb_true_iff in H; destruct H as [Hn00 H].
  apply Bool.andb_true_iff in H; destruct H as [Hn01 H].
  apply Bool.andb_true_iff in H; destruct H as [Hn10 H].
  apply Bool.andb_true_iff in H; destruct H as [Hn11 H].
  apply Bool.andb_true_iff in H; destruct H as [HA H].
  apply Bool.andb_true_iff in H; destruct H as [HB HC].
  apply Z.ltb_lt in Hq, Hn00, Hn01, Hn10, Hn11. apply Z.leb_le in Hp, HA, HB, HC.
  split; [exact Hq | split; [exact Hp |]].
  rewrite !state_bucket_correlation_to_IZR by assumption.
  set (n00 := chsh_n_z (wc_same_00 wc) (wc_diff_00 wc)) in *.
  set (n01 := chsh_n_z (wc_same_01 wc) (wc_diff_01 wc)) in *.
  set (n10 := chsh_n_z (wc_same_10 wc) (wc_diff_10 wc)) in *.
  set (n11 := chsh_n_z (wc_same_11 wc) (wc_diff_11 wc)) in *.
  set (d00 := chsh_d_z (wc_same_00 wc) (wc_diff_00 wc)) in *.
  set (d01 := chsh_d_z (wc_same_01 wc) (wc_diff_01 wc)) in *.
  set (d10 := chsh_d_z (wc_same_10 wc) (wc_diff_10 wc)) in *.
  set (d11 := chsh_d_z (wc_same_11 wc) (wc_diff_11 wc)) in *.
  apply IZR_le in HA, HB, HC.
  rewrite !minus_IZR, !mult_IZR, !plus_IZR in HA.
  rewrite !minus_IZR, !mult_IZR, !plus_IZR in HB.
  rewrite !mult_IZR, !plus_IZR, !minus_IZR, !mult_IZR, !plus_IZR in HC.
  assert (Hqr : 0 < IZR q) by (apply IZR_lt; exact Hq).
  assert (Er : (1 + IZR p / IZR q) * (1 + IZR p / IZR q)
               = ((IZR q + IZR p) * (IZR q + IZR p)) / (IZR q * IZR q)) by (field; lra).
  rewrite Er.
  apply (nec_e_tol_clear ((IZR q + IZR p) * (IZR q + IZR p)) (IZR q * IZR q)).
  - nra.
  - apply IZR_lt. exact Hn00.
  - apply IZR_lt. exact Hn01.
  - apply IZR_lt. exact Hn10.
  - apply IZR_lt. exact Hn11.
  - exact HA.
  - exact HB.
  - exact HC.
Qed.

(** What the tolerance inequalities mean: the operator norm of
    E = [[e00, e01], [e10, e11]] is at most the square root of r. *)
Lemma nec_e_tol_contractive_norm : forall r e00 e01 e10 e11,
  nec_e_tol_contractive r e00 e01 e10 e11 ->
  forall u0 u1, (e00 * u0 + e01 * u1) * (e00 * u0 + e01 * u1)
                + (e10 * u0 + e11 * u1) * (e10 * u0 + e11 * u1)
                <= r * (u0 * u0 + u1 * u1).
Proof.
  intros r e00 e01 e10 e11 [Ha [Hc Hd]] u0 u1.
  set (a := r - e00 * e00 - e10 * e10) in *.
  set (c := r - e01 * e01 - e11 * e11) in *.
  set (b := e00 * e01 + e10 * e11) in *.
  assert (Hform : 0 <= a * u0 * u0 - 2 * b * u0 * u1 + c * u1 * u1).
  { assert (Hu1 : 0 <= u1 * u1) by nra.
    destruct (Req_dec a 0) as [Ha0 | Ha0].
    - assert (Hb : b = 0) by (rewrite Ha0 in Hd; nra). rewrite Ha0, Hb.
      replace (0 * u0 * u0 - 2 * 0 * u0 * u1 + c * u1 * u1) with (c * (u1 * u1)) by ring.
      apply Rmult_le_pos; lra.
    - assert (Hapos : 0 < a) by lra.
      assert (H : 0 <= a * (a * u0 * u0 - 2 * b * u0 * u1 + c * u1 * u1)).
      { replace (a * (a * u0 * u0 - 2 * b * u0 * u1 + c * u1 * u1))
          with ((a * u0 - b * u1) * (a * u0 - b * u1) + (a * c - b * b) * (u1 * u1)) by ring.
        apply Rplus_le_le_0_compat; [apply Rle_0_sqr | apply Rmult_le_pos; lra]. }
      apply (Rmult_le_reg_l a); [exact Hapos | rewrite Rmult_0_r; exact H]. }
  assert (Eq : r * (u0 * u0 + u1 * u1)
               - ((e00 * u0 + e01 * u1) * (e00 * u0 + e01 * u1)
                  + (e10 * u0 + e11 * u1) * (e10 * u0 + e11 * u1))
               = a * u0 * u0 - 2 * b * u0 * u1 + c * u1 * u1) by (unfold a, b, c; ring).
  lra.
Qed.

Theorem nec_e_tol_check_norm : forall p q wc,
  nec_e_tol_check p q wc = true ->
  let e00 := state_bucket_correlation wc.(wc_same_00) wc.(wc_diff_00) in
  let e01 := state_bucket_correlation wc.(wc_same_01) wc.(wc_diff_01) in
  let e10 := state_bucket_correlation wc.(wc_same_10) wc.(wc_diff_10) in
  let e11 := state_bucket_correlation wc.(wc_same_11) wc.(wc_diff_11) in
  forall u0 u1, (e00 * u0 + e01 * u1) * (e00 * u0 + e01 * u1)
                + (e10 * u0 + e11 * u1) * (e10 * u0 + e11 * u1)
                <= (1 + IZR p / IZR q) * (1 + IZR p / IZR q) * (u0 * u0 + u1 * u1).
Proof.
  intros p q wc H e00 e01 e10 e11.
  destruct (nec_e_tol_check_sound p q wc H) as [_ [_ Ht]].
  apply nec_e_tol_contractive_norm. exact Ht.
Qed.

(** And the bound: S^2 <= 8 (1 + eps)^2. *)
Theorem nec_e_tol_check_bound : forall p q wc,
  nec_e_tol_check p q wc = true ->
  let e00 := state_bucket_correlation wc.(wc_same_00) wc.(wc_diff_00) in
  let e01 := state_bucket_correlation wc.(wc_same_01) wc.(wc_diff_01) in
  let e10 := state_bucket_correlation wc.(wc_same_10) wc.(wc_diff_10) in
  let e11 := state_bucket_correlation wc.(wc_same_11) wc.(wc_diff_11) in
  (e00 + e01 + e10 - e11) * (e00 + e01 + e10 - e11)
    <= 8 * ((1 + IZR p / IZR q) * (1 + IZR p / IZR q)).
Proof.
  intros p q wc H. cbv zeta.
  destruct (nec_e_tol_check_sound p q wc H) as [_ [_ [Ha [Hc _]]]].
  set (e00 := state_bucket_correlation wc.(wc_same_00) wc.(wc_diff_00)) in *.
  set (e01 := state_bucket_correlation wc.(wc_same_01) wc.(wc_diff_01)) in *.
  set (e10 := state_bucket_correlation wc.(wc_same_10) wc.(wc_diff_10)) in *.
  set (e11 := state_bucket_correlation wc.(wc_same_11) wc.(wc_diff_11)) in *.
  set (r := (1 + IZR p / IZR q) * (1 + IZR p / IZR q)) in *.
  pose proof (chsh_gap_is_sum_of_squares e00 e01 e10 e11) as G.
  assert (Hsos : 0 <= (e00 - e01) * (e00 - e01) + (e00 - e10) * (e00 - e10)
                      + (e00 + e11) * (e00 + e11) + (e01 - e10) * (e01 - e10)
                      + (e01 + e11) * (e01 + e11) + (e10 + e11) * (e10 + e11))
    by (repeat apply Rplus_le_le_0_compat; apply Rle_0_sqr).
  lra.
Qed.

(** A tally near the Tsirelson point, 100 rounds per pair with correlators
    0.72, 0.70, 0.72, -0.72: the exact check refuses it (0.72^2 + 0.72^2 is
    above 1) and the check with eps = 1/10 accepts it. *)
Definition nec_e_noisy_tsirelson_tally : WitnessCounts :=
  {| wc_same_00 := 86; wc_diff_00 := 14;
     wc_same_01 := 85; wc_diff_01 := 15;
     wc_same_10 := 86; wc_diff_10 := 14;
     wc_same_11 := 14; wc_diff_11 := 86 |}.

Example nec_e_tol_check_accepts_noisy_tsirelson :
  column_contractive_check_witness nec_e_noisy_tsirelson_tally = false /\
  nec_e_tol_check 1 10 nec_e_noisy_tsirelson_tally = true.
Proof. split; vm_compute; reflexivity. Qed.

Print Assumptions nec_e_tol_check_zero.
Print Assumptions nec_e_tol_check_sound.
Print Assumptions nec_e_tol_check_norm.
Print Assumptions nec_e_tol_check_bound.
Print Assumptions nec_e_tol_check_accepts_noisy_tsirelson.
