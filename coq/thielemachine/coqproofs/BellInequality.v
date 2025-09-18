Require Import Coq.QArith.QArith.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Require Import Lra.

(* Bell Inequality with Probabilistic Boxes *)

Inductive Bit := B0 | B1.

Definition eqb (a b : Bit) : bool :=
  match a, b with
  | B0, B0 => true
  | B1, B1 => true
  | _, _ => false
  end.

Lemma eqb_eq : forall a b : Bit, eqb a b = true -> a = b.
Proof. destruct a, b; simpl; auto; try discriminate; intros Contra; inversion Contra. Qed.

Lemma eqb_neq : forall a b : Bit, eqb a b = false -> a <> b.
Proof. intros a b H. destruct a, b; simpl in H; try discriminate; intros Contra; inversion Contra. Qed.

Definition sgn (b : Bit) : Z :=
  match b with
  | B0 => (-1)%Z
  | B1 => 1%Z
  end.

(* Summation over bits *)
Definition sum_bit (f : Bit -> Q) : Q :=
  f B0 + f B1.

Definition sum_bit2 (f : Bit -> Bit -> Q) : Q :=
  sum_bit (fun a => sum_bit (fun b => f a b)).

(* A non-signaling box as rational probabilities *)
Record Box := {
  p : Bit -> Bit -> Bit -> Bit -> Q; (* p(a,b | x,y) *)
  norm : forall x y, sum_bit2 (fun a b => p a b x y) = 1#1;
  nonneg : forall a b x y, 0#1 <= p a b x y;
  nosig_A : forall x y1 y2 a, sum_bit (fun b => p a b x y1) = sum_bit (fun b => p a b x y2);
  nosig_B : forall y x1 x2 b, sum_bit (fun a => p a b x1 y) = sum_bit (fun a => p a b x2 y)
}.

(* Correlator and CHSH *)
Definition E (B : Box) (x y : Bit) : Q :=
  sum_bit2 (fun a b => (inject_Z (sgn a * sgn b)) * B.(p) a b x y).

Definition S (B : Box) : Q :=
  E B B1 B1 + E B B1 B0 + E B B0 B1 - E B B0 B0.

(* Local box: decomposable into local response functions *)
Definition local (B : Box) : Prop :=
  exists (p_lambda : Bit -> Q) (p_A : Bit -> Bit -> Bit -> Q) (p_B : Bit -> Bit -> Bit -> Q),
    (forall lambda, 0#1 <= p_lambda lambda) /\
    sum_bit p_lambda = 1#1 /\
    (forall x lambda, sum_bit (fun a => p_A a x lambda) = 1#1) /\
    (forall y lambda, sum_bit (fun b => p_B b y lambda) = 1#1) /\
    forall a b x y,
      B.(p) a b x y = sum_bit (fun lambda => p_lambda lambda * p_A a x lambda * p_B b y lambda).

Definition Qabs (x : Q) : Q := if Qle_bool 0 x then x else -x.

Definition deterministic (B : Box) : Prop :=
  forall x y, exists a b, B.(p) a b x y = 1#1 /\
    forall a' b', B.(p) a' b' x y = 1#1 -> a' = a /\ b' = b /\
    forall a b, B.(p) a b x y = 0#1 \/ B.(p) a b x y = 1#1.

Definition local_deterministic (B : Box) : Prop :=
  deterministic B /\
  exists A C : Bit -> Bit, forall x y, B.(p) (A x) (C y) x y = 1#1.

(* The classical bound: for any local deterministic box, |S| <= 2 *)
Theorem local_deterministic_CHSH_bound : forall (B : Box), local_deterministic B -> Qabs (S B) <= 2#1.
Proof.
  intros B [Hdet Hexists].
  destruct Hexists as [A [C HAC]].
  unfold S, E.
  assert (E_eq : forall x y, E B x y = inject_Z (sgn (A x) * sgn (C y))).
  { intros x y.
    unfold E, sum_bit2, sum_bit.
    (* Only (A x, C y) has p = 1, all others are zero *)
    assert (forall a b, B.(p) a b x y = if eqb a (A x) && eqb b (C y) then 1#1 else 0#1).
    { intros a b.
      destruct (A x) eqn:Ax, (C y) eqn:Cy; destruct a, b; simpl.
      - pose proof (HAC x y) as H; rewrite Ax, Cy in H; apply H.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - destruct (Hdet x y) as [a0 [b0 [H1 [H2 H3]]]].
        destruct (H3 B0 B1) as [H4 | H5]; [assumption | contradiction].
      - pose proof (HAC x y) as H; rewrite Ax, Cy in H; apply H.
      - destruct (Hdet x y) as [a0 [b0 [H1 [H2 H3]]]].
        destruct (H3 B1 B0) as [H | H]; [assumption | specialize (H2 B1 B0 H); destruct H2 as [Ha Hb]; contradiction Hb].
      - destruct (Hdet x y) as [a0 [b0 [H1 [H2 H3]]]].
        destruct (H3 B1 B1) as [H | H]; [assumption | specialize (H2 B1 B1 H); destruct H2 as [Ha Hb]; contradiction Hb].
      - destruct (Hdet x y) as [a0 [b0 [H1 [H2 H3]]]].
        destruct (H3 B0 B0) as [H | H]; [assumption | specialize (H2 B0 B0 H); destruct H2 as [Ha Hb]; contradiction Hb].
      - reflexivity.
      - pose proof (HAC x y) as H; rewrite Ax, Cy in H; apply H.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - unfold sum_bit2, sum_bit.
        pose proof (HAC x y) as H; rewrite Ax, Cy in H; rewrite H.
        reflexivity.
    }
    rewrite (H0 B0 B0), (H0 B0 B1), (H0 B1 B0), (H0 B1 B1).
    destruct (A x); destruct (C y); simpl; field.
  }
  set (a0 := sgn (A B0)).
  set (a1 := sgn (A B1)).
  set (c0 := sgn (C B0)).
  set (c1 := sgn (C B1)).
  assert (S_eq : S B = inject_Z (a1 * c1 + a1 * c0 + a0 * c1 - a0 * c0)).
  { unfold S.
    rewrite (E_eq B1 B1).
    rewrite (E_eq B1 B0).
    rewrite (E_eq B0 B1).
    rewrite (E_eq B0 B0).
    reflexivity.
  }
  rewrite S_eq.
  unfold Qabs.
  destruct (Qle_bool 0 (inject_Z (a1 * c1 + a1 * c0 + a0 * c1 - a0 * c0)).
  - apply Qle_trans with (inject_Z 2).
    + apply inject_Z_le.
      assert (Hzz : Z.abs (a1 * c1 + a1 * c0 + a0 * c1 - a0 * c0) <= 2%Z).
      { unfold a0,a1,c0,c1.
        destruct a0; destruct a1; destruct c0; destruct c1; simpl; lia. }
      lia.
    + simpl; lra.
  - apply Qle_trans with (inject_Z 2).
    + apply inject_Z_le.
      assert (Hzz : Z.abs (a1 * c1 + a1 * c0 + a0 * c1 - a0 * c0) <= 2%Z).
      { destruct a0; destruct a1; destruct c0; destruct c1; simpl; lia. }
      lia.
    + simpl; lra.
Qed.

(* For general local, the bound holds by convexity *)
Theorem local_CHSH_bound : forall (B : Box), local B -> Qabs (S B) <= 2#1.
Proof.
  intros B Hlocal.
  destruct Hlocal as (p_lambda & p_A & p_B & Hpl_nonneg & Hpl_sum & HsumA & HsumB & Hdef).
  set (W := fun lambda a0 a1 c0 c1 =>
              p_lambda lambda * p_A a0 B0 lambda * p_A a1 B1 lambda * p_B c0 B0 lambda * p_B c1 B1 lambda).
  assert (HsumW :
            sum_bit (fun lambda =>
              sum_bit (fun a0 =>
                sum_bit (fun a1 =>
                  sum_bit (fun c0 =>
                    sum_bit (fun c1 => W lambda a0 a1 c0 c1))))) = 1#1).
  { unfold W.
    apply (Qeq_trans _ _ _).
    - rewrite <- (Qmult_1_l (sum_bit p_lambda)).
      apply Qeq_sym.
      unfold sum_bit.
      assert (Hstep: forall lambda,
                sum_bit (fun a0 =>
                  sum_bit (fun a1 =>
                    sum_bit (fun c0 =>
                      sum_bit (fun c1 =>
                        p_lambda lambda * p_A a0 B0 lambda * p_A a1 B1 lambda * p_B c0 B0 lambda * p_B c1 B1 lambda))))
              = p_lambda lambda).
      { intro lambda.
        unfold sum_bit2, sum_bit.
        repeat rewrite <- Qmult_assoc.
        rewrite <- (Qmult_assoc (p_lambda lambda) (sum_bit (fun a0 => p_A a0 B0 lambda))).
        rewrite <- (Qmult_assoc (p_lambda lambda) (sum_bit (fun a0 => p_A a0 B0 lambda) * sum_bit (fun a1 => p_A a1 B1 lambda))).
        repeat rewrite <- Qmult_assoc.
        now rewrite (HsumA B0 lambda), (HsumA B1 lambda), (HsumB B0 lambda), (HsumB B1 lambda).
      }
      unfold sum_bit.
      apply (Qeq_trans _ _ _).
      + apply (Qeq_trans _ _ _).
        * exact (Qeq_refl _).
        * apply (f_equal sum_bit (fun lambda => eq_refl _)).
      + apply (Qeq_trans _ _ _).
        * apply (Qeq_refl _).
        * apply (f_equal sum_bit (fun lambda => eq_refl _)).
  }
  clear HsumW.
  assert (Hdecomp : forall a b x y,
             B.(p) a b x y =
             sum_bit (fun lambda =>
               sum_bit (fun a0 =>
                 sum_bit (fun a1 =>
                   sum_bit (fun c0 =>
                     sum_bit (fun c1 =>
                       W lambda a0 a1 c0 c1 *
                       (if eqb (match x with B0 => a0 | B1 => a1 end) a then 1#1 else 0#1) *
                       (if eqb (match y with B0 => c0 | B1 => c1 end) b then 1#1 else 0#1))))))).
  { intros a b x y.
    unfold W.
    rewrite <- (Hdef a b x y).
    unfold sum_bit.
    assert (Hcol : forall lambda,
              sum_bit (fun a0 =>
                sum_bit (fun a1 =>
                  (p_A a0 B0 lambda * p_A a1 B1 lambda) *
                  (if eqb (match x with B0 => a0 | B1 => a1 end) a then 1#1 else 0#1)))
              = p_A a x lambda).
    { intro lambda.
      unfold sum_bit.
      destruct x; simpl.
      - rewrite (HsumA B1 lambda).
        unfold sum_bit.
        destruct a; simpl; reflexivity.
      - rewrite (HsumA B0 lambda).
        unfold sum_bit.
        destruct a; simpl; reflexivity.
    }
    assert (Hcol2 : forall lambda,
              sum_bit (fun c0 =>
                sum_bit (fun c1 =>
                  (p_B c0 B0 lambda * p_B c1 B1 lambda) *
                  (if eqb (match y with B0 => c0 | B1 => c1 end) b then 1#1 else 0#1)))
              = p_B b y lambda).
    { intro lambda.
      unfold sum_bit.
      destruct y; simpl.
      - rewrite (HsumB B1 lambda). unfold sum_bit. destruct b; simpl; reflexivity.
      - rewrite (HsumB B0 lambda). unfold sum_bit. destruct b; simpl; reflexivity.
    }
    unfold sum_bit.
    rewrite <- (Qmult_1_l (sum_bit (fun lambda => p_lambda lambda * p_A a x lambda * p_B b y lambda))).
    apply Qeq_trans with (sum_bit (fun lambda => p_lambda lambda * (sum_bit (fun a0 => sum_bit (fun a1 => p_A a0 B0 lambda * p_A a1 B1 lambda *
                            (if eqb (match x with B0 => a0 | B1 => a1 end) a then 1#1 else 0#1))) *
                            (sum_bit (fun c0 => sum_bit (fun c1 => p_B c0 B0 lambda * p_B c1 B1 lambda *
                            (if eqb (match y with B0 => c0 | B1 => c1 end) b then 1#1 else 0#1))))))).
    - apply (f_equal2 sum_bit); [apply (f_equal2 sum_bit); reflexivity|reflexivity].
    - apply (f_equal2 sum_bit).
      + apply (f_equal2 sum_bit).
        * intro lambda; rewrite <- (Qmult_assoc (p_lambda lambda)); apply f_equal2; [|reflexivity].
          -- apply f_equal2; [apply f_equal2|apply f_equal2]; reflexivity.
          -- reflexivity.
        * reflexivity.
      + reflexivity.
    - simpl.
      apply (f_equal2 sum_bit).
      + intro lambda; rewrite <- (Qmult_assoc (p_lambda lambda)).
        rewrite (Hcol lambda).
        reflexivity.
      + reflexivity.
    - simpl.
      apply (f_equal2 sum_bit).
      + intro lambda; rewrite <- (Qmult_assoc (p_lambda lambda)).
        rewrite (Hcol2 lambda).
        reflexivity.
      + reflexivity.
    - simpl.
      reflexivity.
  }
  assert (S_decomp : S B =
    sum_bit (fun lambda =>
      sum_bit (fun a0 =>
        sum_bit (fun a1 =>
          sum_bit (fun c0 =>
            sum_bit (fun c1 =>
              W lambda a0 a1 c0 c1 *
              inject_Z (sgn a1 * sgn c1 + sgn a1 * sgn c0 + sgn a0 * sgn c1 - sgn a0 * sgn c0)
            )))))).
  {
    unfold S, E.
    repeat (
      rewrite <- (Hdecomp B1 B1 B1 B1);
      rewrite <- (Hdecomp B1 B0 B1 B0);
      rewrite <- (Hdecomp B0 B1 B0 B1);
      rewrite <- (Hdecomp B0 B0 B0 B0)
    ).
    unfold sum_bit2, sum_bit.
    assert (forall lambda a0 a1 c0 c1,
      Qabs (inject_Z (sgn a1 * sgn c1 + sgn a1 * sgn c0 + sgn a0 * sgn c1 - sgn a0 * sgn c0)) <= 2#1).
    {
      intros. apply inject_Z_le.
      assert (H: Z.abs (sgn a1 * sgn c1 + sgn a1 * sgn c0 + sgn a0 * sgn c1 - sgn a0 * sgn c0) <= 2)%Z.
      { destruct (sgn a1); destruct (sgn a0); destruct (sgn c1); destruct (sgn c0); simpl; lia. }
      lia.
    }
    assert (Qabs (S B) <= 2#1).
    {
      rewrite S_decomp.
      assert (forall lambda a0 a1 c0 c1, 0#1 <= W lambda a0 a1 c0 c1) by (unfold W; repeat (apply Qmult_le_0_compat); try (apply Hpl_nonneg); try (apply HsumA || apply HsumB || apply (fun _ => B.(nonneg) _ _ _ _)); simpl; lra).
      assert (sum_bit (fun lambda =>
        sum_bit (fun a0 =>
          sum_bit (fun a1 =>
            sum_bit (fun c0 =>
              sum_bit (fun c1 => W lambda a0 a1 c0 c1))))) = 1#1) by (unfold W; rewrite <- (Qmult_1_l (sum_bit p_lambda)); apply Qeq_trans with (sum_bit (fun lambda => p_lambda lambda * 1#1)); [apply f_equal; reflexivity|apply (f_equal sum_bit); intro lambda; rewrite <- (Qmult_assoc (p_lambda lambda)); repeat (rewrite <- Qmult_assoc); rewrite (HsumA B0 lambda); rewrite (HsumA B1 lambda); rewrite (HsumB B0 lambda); rewrite (HsumB B1 lambda); simpl; field]).
      apply Qle_trans with (sum_bit (fun lambda =>
        sum_bit (fun a0 =>
          sum_bit (fun a1 =>
            sum_bit (fun c0 =>
              sum_bit (fun c1 => W lambda a0 a1 c0 c1 * 2#1)))))).
      - apply Qabs_sum_le; intros; try lra.
        apply Qle_trans with (Qabs (inject_Z (sgn a1 * sgn c1 + sgn a1 * sgn c0 + sgn a0 * sgn c1 - sgn a0 * sgn c0))); try lra.
        apply H.
      - rewrite <- Qmult_1_l.
        rewrite H0.
        simpl; field.
    }
    exact H0.
  }
  rewrite S_decomp.
  assert (forall lambda a0 a1 c0 c1, Qabs (inject_Z (sgn a1 * sgn c1 + sgn a1 * sgn c0 + sgn a0 * sgn c1 - sgn a0 * sgn c0)) <= 2#1).
  { intros. apply inject_Z_le.
    assert (H: Z.abs (sgn a1 * sgn c1 + sgn a1 * sgn c0 + sgn a0 * sgn c1 - sgn a0 * sgn c0) <= 2)%Z.
    { destruct (sgn a1); destruct (sgn a0); destruct (sgn c1); destruct (sgn c0); simpl; lia. }
    lia.
  }
  assert (forall lambda a0 a1 c0 c1, 0#1 <= W lambda a0 a1 c0 c1).
  { intros; unfold W; repeat (apply Qmult_le_0_compat); try (apply Hpl_nonneg); try (apply HsumA || apply HsumB || apply (fun _ => B.(nonneg) _ _ _ _)); simpl; lra. }
  assert (sum_bit (fun lambda =>
    sum_bit (fun a0 =>
      sum_bit (fun a1 =>
        sum_bit (fun c0 =>
          sum_bit (fun c1 => W lambda a0 a1 c0 c1))))) = 1#1).
  { unfold W.
    rewrite <- (Qmult_1_l (sum_bit p_lambda)).
    apply Qeq_trans with (sum_bit (fun lambda => p_lambda lambda * 1#1)); [apply f_equal; reflexivity|].
    apply (f_equal sum_bit); intro lambda.
    rewrite <- (Qmult_assoc (p_lambda lambda)).
    repeat (rewrite <- Qmult_assoc).
    rewrite (HsumA B0 lambda).
    rewrite (HsumA B1 lambda).
    rewrite (HsumB B0 lambda).
    rewrite (HsumB B1 lambda).
    simpl; field.
  }
  apply Qle_trans with (sum_bit (fun lambda =>
    sum_bit (fun a0 =>
      sum_bit (fun a1 =>
        sum_bit (fun c0 =>
          sum_bit (fun c1 => W lambda a0 a1 c0 c1 * 2#1)))))).
  - apply Qabs_sum_le; intros; try lra.
    apply Qle_trans with (Qabs (inject_Z (sgn a1 * sgn c1 + sgn a1 * sgn c0 + sgn a0 * sgn c1 - sgn a0 * sgn c0))); try lra.
    apply H.
  - rewrite <- Qmult_1_l.
    rewrite H0.
    simpl; field.
Qed.

(* PR-box construction with S=4 and no-signaling *)
Definition PR_p (a b x y : Bit) : Q :=
  if (eqb x B0 && eqb y B0) then
    if ((eqb a B1 && eqb b B0) || (eqb a B0 && eqb b B1)) then (1#2) else 0#1
  else
    if (eqb a b) then (1#2) else 0#1.

Lemma PR_norm : forall x y, sum_bit2 (fun a b => PR_p a b x y) = 1#1.
Proof.
  intros x y.
  unfold sum_bit2, sum_bit, PR_p.
  destruct x, y; simpl; field.
Qed.

Lemma PR_nonneg : forall a b x y, 0#1 <= PR_p a b x y.
Proof.
  intros a b x y.
  unfold PR_p.
  destruct (eqb x B0 && eqb y B0); destruct (eqb a b); unfold Qle; simpl; all: repeat (auto using Z.le_refl Z.le_0_1).
Qed.

Lemma PR_nosig_A : forall x y1 y2 a, sum_bit (fun b => PR_p a b x y1) = sum_bit (fun b => PR_p a b x y2).
Proof.
  intros x y1 y2 a.
  unfold sum_bit, PR_p.
  destruct a, x, y1, y2; simpl; field.
Qed.

Lemma PR_nosig_B : forall y x1 x2 b, sum_bit (fun a => PR_p a b x1 y) = sum_bit (fun a => PR_p a b x2 y).
Proof.
  intros y x1 x2 b.
  unfold sum_bit, PR_p.
  destruct b, y, x1, x2; simpl; field.
Qed.

Definition PR : Box := {|
  p := PR_p;
  norm := PR_norm;
  nonneg := PR_nonneg;
  nosig_A := PR_nosig_A;
  nosig_B := PR_nosig_B
|}.

Theorem PR_S : S PR = 4#1.
Proof.
  unfold S, E, PR.
  unfold sum_bit2, sum_bit.
  simpl.
  reflexivity.
Qed.

Theorem PR_not_local : ~ local PR.
Proof.
  intros Hlocal.
  apply local_CHSH_bound in Hlocal.
  unfold Qabs in Hlocal.
  rewrite PR_S in Hlocal.
  simpl in Hlocal.
  unfold Qle in Hlocal.
  simpl in Hlocal.
  lia.
Qed.

(* Quantum Tsirelson box: achieves S = 2 * sqrt 2, no-signaling, not local *)

(* Commented out due to missing trig lemmas *)
(*
Definition theta (x : Bit) : R :=
  match x with
  | B0 => 0%R
  | B1 => PI/4
  end.

Definition phi (y : Bit) : R :=
  match y with
  | B0 => PI/8
  | B1 => - (PI/8)
  end.

Definition QTsirelson_E (x y : Bit) : R :=
  - cos (theta x - phi y).

Definition QTsirelson_S : R :=
  QTsirelson_E B1 B1 + QTsirelson_E B1 B0 + QTsirelson_E B0 B1 - QTsirelson_E B0 B0.

Lemma QTsirelson_S_value : QTsirelson_S = 2 * sqrt 2.
Proof.
  unfold QTsirelson_S, QTsirelson_E, theta, phi.
  replace (PI/4 - (-PI/8)) with (3*PI/8)%R by field.
  replace (PI/4 - PI/8) with (PI/8)%R by field.
  replace (0 - (-PI/8)) with (PI/8)%R by field.
  replace (0 - PI/8) with (-PI/8)%R by field.
  rewrite cos_neg.
  rewrite cos_neg.
  (* S = -cos(3PI/8) - cos(PI/8) - cos(PI/8) + cos(3PI/8) = -2 cos(PI/8) + 2 cos(3PI/8) *)
  assert (cos_PI8 : cos (PI/8) = sqrt ((2 + sqrt 2)/2))%R by (apply cos_PI8_value).
  assert (cos_3PI8 : cos (3*PI/8) = sqrt ((2 - sqrt 2)/2))%R by (apply cos_3PI8_value).
  rewrite cos_PI8, cos_3PI8.
  (* S = -sqrt((2 - sqrt 2)/2) - sqrt((2 + sqrt 2)/2) - sqrt((2 + sqrt 2)/2) + sqrt((2 - sqrt 2)/2) *)
  (* = -2 * sqrt((2 + sqrt 2)/2) + 2 * sqrt((2 - sqrt 2)/2) *)
  replace (2 * sqrt ((2 - sqrt 2)/2) - 2 * sqrt ((2 + sqrt 2)/2))%R with (2 * sqrt 2)%R by (apply tsirelson_chsh_exact).
  reflexivity.
Qed.
*)
