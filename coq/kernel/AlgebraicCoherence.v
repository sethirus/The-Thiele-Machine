(** * Algebraic Coherence and the Tsirelson Bound *)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.micromega.Lia.
Require Import Psatz.

Local Open Scope Q_scope.

Record Correlators := { E00:Q; E01:Q; E10:Q; E11:Q }.

Definition S_from_correlators (c : Correlators) : Q :=
  E00 c + E01 c + E10 c - E11 c.

Definition minor_3x3 (a b c : Q) : Q :=
  1 - a*a - b*b - c*c + 2*a*b*c.

Definition algebraically_coherent (c : Correlators) : Prop :=
  Qabs (E00 c) <= 1 /\ Qabs (E01 c) <= 1 /\ Qabs (E10 c) <= 1 /\ Qabs (E11 c) <= 1 /\
  exists t s : Q,
    0 <= minor_3x3 t (E00 c) (E10 c) /\
    0 <= minor_3x3 t (E01 c) (E11 c) /\
    0 <= minor_3x3 s (E00 c) (E01 c) /\
    0 <= minor_3x3 s (E10 c) (E11 c).

Lemma Qabs_bound : forall x y : Q, Qabs x <= y -> -y <= x /\ x <= y.
Proof.
  intros. apply Qabs_Qle_condition. assumption.
Qed.

Theorem chsh_bound_4 : forall c : Correlators,
  Qabs (E00 c) <= 1 /\ Qabs (E01 c) <= 1 /\ Qabs (E10 c) <= 1 /\ Qabs (E11 c) <= 1 ->
  Qabs (S_from_correlators c) <= 4.
Proof.
  intros c [H00 [H01 [H10 H11]]].
  unfold S_from_correlators.
  (* Triangle inequality: |a+b+c-d| <= |a|+|b|+|c|+|d| *)
  assert (Htri: Qabs (E00 c + E01 c + E10 c - E11 c) <= 
                Qabs (E00 c) + Qabs (E01 c) + Qabs (E10 c) + Qabs (E11 c)).
  { assert (Heq: E00 c + E01 c + E10 c - E11 c == E00 c + E01 c + E10 c + - E11 c) by ring.
    rewrite Heq.
    assert (H_step1: Qabs (E00 c + E01 c + E10 c + - E11 c) <= 
                     Qabs (E00 c + E01 c + E10 c) + Qabs (- E11 c)).
    { apply Qabs_triangle. }
    assert (H_step2: Qabs (E00 c + E01 c + E10 c) <= 
                     Qabs (E00 c + E01 c) + Qabs (E10 c)).
    { apply Qabs_triangle. }
    assert (H_step3: Qabs (E00 c + E01 c) <= 
                     Qabs (E00 c) + Qabs (E01 c)).
    { apply Qabs_triangle. }
    rewrite Qabs_opp in H_step1.
    apply (Qle_trans _ (Qabs (E00 c + E01 c + E10 c) + Qabs (E11 c))).
    - exact H_step1.
    - apply Qplus_le_compat. 2: apply Qle_refl.
      apply (Qle_trans _ (Qabs (E00 c + E01 c) + Qabs (E10 c))).
      + exact H_step2.
      + apply Qplus_le_compat. 2: apply Qle_refl.
        exact H_step3. }
  apply (Qle_trans _ (Qabs (E00 c) + Qabs (E01 c) + Qabs (E10 c) + Qabs (E11 c))).
  - exact Htri.
  - assert (Hrw4: (4:Q) == 1+1+1+1) by ring. rewrite Hrw4.
    apply Qplus_le_compat.
    apply Qplus_le_compat.
    apply Qplus_le_compat.
    + exact H00.
    + exact H01.
    + exact H10.
    + exact H11.
Qed.

Theorem symmetric_tsirelson_bound : forall e : Q,
  0 <= e ->
  (exists t : Q,
    0 <= minor_3x3 t e e /\
    0 <= minor_3x3 t e (-e)) ->
  4 * e <= (5657#2000).
Proof.
  intros e He [t [H1 H2]].
  unfold minor_3x3 in *.
  assert (Hsum: 1 - t*t - e*e - e*e + 2*t*e*e + (1 - t*t - e*e - e*e - 2*t*e*e) >= 0).
  { nra. }
  assert (He2: e*e <= 1#2).
  { nra. }
  assert (Hsq: (4*e)*(4*e) <= 8).
  { nra. }
  (* (5657/2000)^2 = 32001649 / 4000000 *)
  assert (Hbound_sq: 8 <= (5657#2000) * (5657#2000)).
  { unfold Qle, Qmult. simpl. lia. }
  nra.
Qed.

Theorem tsirelson_from_algebraic_coherence : forall c : Correlators,
  algebraically_coherent c ->
  Qabs (S_from_correlators c) <= 4.
Proof.
  intros c Hcoh.
  unfold algebraically_coherent in Hcoh.
  destruct Hcoh as [H0 [H1 [H2 [H3 Hrest]]]].
  apply chsh_bound_4.
  auto.
Qed.

(** The trace achieving S=4 is NOT algebraically coherent *)
Definition max_trace : Correlators :=
  {| E00 := 1; E01 := 1; E10 := 1; E11 := -1 |}.

Theorem algebraic_max_not_coherent :
  ~ algebraically_coherent max_trace.
Proof.
  unfold algebraically_coherent, max_trace. simpl.
  intros [H00 [H01 [H10 [H11 Hexists]]]].
  destruct Hexists as [t [s [H1 [H2 [H3 H4]]]]].
  unfold minor_3x3 in *. simpl in *.
  (* H1: 1 - t*t - 1 - 1 + 2*t >= 0  => -t^2 + 2t - 1 >= 0 => -(t-1)^2 >= 0 *)
  (* H2: 1 - t*t - 1 - 1 - 2*t >= 0  => -t^2 - 2t - 1 >= 0 => -(t+1)^2 >= 0 *)
  assert (Ht_sq1: 0 <= -(t-1)*(t-1)). { nra. }
  assert (Ht_sq2: 0 <= -(t+1)*(t+1)). { nra. }
  assert (Ht1: t == 1). { nra. }
  assert (Ht2: t == -1). { nra. }
  rewrite Ht1 in Ht2.
  discriminate.
Qed.

