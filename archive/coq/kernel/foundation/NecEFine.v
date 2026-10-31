(** NecEFine.v: the converse of fine_theorem is false.

    The book's Theorem "fine_theorem, one direction only" says a
    factorizable correlation has -2 <= S <= 2. The converse fails: a
    correlation table can have S = 0 and still not be factorizable,
    because a different relabelling of the same table scores 4.

    The definitions sum_n, is_factorizable and CHSH_from_correlations are
    the ones in kernel/quantum/MinorConstraints.v; nothing else is assumed.

    The table: E(x, y) = -1 at x = 1, y = 0 and 1 elsewhere, for all
    outcome indices. S = 1 + 1 - 1 - 1 = 0, inside [-2, 2]. Every
    factorizable table also has |E00 + E01 - E10 + E11| <= 2
    [nec_e_factorizable_variant_bound]; this one has 4.                  *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is real algebra about tables of correlations (Fine's theorem for the
   factorizable tables of MinorConstraints.v); no machine is involved. The
   link of the CHSH check to the abstract record lives in SmallChshLinks.v. *)

From Coq Require Import Arith Lia Reals Lra Psatz.
From Kernel Require Import MinorConstraints.
Local Open Scope R_scope.

Lemma nec_e_sum_n_lin : forall n f g a b,
  a * sum_n n f + b * sum_n n g = sum_n n (fun l => a * f l + b * g l).
Proof. induction n as [| n IH]; intros; simpl; [ring | rewrite <- IH; ring]. Qed.

Lemma nec_e_sum_n_4 : forall n f1 f2 f3 f4,
  sum_n n f1 + sum_n n f2 - sum_n n f3 + sum_n n f4
  = sum_n n (fun l => f1 l + f2 l - f3 l + f4 l).
Proof. induction n as [| n IH]; intros; simpl; [ring | rewrite <- IH; ring]. Qed.

Lemma nec_e_sum_n_ext : forall n f g,
  (forall l, (l <= n)%nat -> f l = g l) -> sum_n n f = sum_n n g.
Proof.
  induction n as [| n IH]; intros f g H; simpl; [apply H; lia |].
  rewrite (IH f g (fun l Hl => H l ltac:(lia))), (H (S n) ltac:(lia)). reflexivity.
Qed.

Lemma nec_e_sum_n_bound : forall n (p g : nat -> R),
  (forall l, (l <= n)%nat -> 0 <= p l) ->
  (forall l, (l <= n)%nat -> -2 * p l <= g l <= 2 * p l) ->
  -2 * sum_n n p <= sum_n n g <= 2 * sum_n n p.
Proof.
  induction n as [| n IH]; intros p g Hp Hg; simpl.
  - apply Hg. lia.
  - assert (H1 := IH p g (fun l Hl => Hp l ltac:(lia)) (fun l Hl => Hg l ltac:(lia))).
    assert (H2 := Hg (S n) ltac:(lia)). lra.
Qed.

(* Every factorizable table keeps the relabelled score in [-2, 2]. *)
Theorem nec_e_factorizable_variant_bound : forall E,
  is_factorizable E ->
  -2 <= E 0%nat 0%nat 0%nat 0%nat + E 0%nat 0%nat 0%nat 1%nat
        - E 0%nat 0%nat 1%nat 0%nat + E 0%nat 0%nat 1%nat 1%nat <= 2.
Proof.
  intros E [A [B [p [L [Hp [Hsum [HA [HB Hf]]]]]]]].
  rewrite !Hf.
  set (g := fun l => p l * (A 0%nat l * B 0%nat l + A 0%nat l * B 1%nat l
                          - A 1%nat l * B 0%nat l + A 1%nat l * B 1%nat l)).
  rewrite nec_e_sum_n_4.
  replace (sum_n L (fun l => p l * A 0%nat l * B 0%nat l + p l * A 0%nat l * B 1%nat l
                                  - p l * A 1%nat l * B 0%nat l + p l * A 1%nat l * B 1%nat l))
    with (sum_n L g)
    by (apply nec_e_sum_n_ext; intros l _; unfold g; ring).
  assert (Hb := nec_e_sum_n_bound L p g (fun l Hl => proj1 (Hp l Hl))
                  (fun l Hl => ltac:(unfold g;
                     destruct (HA 0%nat l) as [a0 | a0]; destruct (HA 1%nat l) as [a1 | a1];
                     destruct (HB 0%nat l) as [b0 | b0]; destruct (HB 1%nat l) as [b1 | b1];
                     rewrite a0, a1, b0, b1; pose proof (proj1 (Hp l Hl)); split; nra))).
  rewrite Hsum in Hb. lra.
Qed.

(* The table: -1 at (x, y) = (1, 0), 1 elsewhere. *)
Definition nec_e_relabelled_pr (a b x y : nat) : R :=
  match x, y with 1%nat, 0%nat => -1 | _, _ => 1 end.

(* The converse of fine_theorem is false: S = 0, and not factorizable. *)
Theorem nec_e_fine_converse_false :
  -2 <= CHSH_from_correlations nec_e_relabelled_pr <= 2 /\
  CHSH_from_correlations nec_e_relabelled_pr = 0 /\
  ~ is_factorizable nec_e_relabelled_pr.
Proof.
  unfold CHSH_from_correlations, nec_e_relabelled_pr. simpl.
  split; [lra |]. split; [lra |].
  intro H. apply nec_e_factorizable_variant_bound in H.
  unfold nec_e_relabelled_pr in H. simpl in H. lra.
Qed.

(* ================================================================= *)
(* Fine's theorem in correlation form: the converse holds once all     *)
(* eight CHSH inequalities and the four bounds |E| <= 1 are asked.     *)
(* ================================================================= *)

(* A table of four correlators, read at settings 0 and "anything else". *)
Definition nec_e_table (e00 e01 e10 e11 : R) (a b x y : nat) : R :=
  match x, y with
  | 0%nat, 0%nat => e00 | 0%nat, S _ => e01 | S _, 0%nat => e10 | S _, S _ => e11
  end.

Lemma nec_e_sum_n_comb : forall n f00 f01 f10 f11 c00 c01 c10 c11,
  c00 * sum_n n f00 + c01 * sum_n n f01 + c10 * sum_n n f10 + c11 * sum_n n f11
  = sum_n n (fun l => c00 * f00 l + c01 * f01 l + c10 * f10 l + c11 * f11 l).
Proof. induction n as [| n IH]; intros; simpl; [ring | rewrite <- IH; ring]. Qed.

Lemma nec_e_sum_n_boundK : forall n (p g : nat -> R) K,
  (forall l, (l <= n)%nat -> 0 <= p l) ->
  (forall l, (l <= n)%nat -> - K * p l <= g l <= K * p l) ->
  - K * sum_n n p <= sum_n n g <= K * sum_n n p.
Proof.
  induction n as [| n IH]; intros p g K Hp Hg; simpl.
  - apply Hg. lia.
  - assert (H1 := IH p g K (fun l Hl => Hp l ltac:(lia)) (fun l Hl => Hg l ltac:(lia))).
    assert (H2 := Hg (S n) ltac:(lia)). lra.
Qed.

Lemma nec_e_det_term : forall (pl c00 c01 c10 c11 K a0 a1 b0 b1 : R),
  0 <= pl ->
  - K <= c00 * (a0 * b0) + c01 * (a0 * b1) + c10 * (a1 * b0) + c11 * (a1 * b1) <= K ->
  - K * pl <= c00 * (pl * a0 * b0) + c01 * (pl * a0 * b1)
              + c10 * (pl * a1 * b0) + c11 * (pl * a1 * b1) <= K * pl.
Proof.
  intros pl c00 c01 c10 c11 K a0 a1 b0 b1 Hp [H1 H2].
  replace (c00 * (pl * a0 * b0) + c01 * (pl * a0 * b1) + c10 * (pl * a1 * b0) + c11 * (pl * a1 * b1))
    with (pl * (c00 * (a0 * b0) + c01 * (a0 * b1) + c10 * (a1 * b0) + c11 * (a1 * b1))) by ring.
  split; nra.
Qed.

(* Every linear bound that holds of all deterministic plans holds of a
   factorizable table. *)
Lemma nec_e_factorizable_linear : forall E c00 c01 c10 c11 K,
  (forall a0 a1 b0 b1 : R, (a0 = -1 \/ a0 = 1) -> (a1 = -1 \/ a1 = 1) ->
     (b0 = -1 \/ b0 = 1) -> (b1 = -1 \/ b1 = 1) ->
     - K <= c00 * (a0 * b0) + c01 * (a0 * b1) + c10 * (a1 * b0) + c11 * (a1 * b1) <= K) ->
  is_factorizable E ->
  - K <= c00 * E 0%nat 0%nat 0%nat 0%nat + c01 * E 0%nat 0%nat 0%nat 1%nat
         + c10 * E 0%nat 0%nat 1%nat 0%nat + c11 * E 0%nat 0%nat 1%nat 1%nat <= K.
Proof.
  intros E c00 c01 c10 c11 K Hdet [A [B [p [L [Hp [Hsum [HA [HB Hf]]]]]]]].
  rewrite !Hf, nec_e_sum_n_comb.
  assert (Hb := nec_e_sum_n_boundK L p
                  (fun l => c00 * (p l * A 0%nat l * B 0%nat l) + c01 * (p l * A 0%nat l * B 1%nat l)
                          + c10 * (p l * A 1%nat l * B 0%nat l) + c11 * (p l * A 1%nat l * B 1%nat l)) K
                  (fun l Hl => proj1 (Hp l Hl))
                  (fun l Hl => nec_e_det_term (p l) c00 c01 c10 c11 K
                                 (A 0%nat l) (A 1%nat l) (B 0%nat l) (B 1%nat l) (proj1 (Hp l Hl))
                                 (Hdet _ _ _ _ (HA 0%nat l) (HA 1%nat l) (HB 0%nat l) (HB 1%nat l)))).
  rewrite Hsum in Hb. lra.
Qed.

(* The sixteen inequalities: the four bounds |E| <= 1 and the eight CHSH
   inequalities, written as four two-sided ones. *)
Definition nec_e_fine_ineqs (e00 e01 e10 e11 : R) : Prop :=
  -1 <= e00 <= 1 /\ -1 <= e01 <= 1 /\ -1 <= e10 <= 1 /\ -1 <= e11 <= 1 /\
  -2 <= e00 + e01 + e10 - e11 <= 2 /\ -2 <= e00 + e01 - e10 + e11 <= 2 /\
  -2 <= e00 - e01 + e10 + e11 <= 2 /\ -2 <= - e00 + e01 + e10 + e11 <= 2.

Ltac nec_e_signs := intros a0 a1 b0 b1 [-> | ->] [-> | ->] [-> | ->] [-> | ->]; lra.

Lemma nec_e_fine_necessary : forall e00 e01 e10 e11,
  is_factorizable (nec_e_table e00 e01 e10 e11) -> nec_e_fine_ineqs e00 e01 e10 e11.
Proof.
  intros e00 e01 e10 e11 H.
  assert (G : forall c00 c01 c10 c11 K,
    (forall a0 a1 b0 b1 : R, (a0 = -1 \/ a0 = 1) -> (a1 = -1 \/ a1 = 1) ->
       (b0 = -1 \/ b0 = 1) -> (b1 = -1 \/ b1 = 1) ->
       - K <= c00 * (a0 * b0) + c01 * (a0 * b1) + c10 * (a1 * b0) + c11 * (a1 * b1) <= K) ->
    - K <= c00 * e00 + c01 * e01 + c10 * e10 + c11 * e11 <= K)
    by (intros c00 c01 c10 c11 K Hd; exact (nec_e_factorizable_linear _ c00 c01 c10 c11 K Hd H)).
  pose proof (G 1 0 0 0 1 ltac:(nec_e_signs)) as G1.
  pose proof (G 0 1 0 0 1 ltac:(nec_e_signs)) as G2.
  pose proof (G 0 0 1 0 1 ltac:(nec_e_signs)) as G3.
  pose proof (G 0 0 0 1 1 ltac:(nec_e_signs)) as G4.
  pose proof (G 1 1 1 (-1) 2 ltac:(nec_e_signs)) as G5.
  pose proof (G 1 1 (-1) 1 2 ltac:(nec_e_signs)) as G6.
  pose proof (G 1 (-1) 1 1 2 ltac:(nec_e_signs)) as G7.
  pose proof (G (-1) 1 1 1 2 ltac:(nec_e_signs)) as G8.
  unfold nec_e_fine_ineqs. repeat split; lra.
Qed.

(* The eight vertices: the four orthogonal sign vectors w1..w4 and their
   negatives, each a deterministic plan. *)
Definition nec_e_vA (x l : nat) : R :=
  let sg := if Nat.ltb l 4 then 1 else -1 in
  match x with
  | 0%nat => sg
  | _ => match Nat.modulo l 4 with 1%nat | 3%nat => - sg | _ => sg end
  end.

Definition nec_e_vB (y l : nat) : R :=
  match y with
  | 0%nat => 1
  | _ => match Nat.modulo l 4 with 2%nat | 3%nat => -1 | _ => 1 end
  end.

Definition nec_e_pos (y : R) : R := Rmax y 0.

Lemma nec_e_pos_nonneg : forall y, 0 <= nec_e_pos y.
Proof. intro y. unfold nec_e_pos. apply Rmax_r. Qed.

Lemma nec_e_pos_diff : forall y, nec_e_pos y - nec_e_pos (- y) = y.
Proof.
  intro y. unfold nec_e_pos, Rmax.
  destruct (Rle_dec y 0); destruct (Rle_dec (- y) 0); lra.
Qed.

Lemma nec_e_pos_sum : forall y, nec_e_pos y + nec_e_pos (- y) = Rabs y.
Proof.
  intro y. unfold nec_e_pos, Rmax, Rabs.
  destruct (Rle_dec y 0); destruct (Rle_dec (- y) 0); destruct (Rcase_abs y); lra.
Qed.

Lemma nec_e_abs_cases : forall y, (Rabs y = y /\ 0 <= y) \/ (Rabs y = - y /\ y < 0).
Proof.
  intro y. destruct (Rcase_abs y) as [h | h];
    [right; split; [apply Rabs_left, h | exact h] | left; split; [apply Rabs_right, h | lra]].
Qed.

Theorem nec_e_fine_iff : forall e00 e01 e10 e11,
  is_factorizable (nec_e_table e00 e01 e10 e11) <-> nec_e_fine_ineqs e00 e01 e10 e11.
Proof.
  intros e00 e01 e10 e11. split; [apply nec_e_fine_necessary |].
  intro H. unfold nec_e_fine_ineqs in H.
  set (y1 := (e00 + e01 + e10 + e11) / 4). set (y2 := (e00 + e01 - e10 - e11) / 4).
  set (y3 := (e00 - e01 + e10 - e11) / 4). set (y4 := (e00 - e01 - e10 + e11) / 4).
  assert (Habs : Rabs y1 + Rabs y2 + Rabs y3 + Rabs y4 <= 1).
  { destruct (nec_e_abs_cases y1) as [[A1 B1] | [A1 B1]];
    destruct (nec_e_abs_cases y2) as [[A2 B2] | [A2 B2]];
    destruct (nec_e_abs_cases y3) as [[A3 B3] | [A3 B3]];
    destruct (nec_e_abs_cases y4) as [[A4 B4] | [A4 B4]];
    rewrite A1, A2, A3, A4; unfold y1, y2, y3, y4 in *; lra. }
  set (r := 1 - (Rabs y1 + Rabs y2 + Rabs y3 + Rabs y4)).
  set (p := fun l : nat => match l with
            | 0%nat => nec_e_pos y1 + r / 8 | 1%nat => nec_e_pos y2 + r / 8
            | 2%nat => nec_e_pos y3 + r / 8 | 3%nat => nec_e_pos y4 + r / 8
            | 4%nat => nec_e_pos (- y1) + r / 8 | 5%nat => nec_e_pos (- y2) + r / 8
            | 6%nat => nec_e_pos (- y3) + r / 8 | _ => nec_e_pos (- y4) + r / 8 end).
  pose proof (nec_e_pos_diff y1) as D1. pose proof (nec_e_pos_diff y2) as D2.
  pose proof (nec_e_pos_diff y3) as D3. pose proof (nec_e_pos_diff y4) as D4.
  pose proof (nec_e_pos_sum y1) as S1. pose proof (nec_e_pos_sum y2) as S2.
  pose proof (nec_e_pos_sum y3) as S3. pose proof (nec_e_pos_sum y4) as S4.
  pose proof (nec_e_pos_nonneg y1) as P1. pose proof (nec_e_pos_nonneg y2) as P2.
  pose proof (nec_e_pos_nonneg y3) as P3. pose proof (nec_e_pos_nonneg y4) as P4.
  pose proof (nec_e_pos_nonneg (- y1)) as N1. pose proof (nec_e_pos_nonneg (- y2)) as N2.
  pose proof (nec_e_pos_nonneg (- y3)) as N3. pose proof (nec_e_pos_nonneg (- y4)) as N4.
  assert (Hr : 0 <= r) by (unfold r; lra).
  assert (Hrdef : r = 1 - (Rabs y1 + Rabs y2 + Rabs y3 + Rabs y4)) by reflexivity.
  exists nec_e_vA, nec_e_vB, p, 7%nat.
  split; [| split; [| split; [| split]]].
  - intros l Hl. pose proof (Rabs_pos y1). pose proof (Rabs_pos y2).
    pose proof (Rabs_pos y3). pose proof (Rabs_pos y4). unfold p.
    destruct l as [| [| [| [| [| [| [| [| l]]]]]]]]; cbv beta iota; split; lra.
  - simpl. unfold p. cbv beta iota. lra.
  - intros x l. unfold nec_e_vA.
    destruct (Nat.ltb l 4); destruct x as [| x];
      try (left; reflexivity); try (right; reflexivity);
      destruct (Nat.modulo l 4) as [| [| [| [| ]]]];
      first [left; reflexivity | right; reflexivity | left; ring | right; ring].
  - intros y l. unfold nec_e_vB. destruct y as [| y]; [right; reflexivity |].
    destruct (Nat.modulo l 4) as [| [| [| [| ]]]]; first [left; reflexivity | right; reflexivity].
  - intros a b x y. unfold nec_e_table.
    destruct x as [| x]; destruct y as [| y]; simpl; unfold y1, y2, y3, y4 in *; lra.
Qed.

Print Assumptions nec_e_factorizable_variant_bound.
Print Assumptions nec_e_fine_converse_false.
Print Assumptions nec_e_fine_necessary.
Print Assumptions nec_e_fine_iff.
