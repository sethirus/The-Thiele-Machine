(** Helper lemmas for Cauchy-Schwarz *)

Lemma square_nonneg : forall (x : R), 0 <= x^2.
Proof.
  intro x.
  apply Rle_0_sqr.
Qed.

Lemma product_bound_pm1 :
  forall (a b : R),
    (a = -1 \/ a = 1) ->
    (b = -1 \/ b = 1) ->
    -1 <= a * b <= 1.
Proof.
  intros a b [Ha | Ha] [Hb | Hb]; subst;
    split; try lra; try (rewrite Rmult_1_r; lra); try (rewrite Rmult_opp_opp; lra).
Qed.

Lemma sum_n_nonneg :
  forall n f,
    (forall i, (i <= n)%nat -> 0 <= f i) ->
    0 <= sum_n n f.
Proof.
  induction n; intros f Hf.
  - simpl. apply Hf. lia.
  - simpl. apply Rplus_le_le_0_compat.
    + apply IHn. intros i Hi. apply Hf. lia.
    + apply Hf. lia.
Qed.

Lemma sum_n_split :
  forall n f g,
    sum_n n (fun i => f i + g i) = sum_n n f + sum_n n g.
Proof.
  induction n; intros f g.
  - simpl. lra.
  - simpl. rewrite IHn. lra.
Qed.

Lemma sum_n_mult_const :
  forall n c f,
    sum_n n (fun i => c * f i) = c * sum_n n f.
Proof.
  induction n; intros c f.
  - simpl. lra.
  - simpl. rewrite IHn. lra.
Qed.

(** Cauchy-Schwarz for finite sums with bounded terms *)
Lemma cauchy_schwarz_bounded :
  forall n (a b : nat -> R),
    (forall i, (i <= n)%nat -> -1 <= a i <= 1) ->
    (forall i, (i <= n)%nat -> -1 <= b i <= 1) ->
    (sum_n n (fun i => a i * b i))^2 <=
    (sum_n n (fun i => (a i)^2)) * (sum_n n (fun i => (b i)^2)).
Proof.
  intros n a b Ha Hb.
  (* For bounded terms |a|,|b| <= 1, we have |ab| <= 1 *)
  (* Standard Cauchy-Schwarz: (Σ a_i b_i)^2 <= (Σ a_i^2)(Σ b_i^2) *)
  (* This is a special case since a_i, b_i ∈ [-1,1] *)

  (* Key insight: (Σ a_i b_i)^2 = (a_0 b_0 + ... + a_n b_n)^2 *)
  (* Expand and bound each cross term *)

  admit. (* TO COMPLETE: Full Cauchy-Schwarz proof - requires ~80 lines of real analysis *)
Admitted.
