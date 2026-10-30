(* Chapter twenty, going faster costs more: for the walker, ln((1+v)/(1-v)) is never less than 2v, so heat
   times time is at least twice the distance squared. By the mean value theorem on
   f(x) = ln(1+x) - ln(1-x) - 2x, whose slope 2x^2/(1-x^2) is never negative and which is zero at zero.
   This uses Coq's standard real numbers. *)
From Coq Require Import Reals Lra.
Local Open Scope R_scope.

Definition f := (comp ln (fct_cte 1 + id) - comp ln (fct_cte 1 - id) - mult_real_fct 2 id)%F.
Definition f' (c : R) := / (1 + c) * (0 + 1) - / (1 - c) * (0 - 1) - 2 * 1.

Lemma f_deriv : forall c, -1 < c < 1 -> derivable_pt_lim f c (f' c).
Proof.
  intros c Hc. unfold f, f'.
  apply derivable_pt_lim_minus; [apply derivable_pt_lim_minus|].
  - apply derivable_pt_lim_comp.
    + apply derivable_pt_lim_plus; [apply derivable_pt_lim_const | apply derivable_pt_lim_id].
    + apply derivable_pt_lim_ln. unfold plus_fct, fct_cte, id. lra.
  - apply derivable_pt_lim_comp.
    + apply derivable_pt_lim_minus; [apply derivable_pt_lim_const | apply derivable_pt_lim_id].
    + apply derivable_pt_lim_ln. unfold minus_fct, fct_cte, id. lra.
  - apply derivable_pt_lim_scal. apply derivable_pt_lim_id.
Qed.

Lemma f'_nonneg : forall c, 0 <= c < 1 -> 0 <= f' c.
Proof.
  intros c Hc. unfold f'.
  replace (/ (1 + c) * (0 + 1) - / (1 - c) * (0 - 1) - 2 * 1) with (2 * (c * c) / ((1 + c) * (1 - c)))
    by (field; lra).
  apply Rmult_le_pos; [nra | left; apply Rinv_0_lt_compat; nra].
Qed.

Lemma f_at : forall x, -1 < x < 1 -> f x = ln (1 + x) - ln (1 - x) - 2 * x.
Proof. intros x Hx. unfold f, minus_fct, plus_fct, comp, fct_cte, id, mult_real_fct. reflexivity. Qed.

Theorem ln_ratio_ge_2v : forall v, 0 < v < 1 -> 2 * v <= ln ((1 + v) / (1 - v)).
Proof.
  intros v Hv.
  destruct (MVT_cor2 f f' 0 v ltac:(lra) (fun c Hc => f_deriv c ltac:(lra))) as [c [E Hc]].
  pose proof (f'_nonneg c ltac:(lra)) as P.
  rewrite (f_at v ltac:(lra)), (f_at 0 ltac:(lra)) in E.
  replace (1 + 0) with 1 in E by ring. replace (1 - 0) with 1 in E by ring. rewrite ln_1 in E.
  unfold Rdiv. rewrite ln_mult by (try apply Rinv_0_lt_compat; lra). rewrite ln_Rinv by lra.
  assert (0 <= f' c * (v - 0)) by (apply Rmult_le_pos; lra).
  lra.
Qed.

Definition heat (N v : R) := N * ln ((1 + v) / (1 - v)).
Definition time (N v : R) := N / v.

Theorem heat_time_twice : forall N v, 0 <= N -> 0 < v < 1 -> 2 * (N * N) <= heat N v * time N v.
Proof.
  intros N v HN Hv. unfold heat, time.
  pose proof (ln_ratio_ge_2v v Hv) as L.
  replace (N * ln ((1 + v) / (1 - v)) * (N / v)) with (N * N * (ln ((1 + v) / (1 - v)) / v)) by (field; lra).
  assert (2 <= ln ((1 + v) / (1 - v)) / v).
  { apply (Rmult_le_reg_r v); [lra|]. unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra. }
  assert (0 <= N * N) by nra. nra.
Qed.

Print Assumptions heat_time_twice.
