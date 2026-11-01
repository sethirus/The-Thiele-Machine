(** TsirelsonRepresentation: the correlators with a PSD completion are
    exactly the correlators of quantum strategies.

    - Every positive semidefinite matrix is a Gram matrix: its entries are
      the inner products of real vectors ([tr_gram]). The proof peels off
      the first row: a positive pivot leaves a PSD Schur complement, and a
      zero pivot forces a zero row.
    - Four real symmetric 8 x 8 matrices square to the identity and
      anticommute in pairs ([tr_gamma_clifford]); from unit vectors a, b in
      R^4 they build observables sum_m a_m gamma_m whose correlator in the
      maximally entangled state is the inner product a . b.
    - So every point of the completion set of ElliptopeCompletion.v is the
      correlator table of a quantum strategy with real amplitudes on two
      8-level systems ([tr_elliptope_quantum]); every strategy, with real or
      complex amplitudes in finite dimension, has its correlators in that set
      ([tr_quantum_elliptope], [tr_complex_elliptope]); and the two sets are
      equal ([tr_representation]). *)

(* SCOPE NOTE: standalone proof scope. This file stands on its own
   mathematics. No definition or theorem here mentions a certification
   system, a ledger or a machine step; it imports only the finite-sum,
   PSD and quantum-strategy files.

   The audit is waived rather than satisfied: satisfying it from inside would
   mean importing the kernel without using it, which asserts a bridge that is
   not here. The standalone boundary is stated here rather than inferred from
   an import. *)

From Coq Require Import List Reals Lra Psatz Lia Bool ZArith.
Import ListNotations.
From Kernel Require Import FiniteSums ConstructivePSD NPAMomentMatrix ElliptopeCompletion.
From Kernel Require Import QuantumStrategies QuantumStrategiesComplex.
Open Scope R_scope.

(** * Every PSD matrix is a Gram matrix *)

Definition tr_idx (n : nat) : list nat := seq 0 n.

Definition tr_qf (n : nat) (M : nat -> nat -> R) (v : nat -> R) : R :=
  sumL (tr_idx n) (fun i => sumL (tr_idx n) (fun j => v i * M i j * v j)).

Definition tr_psd (n : nat) (M : nat -> nat -> R) : Prop := forall v, 0 <= tr_qf n M v.

Definition tr_sym (n : nat) (M : nat -> nat -> R) : Prop :=
  forall i j, (i < n)%nat -> (j < n)%nat -> M i j = M j i.

Lemma tr_sum_S : forall n f, sumL (tr_idx (S n)) f = f 0%nat + sumL (tr_idx n) (fun i => f (S i)).
Proof.
  intros n f. unfold tr_idx. cbn [seq]. rewrite sumL_cons. f_equal.
  rewrite <- seq_shift, sumL_map. reflexivity.
Qed.

Lemma tr_in_idx : forall n i, In i (tr_idx n) <-> (i < n)%nat.
Proof. intros n i. unfold tr_idx. rewrite in_seq. lia. Qed.

Definition tr_shift (M : nat -> nat -> R) (i j : nat) : R := M (S i) (S j).

(** The quadratic form on n + 1 coordinates, split at coordinate 0. *)
Lemma tr_qf_S : forall n M v, tr_sym (S n) M ->
  tr_qf (S n) M v =
  v 0%nat * M 0%nat 0%nat * v 0%nat +
  2 * v 0%nat * sumL (tr_idx n) (fun j => M 0%nat (S j) * v (S j)) +
  tr_qf n (tr_shift M) (fun i => v (S i)).
Proof.
  intros n M v Hs. unfold tr_qf. rewrite tr_sum_S, tr_sum_S.
  transitivity (v 0%nat * M 0%nat 0%nat * v 0%nat +
    sumL (tr_idx n) (fun j => v 0%nat * M 0%nat (S j) * v (S j)) +
    (sumL (tr_idx n) (fun i => v (S i) * M (S i) 0%nat * v 0%nat) +
     sumL (tr_idx n) (fun i => sumL (tr_idx n) (fun j => v (S i) * M (S i) (S j) * v (S j))))).
  - f_equal. rewrite <- sumL_plus. apply sumL_ext. intros i _. rewrite tr_sum_S. reflexivity.
  - assert (E : sumL (tr_idx n) (fun i => v (S i) * M (S i) 0%nat * v 0%nat) =
                sumL (tr_idx n) (fun j => v 0%nat * M 0%nat (S j) * v (S j))).
    { apply sumL_ext. intros i Hi. apply tr_in_idx in Hi. rewrite (Hs (S i) 0%nat) by lia. ring. }
    rewrite E. unfold tr_shift.
    assert (E2 : sumL (tr_idx n) (fun j => v 0%nat * M 0%nat (S j) * v (S j)) =
                 v 0%nat * sumL (tr_idx n) (fun j => M 0%nat (S j) * v (S j))).
    { rewrite <- sumL_scale_l. apply sumL_ext. intros. ring. }
    rewrite E2. ring.
Qed.

Lemma tr_sym_shift : forall n M, tr_sym (S n) M -> tr_sym n (tr_shift M).
Proof. intros n M Hs i j Hi Hj. unfold tr_shift. apply Hs; lia. Qed.

Lemma tr_qf_zero : forall n M, tr_qf n M (fun _ => 0) = 0.
Proof.
  intros n M. unfold tr_qf. transitivity (sumL (tr_idx n) (fun _ : nat => 0)); [| apply sumL_zero].
  apply sumL_ext. intros i _. transitivity (sumL (tr_idx n) (fun _ : nat => 0)); [| apply sumL_zero].
  apply sumL_ext. intros. ring.
Qed.

Lemma tr_pivot_nonneg : forall n M, tr_sym (S n) M -> tr_psd (S n) M -> 0 <= M 0%nat 0%nat.
Proof.
  intros n M Hs Hp. pose proof (Hp (fun i => if Nat.eqb i 0 then 1 else 0)) as H.
  rewrite tr_qf_S in H by exact Hs. cbn [Nat.eqb] in H.
  rewrite tr_qf_zero in H.
  assert (Z : sumL (tr_idx n) (fun j => M 0%nat (S j) * 0) = 0).
  { transitivity (sumL (tr_idx n) (fun _ : nat => 0)); [| apply sumL_zero]. apply sumL_ext. intros. ring. }
  rewrite Z in H. lra.
Qed.

Lemma tr_restrict : forall n M, tr_sym (S n) M -> tr_psd (S n) M -> tr_psd n (tr_shift M).
Proof.
  intros n M Hs Hp v. pose proof (Hp (fun i => match i with 0%nat => 0 | S i' => v i' end)) as H.
  rewrite tr_qf_S in H by exact Hs. cbv beta iota in H.
  change (fun i : nat => v i) with v in H. lra.
Qed.

(** The point vector at coordinate j. *)
Definition tr_e (j : nat) (i : nat) : R := if Nat.eqb i j then 1 else 0.

Lemma tr_sum_e : forall n j f, (j < n)%nat ->
  sumL (tr_idx n) (fun i => f i * tr_e j i) = f j.
Proof.
  intros n j f Hj.
  transitivity (sumL (tr_idx n) (fun i => (if Nat.eq_dec j i then 1 else 0) * f i)).
  - apply sumL_ext. intros i _. unfold tr_e.
    destruct (Nat.eq_dec j i) as [<- | Hne].
    + rewrite Nat.eqb_refl. ring.
    + replace (Nat.eqb i j) with false by (symmetry; apply Nat.eqb_neq; lia). ring.
  - apply sumL_delta. apply seq_NoDup. apply tr_in_idx. exact Hj.
Qed.

Lemma tr_qf_e : forall n M j, (j < n)%nat -> tr_qf n M (tr_e j) = M j j.
Proof.
  intros n M j Hj. unfold tr_qf.
  transitivity (sumL (tr_idx n) (fun i => (M i j) * tr_e j i)).
  - apply sumL_ext. intros i _.
    transitivity (sumL (tr_idx n) (fun k => (tr_e j i * M i k) * tr_e j k)).
    + apply sumL_ext. intros. ring.
    + rewrite (tr_sum_e n j (fun k => tr_e j i * M i k) Hj). unfold tr_e.
      destruct (Nat.eqb i j); ring.
  - apply (tr_sum_e n j (fun i => M i j) Hj).
Qed.

(** A zero pivot forces a zero row. *)
Lemma tr_zero_pivot_row : forall n M, tr_sym (S n) M -> tr_psd (S n) M -> M 0%nat 0%nat = 0 ->
  forall j, (j < n)%nat -> M 0%nat (S j) = 0.
Proof.
  intros n M Hs Hp H0 j Hj.
  set (c := M 0%nat (S j)). set (d := M (S j) (S j)).
  assert (Hq : forall t, 0 <= 2 * t * c + d).
  { intro t. pose proof (Hp (fun i => match i with 0%nat => t | S i' => tr_e j i' end)) as H.
    rewrite tr_qf_S in H by exact Hs. cbv beta iota in H.
    rewrite H0, (tr_sum_e n j (fun k => M 0%nat (S k)) Hj) in H.
    change (fun i : nat => tr_e j i) with (tr_e j) in H.
    rewrite (tr_qf_e n (tr_shift M) j Hj) in H. unfold tr_shift in H. fold c d in H. lra. }
  destruct (Req_dec c 0) as [Hc | Hc]; [exact Hc |].
  exfalso. pose proof (Hq (- (d + 1) / (2 * c))) as H.
  assert (E : 2 * (- (d + 1) / (2 * c)) * c + d = -1) by (field; exact Hc).
  lra.
Qed.

(** A positive pivot leaves a PSD Schur complement. *)
Definition tr_schur (M : nat -> nat -> R) (i j : nat) : R :=
  M (S i) (S j) - M (S i) 0%nat * M (S j) 0%nat / M 0%nat 0%nat.

Lemma tr_schur_psd : forall n M, tr_sym (S n) M -> tr_psd (S n) M -> 0 < M 0%nat 0%nat ->
  tr_psd n (tr_schur M).
Proof.
  intros n M Hs Hp Hd v.
  set (d := M 0%nat 0%nat) in *.
  set (c := sumL (tr_idx n) (fun j => M 0%nat (S j) * v j)).
  pose proof (Hp (fun i => match i with 0%nat => - c / d | S i' => v i' end)) as H.
  rewrite tr_qf_S in H by exact Hs. cbv beta iota in H. fold d c in H.
  change (fun i : nat => v i) with v in H.
  assert (E : tr_qf n (tr_schur M) v = tr_qf n (tr_shift M) v - c * c / d).
  { unfold tr_qf, tr_schur, tr_shift.
    transitivity (sumL (tr_idx n) (fun i => sumL (tr_idx n) (fun j => v i * M (S i) (S j) * v j)) -
                  sumL (tr_idx n) (fun i => sumL (tr_idx n) (fun j =>
                    (M 0%nat (S i) * v i) * (M 0%nat (S j) * v j) / d))).
    - rewrite <- sumL_minus. apply sumL_ext. intros i Hi. rewrite <- sumL_minus.
      apply sumL_ext. intros j Hj. apply tr_in_idx in Hi. apply tr_in_idx in Hj.
      rewrite (Hs (S i) 0%nat), (Hs (S j) 0%nat) by lia. unfold d in *. field. lra.
    - f_equal. unfold c. rewrite sumL_mult. unfold Rdiv. rewrite <- sumL_scale_r.
      apply sumL_ext. intros i _. rewrite <- sumL_scale_r. reflexivity. }
  rewrite E.
  assert (E2 : - c / d * d * (- c / d) + 2 * (- c / d) * c = - (c * c / d)) by (field; lra).
  lra.
Qed.

Theorem tr_gram : forall n M, tr_sym n M -> tr_psd n M ->
  exists u : nat -> nat -> R, forall i j, (i < n)%nat -> (j < n)%nat ->
    sumL (tr_idx n) (fun k => u i k * u j k) = M i j.
Proof.
  induction n as [| n IH]; intros M Hs Hp.
  - exists (fun _ _ => 0). intros i j Hi. lia.
  - pose proof (tr_pivot_nonneg n M Hs Hp) as Hd0.
    destruct (Rle_lt_or_eq_dec 0 (M 0%nat 0%nat) Hd0) as [Hd | Hd].
    + (* positive pivot *)
      set (r := sqrt (M 0%nat 0%nat)).
      assert (Hr : r * r = M 0%nat 0%nat) by (apply sqrt_sqrt; lra).
      assert (Hr0 : r <> 0) by (intro Z; rewrite Z in Hr; lra).
      assert (Hss : tr_sym n (tr_schur M)).
      { intros i j Hi Hj. unfold tr_schur. rewrite (Hs (S i) (S j)) by lia. rewrite (Rmult_comm (M (S i) 0%nat) (M (S j) 0%nat)). reflexivity. }
      destruct (IH (tr_schur M) Hss (tr_schur_psd n M Hs Hp Hd)) as [u' Hu'].
      exists (fun i k => match i, k with
                    | 0%nat, 0%nat => r
                    | 0%nat, S _ => 0
                    | S i', 0%nat => M (S i') 0%nat / r
                    | S i', S k' => u' i' k'
                    end).
      intros i j Hi Hj. rewrite tr_sum_S.
      destruct i as [| i]; destruct j as [| j].
      * transitivity (r * r + 0); [f_equal | lra].
        transitivity (sumL (tr_idx n) (fun _ : nat => 0)); [| apply sumL_zero].
        apply sumL_ext. intros. ring.
      * rewrite (Hs 0%nat (S j)) by lia.
        transitivity (M (S j) 0%nat + 0); [| ring]. f_equal; [field; exact Hr0 |].
        transitivity (sumL (tr_idx n) (fun _ : nat => 0)); [| apply sumL_zero].
        apply sumL_ext. intros. ring.
      * transitivity (M (S i) 0%nat + 0); [| ring]. f_equal; [field; exact Hr0 |].
        transitivity (sumL (tr_idx n) (fun _ : nat => 0)); [| apply sumL_zero].
        apply sumL_ext. intros. ring.
      * rewrite (Hu' i j) by lia. unfold tr_schur. rewrite <- Hr. field. exact Hr0.
    + (* zero pivot *)
      assert (Hrow := tr_zero_pivot_row n M Hs Hp (eq_sym Hd)).
      destruct (IH (tr_shift M) (tr_sym_shift n M Hs) (tr_restrict n M Hs Hp)) as [u' Hu'].
      exists (fun i k => match i, k with
                    | S i', S k' => u' i' k'
                    | _, _ => 0
                    end).
      intros i j Hi Hj. rewrite tr_sum_S.
      destruct i as [| i]; destruct j as [| j].
      * rewrite <- Hd. transitivity (0 + 0); [f_equal; [ring |] | ring].
        transitivity (sumL (tr_idx n) (fun _ : nat => 0)); [| apply sumL_zero].
        apply sumL_ext. intros. ring.
      * rewrite (Hrow j) by lia. transitivity (0 + 0); [f_equal; [ring |] | ring].
        transitivity (sumL (tr_idx n) (fun _ : nat => 0)); [| apply sumL_zero].
        apply sumL_ext. intros. ring.
      * rewrite (Hs (S i) 0%nat), (Hrow i) by lia. transitivity (0 + 0); [f_equal; [ring |] | ring].
        transitivity (sumL (tr_idx n) (fun _ : nat => 0)); [| apply sumL_zero].
        apply sumL_ext. intros. ring.
      * rewrite (Hu' i j) by lia. unfold tr_shift. ring.
Qed.

(** * Four anticommuting real symmetric involutions on eight levels *)

(** The real 2 x 2 matrices X = [[0,1],[1,0]], Z = [[1,0],[0,-1]],
    Y = [[0,1],[-1,0]] and the identity, over the integers. *)
Definition tr_X (b c : bool) : Z := if Bool.eqb b c then 0 else 1.
Definition tr_Z (b c : bool) : Z := if Bool.eqb b c then (if b then -1 else 1) else 0.
Definition tr_Y (b c : bool) : Z := if Bool.eqb b c then 0 else (if b then -1 else 1).
Definition tr_I (b c : bool) : Z := if Bool.eqb b c then 1 else 0.

(** An index below 8 is three bits; gamma_m is a threefold tensor product:
    X (x) 1 (x) 1, Z (x) 1 (x) 1, Y (x) Y (x) X and Y (x) Y (x) Z. *)
Definition tr_gammaZ (m i k : nat) : Z :=
  let f2 := fun (g : bool -> bool -> Z) => g (Nat.testbit i 2) (Nat.testbit k 2) in
  let f1 := fun (g : bool -> bool -> Z) => g (Nat.testbit i 1) (Nat.testbit k 1) in
  let f0 := fun (g : bool -> bool -> Z) => g (Nat.testbit i 0) (Nat.testbit k 0) in
  match m with
  | 0%nat => (f2 tr_X * f1 tr_I * f0 tr_I)%Z
  | 1%nat => (f2 tr_Z * f1 tr_I * f0 tr_I)%Z
  | 2%nat => (f2 tr_Y * f1 tr_Y * f0 tr_X)%Z
  | _ => (f2 tr_Y * f1 tr_Y * f0 tr_Z)%Z
  end.

Definition tr_sumZ (l : list nat) (f : nat -> Z) : Z := fold_right (fun x acc => (f x + acc)%Z) 0%Z l.

Lemma tr_sumL_IZR : forall l f, sumL l (fun k => IZR (f k)) = IZR (tr_sumZ l f).
Proof.
  intros l f. induction l as [| x l IH]; [reflexivity |].
  rewrite sumL_cons, IH. simpl. rewrite plus_IZR. reflexivity.
Qed.

Definition tr_d (a b : nat) : Z := if Nat.eqb a b then 1%Z else 0%Z.

(** The three finite checks, computed. *)
Definition tr_check_sym : bool :=
  forallb (fun m => forallb (fun i => forallb (fun k =>
    Z.eqb (tr_gammaZ m i k) (tr_gammaZ m k i)) (tr_idx 8)) (tr_idx 8)) (tr_idx 4).

Definition tr_check_anti : bool :=
  forallb (fun m => forallb (fun n => forallb (fun i => forallb (fun j =>
    Z.eqb (tr_sumZ (tr_idx 8) (fun k => (tr_gammaZ m i k * tr_gammaZ n k j)%Z) +
           tr_sumZ (tr_idx 8) (fun k => (tr_gammaZ n i k * tr_gammaZ m k j)%Z))%Z
          (2 * tr_d m n * tr_d i j)%Z) (tr_idx 8)) (tr_idx 8)) (tr_idx 4)) (tr_idx 4).

Definition tr_check_trace : bool :=
  forallb (fun m => forallb (fun n =>
    Z.eqb (tr_sumZ (tr_idx 8) (fun i => tr_sumZ (tr_idx 8) (fun k => (tr_gammaZ m i k * tr_gammaZ n i k)%Z)))
          (8 * tr_d m n)%Z) (tr_idx 4)) (tr_idx 4).

Lemma tr_checks : tr_check_sym = true /\ tr_check_anti = true /\ tr_check_trace = true.
Proof. vm_compute. auto. Qed.

Lemma tr_forallb_idx : forall n (p : nat -> bool), forallb p (tr_idx n) = true ->
  forall i, (i < n)%nat -> p i = true.
Proof. intros n p H i Hi. rewrite forallb_forall in H. apply H. apply tr_in_idx. exact Hi. Qed.

Definition tr_gamma (m i k : nat) : R := IZR (tr_gammaZ m i k).

Lemma tr_gammaZ_sym : forall m i k, tr_gammaZ m i k = tr_gammaZ m k i.
Proof.
  intros m i k. unfold tr_gammaZ.
  destruct (Nat.testbit i 0), (Nat.testbit i 1), (Nat.testbit i 2),
           (Nat.testbit k 0), (Nat.testbit k 1), (Nat.testbit k 2);
  destruct m as [| [| [| m]]]; reflexivity.
Qed.

Lemma tr_gamma_sym : forall m i k, tr_gamma m i k = tr_gamma m k i.
Proof. intros. unfold tr_gamma. rewrite tr_gammaZ_sym. reflexivity. Qed.

Definition tr_dR (a b : nat) : R := if Nat.eqb a b then 1 else 0.

(** Clifford relations: gamma_m gamma_n + gamma_n gamma_m = 2 delta_mn. *)
Theorem tr_gamma_clifford : forall m n i j, (m < 4)%nat -> (n < 4)%nat -> (i < 8)%nat -> (j < 8)%nat ->
  sumL (tr_idx 8) (fun k => tr_gamma m i k * tr_gamma n k j) +
  sumL (tr_idx 8) (fun k => tr_gamma n i k * tr_gamma m k j) = 2 * tr_dR m n * tr_dR i j.
Proof.
  intros m n i j Hm Hn Hi Hj. destruct tr_checks as [_ [H _]].
  pose proof (tr_forallb_idx _ _ (tr_forallb_idx _ _ (tr_forallb_idx _ _
    (tr_forallb_idx _ _ H m Hm) n Hn) i Hi) j Hj) as E.
  apply Z.eqb_eq in E. unfold tr_gamma.
  transitivity (IZR (tr_sumZ (tr_idx 8) (fun k => (tr_gammaZ m i k * tr_gammaZ n k j)%Z) +
                     tr_sumZ (tr_idx 8) (fun k => (tr_gammaZ n i k * tr_gammaZ m k j)%Z))%Z).
  - rewrite plus_IZR, <- !tr_sumL_IZR. f_equal; apply sumL_ext; intros; rewrite mult_IZR; reflexivity.
  - rewrite E, !mult_IZR. unfold tr_d, tr_dR. destruct (Nat.eqb m n), (Nat.eqb i j); reflexivity.
Qed.

Theorem tr_gamma_trace : forall m n, (m < 4)%nat -> (n < 4)%nat ->
  sumL (tr_idx 8) (fun i => sumL (tr_idx 8) (fun k => tr_gamma m i k * tr_gamma n i k)) = 8 * tr_dR m n.
Proof.
  intros m n Hm Hn. destruct tr_checks as [_ [_ H]].
  pose proof (tr_forallb_idx _ _ (tr_forallb_idx _ _ H m Hm) n Hn) as E.
  apply Z.eqb_eq in E. unfold tr_gamma.
  transitivity (IZR (tr_sumZ (tr_idx 8) (fun i => tr_sumZ (tr_idx 8) (fun k => (tr_gammaZ m i k * tr_gammaZ n i k)%Z)))).
  - rewrite <- tr_sumL_IZR. apply sumL_ext. intros i _. rewrite <- tr_sumL_IZR.
    apply sumL_ext. intros. rewrite mult_IZR. reflexivity.
  - rewrite E, mult_IZR. unfold tr_d, tr_dR. destruct (Nat.eqb m n); reflexivity.
Qed.

(** * The strategy built from four unit vectors *)

Definition tr_r : R := / sqrt 8.

Lemma tr_r_sq : tr_r * tr_r = / 8.
Proof. unfold tr_r. rewrite <- Rinv_mult. rewrite sqrt_sqrt by lra. reflexivity. Qed.

(** The maximally entangled state on two 8-level systems. *)
Definition tr_psi (i j : nat) : R := tr_r * tr_e i j.

(** The observable sum_m a_m gamma_m. *)
Definition tr_obs (a : nat -> R) (i k : nat) : R := sumL (tr_idx 4) (fun m => a m * tr_gamma m i k).

Definition tr_unitv (a : nat -> R) : Prop := sumL (tr_idx 4) (fun m => a m * a m) = 1.

Definition tr_inner (a b : nat -> R) : R := sumL (tr_idx 4) (fun m => a m * b m).

Lemma tr_e_refl : forall i, tr_e i i = 1.
Proof. intro i. unfold tr_e. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma tr_obs_square : forall a i j, tr_unitv a -> (i < 8)%nat -> (j < 8)%nat ->
  sumL (tr_idx 8) (fun k => tr_obs a i k * tr_obs a k j) = tr_dR i j.
Proof.
  intros a i j Ha Hi Hj. unfold tr_obs.
  set (P := fun m n => sumL (tr_idx 8) (fun k => tr_gamma m i k * tr_gamma n k j)).
  set (T := sumL (tr_idx 4) (fun m => sumL (tr_idx 4) (fun n => a m * a n * P m n))).
  assert (E1 : sumL (tr_idx 8) (fun k => sumL (tr_idx 4) (fun m => a m * tr_gamma m i k) *
                                         sumL (tr_idx 4) (fun n => a n * tr_gamma n k j)) = T).
  { transitivity (sumL (tr_idx 8) (fun k => sumL (tr_idx 4) (fun m => sumL (tr_idx 4) (fun n =>
      a m * tr_gamma m i k * (a n * tr_gamma n k j))))).
    { apply sumL_ext. intros k _. apply sumL_mult. }
    etransitivity. { apply sumL_swap. }
    unfold T. apply sumL_ext. intros m _.
    etransitivity. { apply sumL_swap. }
    apply sumL_ext. intros n _. unfold P. rewrite <- sumL_scale_l. apply sumL_ext. intros. ring. }
  assert (E2 : T = sumL (tr_idx 4) (fun m => sumL (tr_idx 4) (fun n => a m * a n * P n m))).
  { unfold T. etransitivity. { apply sumL_swap. }
    apply sumL_ext. intros. apply sumL_ext. intros. ring. }
  assert (E3 : T + T = 2 * tr_dR i j).
  { rewrite E2 at 2. unfold T. rewrite <- sumL_plus.
    transitivity (sumL (tr_idx 4) (fun m => 2 * tr_dR i j * (a m * a m))).
    - apply sumL_ext. intros m Hm. apply tr_in_idx in Hm. rewrite <- sumL_plus.
      transitivity (sumL (tr_idx 4) (fun n => (2 * tr_dR i j * a m * a n) * tr_e m n)).
      + apply sumL_ext. intros n Hn. apply tr_in_idx in Hn.
        transitivity (a m * a n * (P m n + P n m)); [ring |].
        unfold P. rewrite (tr_gamma_clifford m n i j Hm Hn Hi Hj).
        unfold tr_dR, tr_e. destruct (Nat.eqb_spec m n), (Nat.eqb_spec n m); try lia; ring.
      + rewrite (tr_sum_e 4 m (fun n => 2 * tr_dR i j * a m * a n) Hm). ring.
    - rewrite sumL_scale_l, Ha. ring. }
  rewrite E1. lra.
Qed.

Lemma tr_obs_valid : forall a, tr_unitv a -> qs_obsI nat Nat.eq_dec (tr_idx 8) (tr_obs a).
Proof.
  intros a Ha. split.
  - intros i k. unfold tr_obs. apply sumL_ext. intros. rewrite tr_gamma_sym. reflexivity.
  - intros i m Hi Hm. apply tr_in_idx in Hi. apply tr_in_idx in Hm.
    rewrite (tr_obs_square a i m Ha Hi Hm). unfold tr_dR, qs_deltaI.
    destruct (Nat.eqb_spec i m), (Nat.eq_dec i m); try lia; reflexivity.
Qed.

Lemma tr_obs_validJ : forall a, tr_unitv a -> qs_obsJ nat Nat.eq_dec (tr_idx 8) (tr_obs a).
Proof.
  intros a Ha. destruct (tr_obs_valid a Ha) as [H1 H2]. split; [exact H1 |].
  intros j m Hj Hm. rewrite (H2 j m Hj Hm). unfold qs_deltaI, qs_deltaJ. reflexivity.
Qed.

Lemma tr_psi_unit : qs_unit nat nat (tr_idx 8) (tr_idx 8) tr_psi.
Proof.
  unfold qs_unit.
  transitivity (sumL (tr_idx 8) (fun _ : nat => tr_r * tr_r)).
  - apply sumL_ext. intros i Hi. apply tr_in_idx in Hi.
    transitivity (sumL (tr_idx 8) (fun j => (tr_r * tr_r * tr_e i j) * tr_e i j)).
    + apply sumL_ext. intros. unfold tr_psi. ring.
    + rewrite (tr_sum_e 8 i (fun j => tr_r * tr_r * tr_e i j) Hi), tr_e_refl. ring.
  - pose proof tr_r_sq. unfold tr_idx. simpl. lra.
Qed.

(** In the maximally entangled state the correlator of sum_m a_m gamma_m
    and sum_m b_m gamma_m is the inner product a . b. *)
Lemma tr_dR_e : forall m n, tr_dR m n = tr_e m n.
Proof.
  intros m n. unfold tr_dR, tr_e. destruct (Nat.eqb_spec m n), (Nat.eqb_spec n m); try lia; reflexivity.
Qed.

Lemma tr_obs_pair : forall a b,
  sumL (tr_idx 8) (fun i => sumL (tr_idx 8) (fun k => tr_obs a i k * tr_obs b i k)) = 8 * tr_inner a b.
Proof.
  intros a b. unfold tr_obs.
  transitivity (sumL (tr_idx 8) (fun i => sumL (tr_idx 8) (fun k =>
    sumL (tr_idx 4) (fun m => sumL (tr_idx 4) (fun n =>
      a m * b n * (tr_gamma m i k * tr_gamma n i k)))))).
  { apply sumL_ext. intros i _. apply sumL_ext. intros k _. rewrite sumL_mult.
    apply sumL_ext. intros. apply sumL_ext. intros. ring. }
  transitivity (sumL (tr_idx 4) (fun m => sumL (tr_idx 4) (fun n =>
    a m * b n * sumL (tr_idx 8) (fun i => sumL (tr_idx 8) (fun k => tr_gamma m i k * tr_gamma n i k))))).
  { etransitivity.
    { apply sumL_ext. intros i _. etransitivity. { apply sumL_swap. }
      apply sumL_ext. intros m _. apply sumL_swap. }
    etransitivity. { apply sumL_swap. }
    apply sumL_ext. intros m _. etransitivity. { apply sumL_swap. }
    apply sumL_ext. intros n _. rewrite <- sumL_scale_l. apply sumL_ext. intros i _.
    rewrite <- sumL_scale_l. reflexivity. }
  transitivity (sumL (tr_idx 4) (fun m => 8 * (a m * b m))).
  - apply sumL_ext. intros m Hm. apply tr_in_idx in Hm.
    transitivity (sumL (tr_idx 4) (fun n => (8 * a m * b n) * tr_e m n)).
    + apply sumL_ext. intros n Hn. apply tr_in_idx in Hn.
      rewrite (tr_gamma_trace m n Hm Hn), tr_dR_e. ring.
    + rewrite (tr_sum_e 4 m (fun n => 8 * a m * b n) Hm). ring.
  - unfold tr_inner. apply sumL_scale_l.
Qed.

(** In the maximally entangled state the correlator of sum_m a_m gamma_m
    and sum_m b_m gamma_m is the inner product a . b. *)
Theorem tr_corr_inner : forall a b,
  qs_corr nat nat (tr_idx 8) (tr_idx 8) tr_psi (tr_obs a) (tr_obs b) = tr_inner a b.
Proof.
  intros a b. unfold qs_corr.
  transitivity (sumL (tr_idx 8) (fun i => sumL (tr_idx 8) (fun k =>
    tr_r * tr_r * (tr_obs a i k * tr_obs b i k)))).
  - apply sumL_ext. intros i Hi. apply tr_in_idx in Hi.
    transitivity (sumL (tr_idx 8) (fun j =>
      (tr_r * sumL (tr_idx 8) (fun k => sumL (tr_idx 8) (fun l =>
         tr_obs a i k * tr_obs b j l * tr_psi k l))) * tr_e i j)).
    + apply sumL_ext. intros j _.
      transitivity ((tr_r * tr_e i j) * sumL (tr_idx 8) (fun k => sumL (tr_idx 8) (fun l =>
         tr_obs a i k * tr_obs b j l * tr_psi k l))); [| ring].
      rewrite <- sumL_scale_l. apply sumL_ext. intros k _.
      rewrite <- sumL_scale_l. apply sumL_ext. intros l _. unfold tr_psi. ring.
    + rewrite (tr_sum_e 8 i (fun j => tr_r * sumL (tr_idx 8) (fun k => sumL (tr_idx 8) (fun l =>
         tr_obs a i k * tr_obs b j l * tr_psi k l))) Hi).
      rewrite <- sumL_scale_l. apply sumL_ext. intros k Hk. apply tr_in_idx in Hk.
      transitivity (tr_r * sumL (tr_idx 8) (fun l => (tr_r * tr_obs a i k * tr_obs b i l) * tr_e k l)).
      * f_equal. apply sumL_ext. intros. unfold tr_psi. ring.
      * rewrite (tr_sum_e 8 k (fun l => tr_r * tr_obs a i k * tr_obs b i l) Hk). ring.
  - transitivity (tr_r * tr_r * sumL (tr_idx 8) (fun i => sumL (tr_idx 8) (fun k =>
      tr_obs a i k * tr_obs b i k))).
    + rewrite <- sumL_scale_l. apply sumL_ext. intros i _. apply sumL_scale_l.
    + rewrite tr_obs_pair, tr_r_sq. field.
Qed.

Definition tr_strategy (a0 a1 b0 b1 : nat -> R) : qs_strategy nat nat :=
  {| qs_psi := tr_psi; qs_A0 := tr_obs a0; qs_A1 := tr_obs a1; qs_B0 := tr_obs b0; qs_B1 := tr_obs b1 |}.

Lemma tr_strategy_valid : forall a0 a1 b0 b1,
  tr_unitv a0 -> tr_unitv a1 -> tr_unitv b0 -> tr_unitv b1 ->
  qs_valid nat nat Nat.eq_dec Nat.eq_dec (tr_idx 8) (tr_idx 8) (tr_strategy a0 a1 b0 b1).
Proof.
  intros a0 a1 b0 b1 H0 H1 H2 H3. unfold qs_valid. cbn [qs_psi qs_A0 qs_A1 qs_B0 qs_B1 tr_strategy].
  refine (conj tr_psi_unit (conj (tr_obs_valid _ H0) (conj (tr_obs_valid _ H1)
    (conj (tr_obs_validJ _ H2) (tr_obs_validJ _ H3))))).
Qed.

(** * From the completion set to a quantum strategy *)

Definition tr_G (E00 E01 E10 E11 x y : R) (i j : nat) : R :=
  npa_to_matrix (completed_npa E00 E01 E10 E11 x y) (S i) (S j).

Lemma tr_G_sym : forall E00 E01 E10 E11 x y, tr_sym 4 (tr_G E00 E01 E10 E11 x y).
Proof.
  intros E00 E01 E10 E11 x y i j Hi Hj. unfold tr_G.
  destruct i as [| [| [| [| i]]]]; try lia; destruct j as [| [| [| [| j]]]]; try lia; reflexivity.
Qed.

Lemma tr_G_psd : forall E00 E01 E10 E11 x y,
  npa_psd (completed_npa E00 E01 E10 E11 x y) -> tr_psd 4 (tr_G E00 E01 E10 E11 x y).
Proof.
  intros E00 E01 E10 E11 x y [_ Hp] v.
  pose proof (Hp (fun f => match proj1_sig (Fin.to_nat f) with 0%nat => 0 | S k => v k end)) as H.
  assert (E : quad5 (nat_matrix_to_fin5 (npa_to_matrix (completed_npa E00 E01 E10 E11 x y)))
            (fun f => match proj1_sig (Fin.to_nat f) with 0%nat => 0 | S k => v k end) =
            tr_qf 4 (tr_G E00 E01 E10 E11 x y) v).
  { unfold quad5, sum_fin5, nat_matrix_to_fin5, tr_qf, tr_G, tr_idx. cbn. ring. }
  rewrite E in H. lra.
Qed.

Theorem tr_elliptope_quantum : forall E00 E01 E10 E11,
  elliptope_realizable E00 E01 E10 E11 ->
  exists s : qs_strategy nat nat,
    qs_valid nat nat Nat.eq_dec Nat.eq_dec (tr_idx 8) (tr_idx 8) s /\
    qs_corr nat nat (tr_idx 8) (tr_idx 8) (qs_psi _ _ s) (qs_A0 _ _ s) (qs_B0 _ _ s) = E00 /\
    qs_corr nat nat (tr_idx 8) (tr_idx 8) (qs_psi _ _ s) (qs_A0 _ _ s) (qs_B1 _ _ s) = E01 /\
    qs_corr nat nat (tr_idx 8) (tr_idx 8) (qs_psi _ _ s) (qs_A1 _ _ s) (qs_B0 _ _ s) = E10 /\
    qs_corr nat nat (tr_idx 8) (tr_idx 8) (qs_psi _ _ s) (qs_A1 _ _ s) (qs_B1 _ _ s) = E11.
Proof.
  intros E00 E01 E10 E11 [x [y Hpsd]].
  destruct (tr_gram 4 _ (tr_G_sym E00 E01 E10 E11 x y) (tr_G_psd E00 E01 E10 E11 x y Hpsd))
    as [u Hu].
  exists (tr_strategy (u 0%nat) (u 1%nat) (u 2%nat) (u 3%nat)).
  split; [apply tr_strategy_valid; unfold tr_unitv; [rewrite (Hu 0%nat 0%nat) | rewrite (Hu 1%nat 1%nat)
          | rewrite (Hu 2%nat 2%nat) | rewrite (Hu 3%nat 3%nat)]; try lia; reflexivity |].
  cbn [qs_psi qs_A0 qs_A1 qs_B0 qs_B1 tr_strategy]. rewrite !tr_corr_inner. unfold tr_inner.
  rewrite (Hu 0%nat 2%nat), (Hu 0%nat 3%nat), (Hu 1%nat 2%nat), (Hu 1%nat 3%nat) by lia.
  repeat split.
Qed.

(** * From a quantum strategy to the completion set *)

(** Four unit vectors of any finite real inner-product space: their cross
    inner products are a point of the completion set, the completion being
    their within-party inner products. *)
Theorem tr_vectors_elliptope : forall (X Y : Type) (LX : list X) (LY : list Y) (U0 U1 V0 V1 : X -> Y -> R),
  qs_dot X Y LX LY U0 U0 = 1 -> qs_dot X Y LX LY U1 U1 = 1 ->
  qs_dot X Y LX LY V0 V0 = 1 -> qs_dot X Y LX LY V1 V1 = 1 ->
  elliptope_realizable (qs_dot X Y LX LY U0 V0) (qs_dot X Y LX LY U0 V1)
                       (qs_dot X Y LX LY U1 V0) (qs_dot X Y LX LY U1 V1).
Proof.
  intros X Y LX LY U0 U1 V0 V1 H0 H1 H2 H3.
  exists (qs_dot X Y LX LY U0 U1), (qs_dot X Y LX LY V0 V1). split.
  - exact (completed_matrix_symmetric _ _ _ _ _ _).
  - intro w.
    set (fam := fun t : Fin5 => match proj1_sig (Fin.to_nat t) with
                                | 1%nat => U0 | 2%nat => U1 | 3%nat => V0 | _ => V1 end).
    set (T := [Fin.FS Fin.F1; Fin.FS (Fin.FS Fin.F1); Fin.FS (Fin.FS (Fin.FS Fin.F1));
               Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))] : list Fin5).
    pose proof (qs_dot_combination X Y LX LY T w fam) as C.
    pose proof (qs_dot_nonneg X Y LX LY (fun k j => sumL T (fun t => w t * fam t k j))) as N.
    rewrite C in N. clear C.
    assert (E : quad5 (nat_matrix_to_fin5 (npa_to_matrix (completed_npa
                  (qs_dot X Y LX LY U0 V0) (qs_dot X Y LX LY U0 V1)
                  (qs_dot X Y LX LY U1 V0) (qs_dot X Y LX LY U1 V1)
                  (qs_dot X Y LX LY U0 U1) (qs_dot X Y LX LY V0 V1)))) w =
                w Fin.F1 * w Fin.F1 +
                sumL T (fun t => sumL T (fun t' => w t * qs_dot X Y LX LY (fam t) (fam t') * w t'))).
    { unfold quad5, sum_fin5, nat_matrix_to_fin5, T, fam. cbn.
      rewrite (qs_dot_sym X Y LX LY U1 U0), (qs_dot_sym X Y LX LY V0 U0), (qs_dot_sym X Y LX LY V1 U0),
              (qs_dot_sym X Y LX LY V0 U1), (qs_dot_sym X Y LX LY V1 U1), (qs_dot_sym X Y LX LY V1 V0).
      rewrite H0, H1, H2, H3. ring. }
    rewrite E. pose proof (sq_nonneg (w Fin.F1)). lra.
Qed.

(** Every strategy with real amplitudes in finite dimension has its
    correlators in the completion set. *)
Theorem tr_quantum_elliptope : forall (I J : Type) (eqI : forall a b : I, {a = b} + {a <> b})
  (eqJ : forall a b : J, {a = b} + {a <> b}) (LI : list I) (LJ : list J),
  NoDup LI -> NoDup LJ -> forall s, qs_valid I J eqI eqJ LI LJ s ->
  elliptope_realizable
    (qs_corr I J LI LJ (qs_psi _ _ s) (qs_A0 _ _ s) (qs_B0 _ _ s))
    (qs_corr I J LI LJ (qs_psi _ _ s) (qs_A0 _ _ s) (qs_B1 _ _ s))
    (qs_corr I J LI LJ (qs_psi _ _ s) (qs_A1 _ _ s) (qs_B0 _ _ s))
    (qs_corr I J LI LJ (qs_psi _ _ s) (qs_A1 _ _ s) (qs_B1 _ _ s)).
Proof.
  intros I J eqI eqJ LI LJ HI HJ s [Hu [HA0 [HA1 [HB0 HB1]]]].
  rewrite !qs_corr_dot. apply tr_vectors_elliptope.
  - apply (qs_uvec_unit I J eqI LI LJ HI); assumption.
  - apply (qs_uvec_unit I J eqI LI LJ HI); assumption.
  - apply (qs_vvec_unit I J eqJ LI LJ HJ); assumption.
  - apply (qs_vvec_unit I J eqJ LI LJ HJ); assumption.
Qed.

(** And so does every strategy with complex amplitudes in finite dimension. *)
Theorem tr_complex_elliptope : forall (I J : Type) (eqI : forall a b : I, {a = b} + {a <> b})
  (eqJ : forall a b : J, {a = b} + {a <> b}) (LI : list I) (LJ : list J),
  NoDup LI -> NoDup LJ -> forall s, qc_valid I J eqI eqJ LI LJ s ->
  let c := fun ar ai br bi => qc_corr I J LI LJ (qc_pr _ _ s) (qc_pi _ _ s) ar ai br bi in
  elliptope_realizable
    (c (qc_A0r _ _ s) (qc_A0i _ _ s) (qc_B0r _ _ s) (qc_B0i _ _ s))
    (c (qc_A0r _ _ s) (qc_A0i _ _ s) (qc_B1r _ _ s) (qc_B1i _ _ s))
    (c (qc_A1r _ _ s) (qc_A1i _ _ s) (qc_B0r _ _ s) (qc_B0i _ _ s))
    (c (qc_A1r _ _ s) (qc_A1i _ _ s) (qc_B1r _ _ s) (qc_B1i _ _ s)).
Proof.
  intros I J eqI eqJ LI LJ HI HJ s [Hu [HA0 [HA1 [HB0 HB1]]]] c.
  pose proof HA0 as [HA0s [HA0a _]]. pose proof HA1 as [HA1s [HA1a _]].
  unfold c. rewrite !(qc_corr_dot I J LI LJ) by assumption. rewrite !qc_dot_lift.
  apply tr_vectors_elliptope; rewrite <- qc_dot_lift.
  - apply (qc_uvec_unit I J eqI LI LJ HI); assumption.
  - apply (qc_uvec_unit I J eqI LI LJ HI); assumption.
  - apply (qc_vvec_unit I J eqJ LI LJ HJ); assumption.
  - apply (qc_vvec_unit I J eqJ LI LJ HJ); assumption.
Qed.

(** Tsirelson's representation for CHSH: the completion set is exactly the
    set of correlator tables of quantum strategies with real amplitudes in
    finite dimension, and two 8-level systems suffice. *)
Theorem tr_representation : forall E00 E01 E10 E11,
  elliptope_realizable E00 E01 E10 E11 <->
  exists s : qs_strategy nat nat,
    qs_valid nat nat Nat.eq_dec Nat.eq_dec (tr_idx 8) (tr_idx 8) s /\
    qs_corr nat nat (tr_idx 8) (tr_idx 8) (qs_psi _ _ s) (qs_A0 _ _ s) (qs_B0 _ _ s) = E00 /\
    qs_corr nat nat (tr_idx 8) (tr_idx 8) (qs_psi _ _ s) (qs_A0 _ _ s) (qs_B1 _ _ s) = E01 /\
    qs_corr nat nat (tr_idx 8) (tr_idx 8) (qs_psi _ _ s) (qs_A1 _ _ s) (qs_B0 _ _ s) = E10 /\
    qs_corr nat nat (tr_idx 8) (tr_idx 8) (qs_psi _ _ s) (qs_A1 _ _ s) (qs_B1 _ _ s) = E11.
Proof.
  intros E00 E01 E10 E11. split; [apply tr_elliptope_quantum |].
  intros [s [Hv [e0 [e1 [e2 e3]]]]]. rewrite <- e0, <- e1, <- e2, <- e3.
  apply (tr_quantum_elliptope nat nat Nat.eq_dec Nat.eq_dec); [apply seq_NoDup | apply seq_NoDup | exact Hv].
Qed.

(** The same set with complex amplitudes. *)
Theorem tr_representation_complex : forall E00 E01 E10 E11,
  elliptope_realizable E00 E01 E10 E11 <->
  exists s : qc_strategy nat nat,
    qc_valid nat nat Nat.eq_dec Nat.eq_dec (tr_idx 8) (tr_idx 8) s /\
    let c := fun ar ai br bi => qc_corr nat nat (tr_idx 8) (tr_idx 8) (qc_pr _ _ s) (qc_pi _ _ s) ar ai br bi in
    c (qc_A0r _ _ s) (qc_A0i _ _ s) (qc_B0r _ _ s) (qc_B0i _ _ s) = E00 /\
    c (qc_A0r _ _ s) (qc_A0i _ _ s) (qc_B1r _ _ s) (qc_B1i _ _ s) = E01 /\
    c (qc_A1r _ _ s) (qc_A1i _ _ s) (qc_B0r _ _ s) (qc_B0i _ _ s) = E10 /\
    c (qc_A1r _ _ s) (qc_A1i _ _ s) (qc_B1r _ _ s) (qc_B1i _ _ s) = E11.
Proof.
  intros E00 E01 E10 E11. split.
  - intro H. destruct (tr_elliptope_quantum _ _ _ _ H) as [s [Hv [e0 [e1 [e2 e3]]]]].
    exists (qc_of_real nat nat s).
    destruct (qc_of_real_valid nat nat Nat.eq_dec Nat.eq_dec (tr_idx 8) (tr_idx 8) s Hv) as [Hcv _].
    split; [exact Hcv |]. cbv zeta. unfold qc_of_real.
    cbn [qc_pr qc_pi qc_A0r qc_A0i qc_A1r qc_A1i qc_B0r qc_B0i qc_B1r qc_B1i].
    rewrite !qc_corr_real. repeat split; assumption.
  - intros [s [Hv He]]. cbv zeta in He. destruct He as [e0 [e1 [e2 e3]]].
    rewrite <- e0, <- e1, <- e2, <- e3.
    exact (tr_complex_elliptope nat nat Nat.eq_dec Nat.eq_dec (tr_idx 8) (tr_idx 8)
      (seq_NoDup 8 0) (seq_NoDup 8 0) s Hv).
Qed.

Print Assumptions tr_gram.
Print Assumptions tr_gamma_clifford.
Print Assumptions tr_gamma_trace.
Print Assumptions tr_corr_inner.
Print Assumptions tr_strategy_valid.
Print Assumptions tr_elliptope_quantum.
Print Assumptions tr_vectors_elliptope.
Print Assumptions tr_quantum_elliptope.
Print Assumptions tr_complex_elliptope.
Print Assumptions tr_representation.
Print Assumptions tr_representation_complex.
