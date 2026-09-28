(** An alternative diagonal witness layout under the existing ISA.
    This removes the shared-base-guard rejection of the pinned layout.
    It does not establish independent zero tests or universal computation. *)
From Coq Require Import ZArith Lia Bool.
From Kernel Require Import VMState VMStep.
Definition diagonal_counter_witness (u v a b : nat) : WitnessCounts :=
 {| wc_same_00 := S u; wc_diff_00 := S v;
    wc_same_01 := 1; wc_diff_01 := 1;
    wc_same_10 := 1; wc_diff_10 := 1;
    wc_same_11 := S a; wc_diff_11 := S b |}.
Theorem diagonal_base_guard : forall u v a b,
 column_contractive_check_witness (diagonal_counter_witness u v a b) = true.
Proof.
 intros u v a b.
 unfold column_contractive_check_witness, chsh_n_z, chsh_d_z.
 cbn [diagonal_counter_witness wc_same_00 wc_diff_00 wc_same_01 wc_diff_01 wc_same_10 wc_diff_10 wc_same_11 wc_diff_11].
 repeat rewrite Bool.andb_true_iff.
 repeat rewrite Z.ltb_lt. repeat rewrite Z.leb_le.
 rewrite !Nat2Z.inj_succ.
 repeat split; nia.
Qed.
Lemma diagonal_increment_first : forall u v a b,
 record_trial (diagonal_counter_witness u v a b) 0 0 0 0 = diagonal_counter_witness (S u) v a b.
Proof. reflexivity. Qed.
Lemma diagonal_decrement_first : forall u v a b,
 record_trial (diagonal_counter_witness u v a b) 0 0 0 1 = diagonal_counter_witness u (S v) a b.
Proof. reflexivity. Qed.
Lemma diagonal_increment_second : forall u v a b,
 record_trial (diagonal_counter_witness u v a b) 1 1 0 0 = diagonal_counter_witness u v (S a) b.
Proof. reflexivity. Qed.
Lemma diagonal_decrement_second : forall u v a b,
 record_trial (diagonal_counter_witness u v a b) 1 1 0 1 = diagonal_counter_witness u v a (S b).
Proof. reflexivity. Qed.

Definition diagonal_sos_condition (u v a b : nat) : Prop :=
 let x := chsh_d_z (S u) (S v) in
 let nx := chsh_n_z (S u) (S v) in
 let y := chsh_d_z (S a) (S b) in
 let ny := chsh_n_z (S a) (S b) in
 (x*x*ny*ny + y*y*nx*nx <= nx*nx*ny*ny)%Z.
Theorem diagonal_combined_guard : forall u v a b,
 column_contractive_check_q1ab_kernel (diagonal_counter_witness u v a b) = true <->
 diagonal_sos_condition u v a b.
Proof.
 intros. unfold column_contractive_check_q1ab_kernel.
 rewrite diagonal_base_guard. cbn [andb].
 unfold sum_E_sq_check_witness, diagonal_sos_condition, chsh_n_z, chsh_d_z.
 cbn [diagonal_counter_witness wc_same_00 wc_diff_00 wc_same_01 wc_diff_01 wc_same_10 wc_diff_10 wc_same_11 wc_diff_11].
 rewrite Z.leb_le. nia.
Qed.
Theorem diagonal_combined_symmetric : forall u v a b,
 column_contractive_check_q1ab_kernel (diagonal_counter_witness u v a b) =
 column_contractive_check_q1ab_kernel (diagonal_counter_witness a b u v).
Proof.
 intros. apply Bool.eq_true_iff_eq.
 rewrite !diagonal_combined_guard.
 unfold diagonal_sos_condition. nia.
Qed.
Example diagonal_nonzero_counters_can_pass :
 column_contractive_check_q1ab_kernel (diagonal_counter_witness 1 0 1 0) = true.
Proof. vm_compute. reflexivity. Qed.
Example diagonal_nonzero_counters_can_fail :
 column_contractive_check_q1ab_kernel (diagonal_counter_witness 9 0 9 0) = false.
Proof. vm_compute. reflexivity. Qed.

(** The symmetric combined guard cannot itself select which difference is zero.
    This counterexample concerns this layout and this single guard only. *)
Example diagonal_swapped_zero_tests_collide :
 column_contractive_check_q1ab_kernel (diagonal_counter_witness 0 0 1 0) = true /\
 column_contractive_check_q1ab_kernel (diagonal_counter_witness 1 0 0 0) = true.
Proof. vm_compute. auto. Qed.
