(** A usable unbounded counter primitive in the existing abstract ISA.
    The 00 bucket difference represents u-v; all setting totals are positive.
    Matching/differing trials increment either component. The existing base
    CHSH guard succeeds exactly at equality. This is one counter primitive,
    not a universal interpreter or a two-counter-machine simulation. *)
From Coq Require Import ZArith Lia.
From Kernel Require Import VMState VMStep.
Definition counter_witness (u v : nat) : WitnessCounts :=
 {| wc_same_00 := S u; wc_diff_00 := S v;
    wc_same_01 := 1; wc_diff_01 := 1;
    wc_same_10 := 1; wc_diff_10 := 0;
    wc_same_11 := 1; wc_diff_11 := 1 |}.
Theorem witness_counter_equality_test : forall u v,
 column_contractive_check_witness (counter_witness u v) = true <-> u = v.
Proof.
 intros u v.
 unfold column_contractive_check_witness, chsh_n_z, chsh_d_z.
 cbn [counter_witness wc_same_00 wc_diff_00 wc_same_01 wc_diff_01 wc_same_10 wc_diff_10 wc_same_11 wc_diff_11].
 repeat rewrite Bool.andb_true_iff.
 repeat rewrite Z.ltb_lt. repeat rewrite Z.leb_le.
 rewrite !Nat2Z.inj_succ.
 split; intros H; [nia|subst; repeat split; nia].
Qed.

Lemma counter_witness_increment : forall u v,
 record_trial (counter_witness u v) 0 0 0 0 = counter_witness (S u) v.
Proof. reflexivity. Qed.
Lemma counter_witness_decrement : forall u v,
 record_trial (counter_witness u v) 0 0 0 1 = counter_witness u (S v).
Proof. reflexivity. Qed.
