(** Tc2Mult.v: no program of the machine multiplies every input by a number
    that is coprime to all small numbers.

    For a program P of EarnedCore let N(P) = 4 * Nb(length P), where Nb is an
    explicit bound on the number of control states of the abstract machine of
    P (Tc2Embed.v). Let c(P) = N(P)! + 1. Then c(P) is coprime to every
    number up to N(P). The theorem: there is no program P that, started with x
    in counter A and 0 in counter B, stops with c(P) * x in counter A for every
    x. The whole argument is in Tc2Chain.v (a chain of stages gives
    c * (product of m_i) = product of n_i with every m_i, n_i at most N(P)); this
    file connects it to the programs.

    Dependencies: Tc2Am.v, Tc2Forced.v, Tc2Chain.v, Tc2Embed.v. No axioms and no
    unfinished proofs. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Minimal.EarnedCore.
Require Import Minimal.Tc2Am Minimal.Tc2Forced Minimal.Tc2Stage Minimal.Tc2Chain Minimal.Tc2Embed.
Module E := Minimal.EarnedCore.
Set Default Goal Selector "!".

Fixpoint tc2_fact (n : nat) : nat := match n with 0 => 1 | S m => S m * tc2_fact m end.

Lemma tc2_fact_pos : forall n, 1 <= tc2_fact n.
Proof. induction n as [| n IH]; simpl; [lia | nia]. Qed.

Lemma tc2_fact_div : forall N k, 1 <= k -> k <= N -> Nat.divide k (tc2_fact N).
Proof.
  intros N. induction N as [| N IH]; intros k H1 H2; [lia |].
  simpl. destruct (Nat.eq_dec k (S N)) as [-> | Hne].
  - exists (tc2_fact N). simpl. ring.
  - destruct (IH k H1 ltac:(lia)) as [m Hm]. exists (S N * m). rewrite Hm. ring.
Qed.

Lemma tc2_fact_coprime : forall N k, 1 <= k -> k <= N -> Nat.gcd (tc2_fact N + 1) k = 1.
Proof.
  intros N k H1 H2. set (g := Nat.gcd (tc2_fact N + 1) k).
  assert (Hg1 : Nat.divide g (tc2_fact N + 1)) by apply Nat.gcd_divide_l.
  assert (Hg2 : Nat.divide g k) by apply Nat.gcd_divide_r.
  assert (Hg3 : Nat.divide g (tc2_fact N)) by (eapply Nat.divide_trans; [exact Hg2 | apply tc2_fact_div; assumption]).
  apply Nat.divide_1_r.
  pose proof (Nat.divide_sub_r g (tc2_fact N + 1) (tc2_fact N) Hg1 Hg3) as H.
  replace (tc2_fact N + 1 - tc2_fact N) with 1 in H by lia. exact H.
Qed.

Lemma tc2_pw_mono : forall a b e, a <= b -> tc2_pw a e <= tc2_pw b e.
Proof.
  intros a b e H. induction e as [| e IH]; simpl; [lia |].
  pose proof (tc2_pw_pos a e). nia.
Qed.

(* a bound on the number of control states of the abstract machine of a program of n lines *)
Definition tc2_Nb (n : nat) : nat := S n * 4 * tc2_pw (S (2 * n)) E.fact_cap.

Lemma tc2_lq_len : forall P, length (tc2_lq P) <= tc2_Nb (length P).
Proof.
  intro P. unfold tc2_Nb.
  assert (Hl : length (tc2_lq P) = S (length P) * 2 * 2 * length (tc2_lu E.fact_cap (tc2_fal P))).
  { unfold tc2_lq. etransitivity; [apply prod_length |]. rewrite !prod_length. rewrite seq_length. simpl length. reflexivity. }
  rewrite Hl.
  pose proof (tc2_lu_len E.fact_cap (tc2_fal P)) as H1.
  pose proof (tc2_fal_len P) as H2.
  pose proof (tc2_pw_mono (S (length (tc2_fal P))) (S (2 * length P)) E.fact_cap ltac:(lia)) as H3.
  nia.
Qed.

Definition tc2_N (n : nat) : nat := 4 * tc2_Nb n.
Definition tc2_c (n : nat) : nat := tc2_fact (tc2_N n) + 1.

Lemma tc2_q0_in : forall P, In (tc2_q0 P) (tc2_lq P).
Proof.
  intro P. apply tc2_lq_in. unfold tc2_q0, tc2_abs, tc2_okq. cbn [E.start_core E.pc E.err E.chan E.facts].
  destruct (tc2_cl_range (length P) 1) as [H1 H2]. repeat split; [exact H1 | exact H2 | simpl; lia |].
  intros x []. 
Qed.

Theorem tc2_no_mult : forall P : list E.instr, ~ (forall x, tc2_pf P x (tc2_c (length P) * x)).
Proof.
  intros P H.
  pose proof (tc2_lq_len P) as Hlq. pose proof (tc2_fact_pos (tc2_N (length P))) as Hf.
  apply (am_no_multiplier (tc2_am_of P) (tc2_q0 P) (tc2_c (length P))).
  - exact (tc2_q0_in P).
  - unfold tc2_c. lia.
  - intros k Hk1 Hk2. unfold tc2_c. apply tc2_fact_coprime; [exact Hk1 |].
    unfold tc2_N. 
    assert (HK : length (fs_lA (tc2_am_of P)) = length (tc2_lq P) * 2 * 2).
    { unfold fs_lA. rewrite !prod_length. reflexivity. }
    rewrite HK in Hk2. lia.
  - intro x. destruct (proj1 (tc2_pf_iff P x _) (H x)) as (n & Hh & Hy). exists n. split; assumption.
Qed.

Print Assumptions tc2_no_mult.
