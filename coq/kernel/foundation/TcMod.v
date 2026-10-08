(** TcMod.v: moduli with two prescribed entries, and codes of simple register
    files.

    The packed universal machine reads its two inputs as 2^x * 3^e. The
    vendored layout puts the output in register 0 and the inputs in
    registers 1 and 2, so the moduli of registers 1 and 2 must be 2 and 3:
    [tc_moduli_for n0] gives pairwise coprime moduli larger than 1 for 3 + n0
    registers with those two entries. The code of a register file that is 0
    except in one or two places is a power of the modulus or a product of
    two.

    Dependencies: Coq standard library, the vendored coq-undecidability
    library, TcGodel.v. No axioms and no unfinished proofs.                             *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is recursion theory on the two-counter machine of EarnedCore.v (its
   programs, runs and the numbering of programs). The machine's link to the
   abstract record (a CertificationSystem with the trace cost floor, and a
   Thiele-complete machine) lives in EarnedCoreLinks.v and ThieleComplete.v. *)


From Coq Require Import List Arith Lia.
From Undecidability.Shared.Libs.DLW Require Import utils gcd pos vec godel_coding.
Require Import Kernel.TcGodel.
Set Implicit Arguments.
Set Default Goal Selector "!".

#[local] Notation "e #> x" := (vec_pos e x).

Lemma tc_ok_cons : forall k m (ms : vec nat k),
  tc_moduli_ok (m ## ms) <->
  1 < m /\ (forall q, Nat.gcd m (ms#>q) = 1) /\ tc_moduli_ok ms.
Proof.
  intros k m ms. split.
  - intros [Hgt Hcop]. repeat split.
    + apply (Hgt pos0).
    + intro q. apply (Hcop pos0 (pos_nxt q)). discriminate.
    + intro q. apply (Hgt (pos_nxt q)).
    + intros p q Hpq. apply (Hcop (pos_nxt p) (pos_nxt q)). intro E. apply Hpq. apply pos_nxt_inj. exact E.
  - intros (Hm & Hg & Hgt & Hcop). split.
    + intro p. pos_inv p; simpl; [exact Hm | apply Hgt].
    + intros p q Hpq. pos_inv p; pos_inv q; simpl.
      * exfalso. apply Hpq. reflexivity.
      * apply Hg.
      * rewrite Nat.gcd_comm. apply Hg.
      * apply Hcop. intro E. apply Hpq. f_equal. exact E.
Qed.

Lemma tc_moduli6 : forall k, exists r : vec nat k, tc_moduli_ok r /\
  forall q, Nat.gcd 2 (r#>q) = 1 /\ Nat.gcd 3 (r#>q) = 1.
Proof.
  induction k as [| k IH].
  - exists vec_nil. split; [split; intro p; invert pos p |]. intro q. invert pos q.
  - destruct IH as [r [Hok H6]].
    destruct Hok as [Hgt Hcop].
    assert (Hpos : 0 < tc_prod r) by (apply tc_prod_pos; intro p; pose proof (Hgt p); lia).
    exists ((1 + 6 * tc_prod r) ## r).
    assert (Hnew : forall q, Nat.gcd (1 + 6 * tc_prod r) (r#>q) = 1).
    { intro q. destruct (tc_prod_div r q) as [c Hc]. rewrite Nat.gcd_comm.
      replace (1 + 6 * tc_prod r) with (1 + (6 * c) * (r#>q)) by (rewrite Hc; ring).
      apply tc_gcd_succ. }
    split.
    + apply tc_ok_cons. split; [lia |]. split; [exact Hnew | split; assumption].
    + intro q. pos_inv q.
      * split.
        -- change (Nat.gcd 2 (1 + 6 * tc_prod r) = 1).
           replace (1 + 6 * tc_prod r) with (1 + (3 * tc_prod r) * 2) by ring.
           exact (tc_gcd_succ (3 * tc_prod r) 2).
        -- change (Nat.gcd 3 (1 + 6 * tc_prod r) = 1).
           replace (1 + 6 * tc_prod r) with (1 + (2 * tc_prod r) * 3) by ring.
           exact (tc_gcd_succ (2 * tc_prod r) 3).
      * apply H6.
Qed.

Theorem tc_moduli_for : forall n0, exists ms : vec nat (3 + n0),
  tc_moduli_ok ms /\ ms#>pos1 = 2 /\ ms#>pos2 = 3.
Proof.
  intro n0. destruct (tc_moduli6 (S n0)) as [r [Hok H6]].
  destruct (tc_cons_inv r) as [r0 [r' ->]].
  apply tc_ok_cons in Hok as (Hr0 & Hg0 & Hok').
  exists (r0 ## 2 ## 3 ## r'). split; [| split; reflexivity].
  apply tc_ok_cons. split; [exact Hr0 |]. split.
  - intro q. pos_inv q; simpl.
    + rewrite Nat.gcd_comm. exact (proj1 (H6 pos0)).
    + pos_inv q; simpl.
      * rewrite Nat.gcd_comm. exact (proj2 (H6 pos0)).
      * apply Hg0.
  - apply tc_ok_cons. split; [lia |]. split.
    + intro q. pos_inv q; simpl.
      * reflexivity.
      * exact (proj1 (H6 (pos_nxt q))).
    + apply tc_ok_cons. split; [lia |]. split.
      * intro q. exact (proj2 (H6 (pos_nxt q))).
      * exact Hok'.
Qed.

(* the code of the zero register file is 1 *)
Lemma tc_enc_zero : forall k (ms : vec nat k), tc_enc ms (vec_zero (n := k)) = 1.
Proof.
  induction k as [| k IH]; intro ms; [reflexivity |].
  destruct (tc_cons_inv ms) as [m [ms' ->]]. rewrite vec_zero_S. rewrite tc_enc_cons. simpl.
  rewrite IH. lia.
Qed.

(* the code of a register file that is 0 except at the first three places *)
Lemma tc_enc_three : forall k m0 m1 m2 (ms : vec nat k) a b c,
  tc_enc (m0 ## m1 ## m2 ## ms) (a ## b ## c ## vec_zero (n := k)) = m0 ^ a * (m1 ^ b * (m2 ^ c * 1)).
Proof.
  intros k m0 m1 m2 ms a b c. rewrite !tc_enc_cons. rewrite tc_enc_zero. reflexivity.
Qed.

Print Assumptions tc_moduli_for.
