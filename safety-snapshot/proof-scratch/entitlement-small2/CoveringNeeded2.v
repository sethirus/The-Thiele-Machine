(** CoveringNeeded2.v: without the covering hypothesis the bound is false.

    Structural entitlement (EntitlementSmall.v) says: if the narrowing is
    covered by a tree no deeper than the record moves the run made, the
    ledger's rise covers the index bits. The covering is a hypothesis. This
    file shows it cannot be dropped, on the small machine itself.

    The program is the three-move chain on the claim "A >= m", for a number
    m as large as you like. It raises the record exactly when A >= m
    (TimeTax2.v, ent2_chain_decides) and always charges 3. Take the prior to
    be the 2^n starts with A below 2^n, and m = 2^n - 1. Then the chain
    certifies exactly the start with A = 2^n - 1: a one-member posterior,
    n index bits narrowed, for a ledger of 3. So for n >= 4 the claim "the
    index-bit drop is at most the ledger's rise" is false for this run
    [ent2_uncovered_claim_false], and so no tree of depth at most 3 covers it,
    whatever the representative observation [ent2_no_cheap_covering].

    This is the small machine's own version of the big build's rejected
    "single-trace claim". One property with a big constant in it carries n
    bits in a single yes/no question; what the bound prices is a narrowing
    whose classes are balanced (a tree with enough leaves), not any
    narrowing.

    Dependencies: EntitlementSmall.v, TimeTax2.v and what they require. No
    axioms, no Admitted.                                                  *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Minimal.ThieleComplete.
Require Import Minimal.EntitlementSmall.
Require Import Minimal.TimeTax2.
Require Minimal.EarnedCore.
Module E := Minimal.EarnedCore.

Definition ent2_prior_ge (n : nat) : list E.state := map (fun a => E.start a 0) (seq 0 (2 ^ n)).
Definition ent2_post_ge (n : nat) : list E.state := [E.start (2 ^ n - 1) 0].

Lemma ent2_start_inj : forall a a' b b', E.start a b = E.start a' b' -> a = a'.
Proof. intros a a' b b' H. apply (f_equal (fun s => E.ca (E.core_of s))) in H. exact H. Qed.

(* The chain on "A >= 2^n - 1" certifies exactly the last start. *)
Theorem ent2_uncovered_posterior : forall n, 1 <= n ->
  forall x, In x (ent2_prior_ge n) ->
    (In x (ent2_post_ge n) <-> E.cert (E.run (ent2_chain (2 ^ n - 1)) x) = true).
Proof.
  intros n Hn x Hx. unfold ent2_prior_ge in Hx. apply in_map_iff in Hx as [a [<- Ha]].
  apply in_seq in Ha. destruct (ent2_chain_decides (2 ^ n - 1) a 0) as [Hc _].
  rewrite Hc. unfold ent2_post_ge. simpl. split.
  - intros [H | []]. apply ent2_start_inj in H. subst a. apply Nat.leb_le. lia.
  - intro H. apply Nat.leb_le in H. left. f_equal. lia.
Qed.

Theorem ent2_uncovered_claim_false : forall n, 4 <= n ->
  length (ent2_prior_ge n) = 2 ^ n /\ length (ent2_post_ge n) = 1 /\
  Nat.log2_up (length (ent2_prior_ge n)) - Nat.log2_up (length (ent2_post_ge n)) = n /\
  E.mu (E.run (ent2_chain (2 ^ n - 1)) (E.start (2 ^ n - 1) 0)) = 3 /\
  ~ (Nat.log2_up (length (ent2_prior_ge n)) - Nat.log2_up (length (ent2_post_ge n))
       <= E.mu (E.run (ent2_chain (2 ^ n - 1)) (E.start (2 ^ n - 1) 0)) - E.mu (E.start (2 ^ n - 1) 0)).
Proof.
  intros n Hn.
  assert (Hp : length (ent2_prior_ge n) = 2 ^ n)
    by (unfold ent2_prior_ge; rewrite map_length, seq_length; reflexivity).
  assert (Hmu : E.mu (E.run (ent2_chain (2 ^ n - 1)) (E.start (2 ^ n - 1) 0)) = 3)
    by (apply (proj1 (proj2 (ent2_chain_decides (2 ^ n - 1) (2 ^ n - 1) 0)))).
  assert (Hbits : Nat.log2_up (length (ent2_prior_ge n)) -
                  Nat.log2_up (length (ent2_post_ge n)) = n).
  { rewrite Hp. unfold ent2_post_ge. simpl length. rewrite Nat.log2_up_pow2 by lia.
    rewrite Nat.log2_up_1. lia. }
  split; [exact Hp |]. split; [reflexivity |]. split; [exact Hbits |]. split; [exact Hmu |].
  rewrite Hbits, Hmu. simpl. lia.
Qed.

(* So no tree of depth at most 3 covers that narrowing, whatever the
   representative observation. *)
Theorem ent2_no_cheap_covering : forall n, 4 <= n ->
  forall (r : E.state -> nat) (T : ent_tree), ent_depth T <= 3 ->
    ~ ent_reduction r T (ent2_prior_ge n) (ent2_post_ge n).
Proof.
  intros n Hn r T HT Hred.
  destruct (ent2_uncovered_claim_false n Hn) as [_ [_ [Hbits _]]].
  pose proof (ent_index_bits_le_depth r T (ent2_prior_ge n) (ent2_post_ge n)
                ltac:(unfold ent2_post_ge; simpl; lia) Hred) as H.
  lia.
Qed.

Print Assumptions ent2_uncovered_posterior.
Print Assumptions ent2_uncovered_claim_false.
Print Assumptions ent2_no_cheap_covering.
