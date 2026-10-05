(** CasperRecordReading: where Casper FFG puts its price.

    Read Casper FFG through the record axis. The record is "this block is
    finalized." The ported model ([CasperFFG]) shows two things about it.

    - Contradicting the record is priced: two finalized blocks on different
      branches mean a "1/3" set of validators broke a slashing condition
      ([conflicting_records_are_priced]). This is accountable safety, read
      as a price on revoking a finalized record.
    - Writing the record is not priced: a block can be finalized with no
      validator slashed at all ([finalization_without_slashing]).

    So Casper prices the revocation of its record, not the write. A2 prices
    the write. The two fit the finite-machine result: a record whose write
    is free must be one that can be revoked, and Casper's finalization can
    be revoked, at the price of a slashed quorum. *)

(* SCOPE NOTE: standalone proof scope. It reads the Casper FFG model
   through the record axis; the Casper model imports no machine semantics. *)

From Coq Require Import Arith.PeanoNat Lia Relations Bool.
From Kernel Require Import CasperFFG.

Section Reading.

Variable C : CasperSetting.

(** The record: some finalization of block [h] is in the vote set. *)
Definition finalized_record (s : State C) (h : Hash C) : Prop :=
  exists q v child, finalized C s q h v child.

Theorem conflicting_records_are_priced : forall s h1 h2,
  finalized_record s h1 -> finalized_record s h2 ->
  ~ hash_ancestor C h2 h1 -> ~ hash_ancestor C h1 h2 -> h1 <> h2 ->
  quorum_slashed C s.
Proof.
  intros s h1 h2 [q1 [v1 [c1 Hf1]]] [q2 [v2 [c2 Hf2]]] Hh Hh' Hn.
  apply accountable_safety.
  exists h1, h2, q1, q2, v1, v2, c1, c2.
  exact (conj Hf1 (conj Hf2 (conj Hh (conj Hh' Hn)))).
Qed.

End Reading.

(** In the one-validator chain, a single vote finalizes the genesis block and
    slashes nobody. *)
Definition one_vote : State chain_setting :=
  mkSt chain_setting (fun _ h v src => Nat.eqb h 1 && Nat.eqb v 1 && Nat.eqb src 0).

Theorem finalization_without_slashing :
  finalized_record chain_setting one_vote 0 /\
  forall n, ~ slashed chain_setting one_vote n.
Proof.
  split.
  - exists (fun _ => True), 0, 1.
    split; [reflexivity |].
    split; [constructor |].
    split; [exact I |].
    split; [intros [] _; reflexivity |].
    split; [| simpl; lia].
    simpl. apply (nth_ancestor_nth chain_setting 0 0 0 1);
      [constructor | reflexivity].
  - intros [] [[h1 [h2 [Hne [v [s1 [s2 [H1 H2]]]]]]] |
             [h1 [h2 [v1 [v2 [s1 [s2 [H1 [H2 [Hv Hs]]]]]]]]]]; simpl in *.
    + apply andb_prop in H1 as [H1 _]. apply andb_prop in H1 as [H1 _].
      apply andb_prop in H2 as [H2 _]. apply andb_prop in H2 as [H2 _].
      apply Nat.eqb_eq in H1. apply Nat.eqb_eq in H2. congruence.
    + apply andb_prop in H1 as [H1 Hs1]. apply andb_prop in H1 as [_ Hv1].
      apply andb_prop in H2 as [H2 Hs2]. apply andb_prop in H2 as [_ Hv2].
      apply Nat.eqb_eq in Hv1. apply Nat.eqb_eq in Hv2. lia.
Qed.

Print Assumptions conflicting_records_are_priced.
Print Assumptions finalization_without_slashing.
