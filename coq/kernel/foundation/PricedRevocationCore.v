(** Exact targets for classifying records revocable at a price. *)

(* SCOPE NOTE: standalone proof scope. This generic transition boundary and
   Casper classification intentionally import no Thiele VM semantics. *)

From Coq Require Import Arith.PeanoNat.
From Kernel Require Import CasperFFG CasperRecordReading.

Definition transition_record_permanent {S : Type}
    (next : S -> S) (read : S -> bool) : Prop :=
  forall s, read s = true -> read (next s) = true.

Definition actual_revocation {S : Type}
    (next : S -> S) (read : S -> bool) : Prop :=
  exists s, read s = true /\ read (next s) = false.

Definition revocation_priced {S : Type}
    (next : S -> S) (read : S -> bool) (cost : S -> nat) : Prop :=
  forall s, read s = true -> read (next s) = false -> cost s >= 1.

Definition write_priced {S : Type}
    (next : S -> S) (read : S -> bool) (cost : S -> nat) : Prop :=
  forall s, read s = false -> read (next s) = true -> cost s >= 1.

Definition actual_revocation_excludes_permanence : Prop :=
  forall (S : Type) (next : S -> S) (read : S -> bool),
    actual_revocation next read -> ~ transition_record_permanent next read.

(** This universal implication is the tempting claim to test and refute. *)
Definition revocation_price_does_not_price_writes : Prop :=
  forall (S : Type) (next : S -> S) (read : S -> bool) (cost : S -> nat),
    revocation_priced next read cost -> write_priced next read cost.

(** Casper's actual proved price is accountable conflict: conflicting
    finalizations imply a slashable quorum. It is not a transition cost. *)
Definition casper_conflict_is_accountable : Prop :=
  forall (C : CasperSetting) (s : State C) (h1 h2 : Hash C),
    finalized_record C s h1 -> finalized_record C s h2 ->
    ~ hash_ancestor C h2 h1 -> ~ hash_ancestor C h1 h2 -> h1 <> h2 ->
    quorum_slashed C s.

Definition casper_write_without_slashing : Prop :=
  finalized_record chain_setting one_vote 0 /\
  forall n, ~ slashed chain_setting one_vote n.
