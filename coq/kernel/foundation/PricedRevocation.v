(** Proved outcomes for the priced-revocation targets. *)

(* SCOPE NOTE: standalone proof scope. These outcomes concern the generic
   transition model and the separately specified Casper FFG model. *)

From Coq Require Import Arith.PeanoNat Lia Bool.
From Kernel Require Import CasperRecordReading PricedRevocationCore.

Theorem actual_revocation_excludes_permanence_holds :
  actual_revocation_excludes_permanence.
Proof.
  intros S next read [s [Htrue Hfalse]] Hpermanent.
  specialize (Hpermanent s Htrue). congruence.
Qed.

Definition toggle_cost (b : bool) : nat := if b then 1 else 0.

Theorem revocation_price_does_not_price_writes_refuted :
  ~ revocation_price_does_not_price_writes.
Proof.
  intro Hall.
  specialize (Hall bool negb (fun b => b) toggle_cost).
  assert (Hrev : revocation_priced negb (fun b => b) toggle_cost).
  { intros [] Htrue Hfalse; simpl in *; try discriminate; lia. }
  specialize (Hall Hrev false eq_refl eq_refl).
  simpl in Hall. lia.
Qed.

Theorem casper_conflict_is_accountable_holds :
  casper_conflict_is_accountable.
Proof.
  intros C s h1 h2 H1 H2 H21 H12 Hneq.
  exact (conflicting_records_are_priced C s h1 h2 H1 H2 H21 H12 Hneq).
Qed.

Theorem casper_write_without_slashing_holds :
  casper_write_without_slashing.
Proof. exact finalization_without_slashing. Qed.

Print Assumptions actual_revocation_excludes_permanence_holds.
Print Assumptions revocation_price_does_not_price_writes_refuted.
Print Assumptions casper_conflict_is_accountable_holds.
Print Assumptions casper_write_without_slashing_holds.
