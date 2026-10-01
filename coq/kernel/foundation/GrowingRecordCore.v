(** GrowingRecordCore: exact targets for monotone multi-valued records.

    A value grows in an arbitrary Boolean-decidable partial order.  Each
    possible threshold [a <= value] is a Boolean observation.  The proposed
    extension of the record axis over any base ([StructuralCoreAnyBase]) is
    a family of threshold latches plus a price schedule, not necessarily one
    Boolean latch.

    This file states definitions and propositions only.  Their outcomes are
    in [GrowingRecord]. *)

From Coq Require Import List Bool Arith.PeanoNat.
Import ListNotations.

From Kernel Require Import StructuralCore StructuralCoreAnyBase.

(** * Ordered record values *)

Record BoolPartialOrder (A : Type) : Type := {
  gr_leq : A -> A -> bool;
  gr_leq_refl : forall x, gr_leq x x = true;
  gr_leq_antisym : forall x y,
    gr_leq x y = true -> gr_leq y x = true -> x = y;
  gr_leq_trans : forall x y z,
    gr_leq x y = true -> gr_leq y z = true -> gr_leq x z = true
}.

Arguments gr_leq {A} _ _ _.

Definition record_grows (M : RCM) {A : Type} (P : BoolPartialOrder A)
    (rec : rc_state M -> A) : Prop :=
  forall m, gr_leq P (rec m) (rec (rc_next M m)) = true.

Definition record_driven (M : RCM) (B : BaseMachine) (C : BaseCover M B)
    {A : Type} (rec : rc_state M -> A) : Prop :=
  exists f : b_state B -> A -> A,
    forall m, rec (rc_next M m) = f (base_state M B C m) (rec m).

Definition reachable_strict_record_write (M : RCM) {A : Type}
    (rec : rc_state M -> A) : Prop :=
  exists m n, rc_init M m /\
    rec (rc_run M n m) <> rec (rc_next M (rc_run M n m)).

(** * Threshold latches *)

Definition threshold_latch_factorization
    (M : RCM) (B : BaseMachine) (C : BaseCover M B)
    {A : Type} (P : BoolPartialOrder A) (rec : rc_state M -> A)
    (h : A -> b_state B -> A -> bool) : Prop :=
  forall m a,
    gr_leq P a (rec (rc_next M m)) =
    orb (gr_leq P a (rec m))
        (h a (base_state M B C m) (rec m)).

(** The schedule charges every strict growth of the multi-valued record. *)
Definition record_schedule_priced (M : RCM) {A : Type}
    (rec : rc_state M -> A) : Prop :=
  ledger_carried M /\
  forall m, rec m <> rec (rc_next M m) -> step_cost M m >= 1.

(** Equivalently, the schedule charges whenever any threshold latch sets. *)
Definition threshold_schedule_priced (M : RCM) {A : Type}
    (P : BoolPartialOrder A) (rec : rc_state M -> A) : Prop :=
  ledger_carried M /\
  forall m a,
    gr_leq P a (rec m) = false ->
    gr_leq P a (rec (rc_next M m)) = true ->
    step_cost M m >= 1.

Definition HonestGrowingExtension
    (M : RCM) (B : BaseMachine) (C : BaseCover M B)
    {A : Type} (P : BoolPartialOrder A) (rec : rc_state M -> A) : Prop :=
  record_driven M B C rec /\
  record_grows M P rec /\
  record_schedule_priced M rec /\
  reachable_strict_record_write M rec.

(** Exact positive decomposition target: base + threshold latches + schedule. *)
Definition growing_record_decomposes : Prop :=
  forall (M : RCM) (B : BaseMachine) (C : BaseCover M B)
         (A : Type) (P : BoolPartialOrder A) (rec : rc_state M -> A),
    HonestGrowingExtension M B C P rec ->
    exists h,
      threshold_latch_factorization M B C P rec h /\
      record_schedule_priced M rec.

(** The complete family of thresholds determines the ordered record value. *)
Definition thresholds_determine_record : Prop :=
  forall (A : Type) (P : BoolPartialOrder A) (x y : A),
    (forall a, gr_leq P a x = gr_leq P a y) -> x = y.

(** On a growing record, pricing strict writes and threshold flips agrees. *)
Definition record_price_iff_threshold_price : Prop :=
  forall (M : RCM) (A : Type) (P : BoolPartialOrder A)
         (rec : rc_state M -> A),
    record_grows M P rec ->
    (record_schedule_priced M rec <->
     threshold_schedule_priced M P rec).

(** * Does one Boolean latch suffice? *)

Definition single_latch_carries
    (M : RCM) (B : BaseMachine) (C : BaseCover M B)
    {A : Type} (rec : rc_state M -> A) : Prop :=
  exists (h : b_state B -> bool) (latch : rc_state M -> bool)
         (decode : b_state B -> bool -> A),
    (forall m,
      latch (rc_next M m) =
      orb (latch m) (h (base_state M B C m))) /\
    (forall m, rec m = decode (base_state M B C m) (latch m)).

Definition one_latch_suffices : Prop :=
  forall (M : RCM) (B : BaseMachine) (C : BaseCover M B)
         (A : Type) (P : BoolPartialOrder A) (rec : rc_state M -> A),
    HonestGrowingExtension M B C P rec ->
    single_latch_carries M B C rec.

(** * Finite Boolean lower bound *)

Definition bits_le (u v : list bool) : Prop :=
  length u = length v /\
  forall n, nth n u false = true -> nth n v false = true.

Fixpoint bits_chain (vs : list (list bool)) : Prop :=
  match vs with
  | [] => True
  | u :: rest =>
      match rest with
      | [] => True
      | v :: _ => bits_le u v /\ bits_chain rest
      end
  end.

Definition chain_needs_bits : Prop :=
  forall (k : nat) (vs : list (list bool)),
    Forall (fun v => length v = k) vs ->
    bits_chain vs -> NoDup vs ->
    length vs <= S k.
