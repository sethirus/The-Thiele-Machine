(** Statement vocabulary for the pricing and physics results. *)

From Coq Require Import List Bool Arith Reals.
Import ListNotations.
Open Scope R_scope.

From Kernel Require Import PermanentCertification.
From Kernel Require Import PermanentRecordPricing.
From Kernel Require Import PermanentCertificationEntropy.

Definition no_price_beyond_merges
    {S I : Type} (step : S -> I -> S)
    (instr_eq_dec : forall a b : I, {a = b} + {a <> b}) : Prop :=
  forall i, ~ (forced_priced step i /\ step_injective step i).

Definition permanent_flip_logical_payment
    {S I : Type} (step : S -> I -> S) (cert : S -> bool) : Prop :=
  forall (all : list S) s i,
    finite_states all ->
    permanent_at step cert i ->
    cert s = false ->
    cert (step s i) = true ->
    ~ step_injective step i.

(** A ledger reading in natural units, scaled to energy by a chosen factor. *)
Definition mu_energy_at_scale {S : Type} (mu : S -> nat) (scale : R) (s : S) : R :=
  INR (mu s) * scale.

(** For any machine with a ledger reading, two scales assign one unit
    different energies: the unit carries no joule value of its own. *)
Definition no_intrinsic_joule_scale : Prop :=
  forall (S : Type) (mu : S -> nat),
    exists e1 e2 : S -> R,
      forall s, mu s = 1%nat ->
        e1 s = 1 /\ e2 s = 2 /\ e1 s <> e2 s.

Definition mu_landauer_calibration (k_B T : R) : Prop :=
  forall (S : Type) (mu : S -> nat) (s : S), mu s = 1%nat ->
    mu_energy_at_scale mu (k_B * T * ln 2) s = k_B * T * ln 2.

Definition landauer_permanence_heat_floor : Prop :=
  forall (S I : Type) (step : S -> I -> S) (cert : S -> bool)
         (eq_dec : forall a b : S, {a = b} + {a <> b})
         (all : list S) (i : I) (F : list S) (kT heat : R),
    finite_states all ->
    permanent step cert ->
    flip_list step cert i F ->
    (0 < length F)%nat ->
    0 <= kT ->
    let C := certified_states S cert all in
    let p := uniform_on eq_dec (C ++ F) in
    landauer_heat kT heat
      (entropy all p - entropy all (push eq_dec all (fun s => step s i) p)) ->
    heat >= kT * ln (INR (length C + length F) / INR (length C)).
