(** Pricing and physics outcomes for the statements of [PricingPhysicsTarget]. *)

From Coq Require Import List Bool Arith Reals Lra Sorting.Permutation.
Import ListNotations.
Open Scope R_scope.

From Kernel Require Import PermanentCertification.
From Kernel Require Import PermanentRecordPricing.
From Kernel Require Import PermanentCertificationEntropy.
From Kernel Require Import PricingPhysicsTarget.

Theorem no_forced_price_beyond_merges :
  forall (S I : Type) (step : S -> I -> S)
         (instr_eq_dec : forall a b : I, {a = b} + {a <> b}),
    no_price_beyond_merges step instr_eq_dec.
Proof.
  intros S I step instr_eq_dec i [Hforced Hinjective].
  apply (proj1 (@forced_priced_iff_merges S I step instr_eq_dec i) Hforced).
  exact Hinjective.
Qed.

Theorem permanent_write_has_logical_payment :
  forall (S I : Type) (step : S -> I -> S) (cert : S -> bool),
    permanent_flip_logical_payment step cert.
Proof.
  intros S I step cert all s i Hfinite Hpermanent Hoff Hon.
  eapply (@permanent_at_flip_is_not_injective S I step cert); eauto.
Qed.

Theorem mu_has_no_intrinsic_joule_value : no_intrinsic_joule_scale.
Proof.
  intros S mu.
  exists (mu_energy_at_scale mu 1), (mu_energy_at_scale mu 2).
  intros s Hmu. unfold mu_energy_at_scale. rewrite Hmu. simpl.
  split; [ring |]. split; [ring | lra].
Qed.

Theorem calibrated_mu_landauer_energy :
  forall k_B T : R, mu_landauer_calibration k_B T.
Proof.
  intros k_B T S mu s Hmu.
  unfold mu_landauer_calibration, mu_energy_at_scale in *.
  rewrite Hmu. simpl. ring.
Qed.

(** Entropy is invariant under reordering the finite state enumeration. This
    is the representation invariance used by the physical reading below. *)
Theorem semantics_entropy_permutation_invariant :
  forall (S : Type) (all all' : list S) (p : S -> R),
    Permutation all all' -> entropy all p = entropy all' p.
Proof.
  intros S all all' p Hperm.
  unfold entropy. apply rsum_permutation. exact Hperm.
Qed.

(** The heat conclusion retains [landauer_heat] as an explicit premise and
    uses the finite-state permanent-record entropy theorem. *)
Theorem permanence_heat_floor_uses_landauer : landauer_permanence_heat_floor.
Proof.
  intros S I step cert eq_dec all i F kT heat Hfin Hperm Hfl Hpos HkT.
  cbv zeta.
  intros Hlandauer.
  eapply (@permanent_flip_heat_floor S I step cert eq_dec all i F kT heat);
    eauto.
Qed.

Print Assumptions no_forced_price_beyond_merges.
Print Assumptions permanent_write_has_logical_payment.
Print Assumptions mu_has_no_intrinsic_joule_value.
Print Assumptions calibrated_mu_landauer_energy.
Print Assumptions semantics_entropy_permutation_invariant.
Print Assumptions permanence_heat_floor_uses_landauer.
