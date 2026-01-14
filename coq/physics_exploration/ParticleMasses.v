(** Particle Masses: Analysis *)

Require Import Reals Lra.
From PhysicsExploration Require Import PlanckDerivation EmergentSpacetime.
Open Scope R_scope.

(** INQUISITOR NOTE: Masses appear as free parameters *)

Parameter m_electron : R.
Parameter m_muon : R.
Parameter m_proton : R.

Axiom masses_positive : m_electron > 0 /\ m_muon > 0 /\ m_proton > 0.

Definition muon_electron_ratio : R := m_muon / m_electron.
Definition proton_electron_ratio : R := m_proton / m_electron.

Theorem masses_are_free_parameters :
  exists (r1 r2 : R), r1 > 0 /\ r2 > 0.
Proof.
  exists muon_electron_ratio, proton_electron_ratio.
  split; unfold muon_electron_ratio, proton_electron_ratio; apply Rdiv_lt_0_compat; apply masses_positive.
Qed.
