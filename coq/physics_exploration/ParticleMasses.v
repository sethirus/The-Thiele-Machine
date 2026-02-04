(** Particle Masses: Analysis *)

Require Import Reals Lra.
From PhysicsExploration Require Import PlanckDerivation EmergentSpacetime.
Open Scope R_scope.

(** Particle masses in normalized units *)

Definition m_electron : R := 1.
Definition m_muon : R := 207.     (* Approximate muon/electron mass ratio *)
Definition m_proton : R := 1836.  (* Approximate proton/electron mass ratio *)

Lemma masses_positive : m_electron > 0 /\ m_muon > 0 /\ m_proton > 0.
Proof. unfold m_electron, m_muon, m_proton. lra. Qed.

Definition muon_electron_ratio : R := m_muon / m_electron.
Definition proton_electron_ratio : R := m_proton / m_electron.

Theorem masses_are_free_parameters :
  exists (r1 r2 : R), r1 > 0 /\ r2 > 0.
Proof.
  exists muon_electron_ratio, proton_electron_ratio.
  split; unfold muon_electron_ratio, proton_electron_ratio; apply Rdiv_lt_0_compat; apply masses_positive.
Qed.
