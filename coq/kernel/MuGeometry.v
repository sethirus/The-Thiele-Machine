From Coq Require Import ZArith Lia.

Require Import VMState.
Require Import SimulationProof.
Require Import MuInformation.

(** * μ-Geometry (Phase II)

    We derive a simple, fully constructive geometry from the μ accumulator.

    This is intentionally minimal and kernel-native:
    - distance between states is absolute μ difference
    - it is a genuine metric on states projected to μ
    - along executions, distance equals the μ-information injected
*)

Module MuGeometry.

Definition mu_total_z (s : VMState) : Z := Z.of_nat (mu_total s).

Definition mu_distance (s1 s2 : VMState) : Z :=
  Z.abs (mu_total_z s2 - mu_total_z s1).

Lemma mu_distance_nonneg : forall s1 s2, (0 <= mu_distance s1 s2)%Z.
Proof.
  intros. unfold mu_distance. apply Z.abs_nonneg.
Qed.

Lemma mu_distance_refl : forall s, mu_distance s s = 0%Z.
Proof.
  intro s.
  unfold mu_distance.
  rewrite Z.sub_diag.
  exact Z.abs_0.
Qed.

Lemma mu_distance_sym : forall s1 s2, mu_distance s1 s2 = mu_distance s2 s1.
Proof.
  intros s1 s2.
  unfold mu_distance.
  replace (mu_total_z s2 - mu_total_z s1)%Z with (-(mu_total_z s1 - mu_total_z s2))%Z by ring.
  rewrite Z.abs_opp.
  reflexivity.
Qed.

Lemma mu_distance_triangle :
  forall a b c,
    (mu_distance a c <= mu_distance a b + mu_distance b c)%Z.
Proof.
  intros a b c.
  unfold mu_distance.
  (* |(c-a)| = |(c-b) + (b-a)| <= |c-b| + |b-a| *)
  replace (mu_total_z c - mu_total_z a)%Z with
    ((mu_total_z c - mu_total_z b) + (mu_total_z b - mu_total_z a))%Z by ring.
  eapply Z.le_trans.
  - apply Z.abs_triangle.
  - lia.
Qed.

(** Along a bounded execution, μ only increases, so the absolute difference is
    exactly the injected μ-information. *)
Lemma mu_distance_run_vm :
  forall fuel trace s,
    mu_distance s (run_vm fuel trace s) = Z.of_nat (mu_info_run_vm fuel trace s).
Proof.
  intros fuel trace s.
  unfold mu_distance, mu_total_z.
  rewrite run_vm_mu_total_decomposes.
  (* abs( (mu+s) - mu ) = abs(mu_info) = mu_info *)
  replace (Z.of_nat (mu_total s + mu_info_run_vm fuel trace s) - Z.of_nat (mu_total s))%Z with
    (Z.of_nat (mu_info_run_vm fuel trace s))%Z.
  - apply Z.abs_eq.
    lia.
  - rewrite Nat2Z.inj_add.
    lia.
Qed.

End MuGeometry.
