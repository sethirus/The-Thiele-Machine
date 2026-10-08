(** NecFCalorimeter: the heat is fixed by the chosen gap, at the limit.

    - Part (4) of the calorimeter theorem asks for k_B > 0 and T > 0. What it
      needs is exactly k_B T > 0: the gap k_B T ln 2 gives heat strictly below
      k_B T ln 2 if and only if k_B T > 0 ([nec_f_smaller_gap_iff]). The signs
      of the two factors separately do not matter
      ([nec_f_smaller_gap_negative_pair]).
    - Part (5) says two gaps give different heats. Every two different gaps
      do: the heat determines the gap ([nec_f_heat_determines_gap]). And the
      gap 2 k_B T ln 2 is the only one giving heat k_B T ln 2
      ([nec_f_landauer_gap_unique]).
    - The calibration: any two different scales give different energies to
      every state with a nonzero count, not just to states with one mark
      ([nec_f_scales_always_disagree]).

    This file uses the real numbers and rests on the standard library's
    classical axioms for them. *)

From Coq Require Import Reals Lra.
From Kernel Require Import CalorimeterProtocolTarget CalorimeterProtocol.
From Kernel Require Import PricingPhysicsTarget.

Open Scope R_scope.

Notation nec_f_heat D := (bath_heat_fixed_hamiltonian D canonical_reset_before canonical_reset_after).

Theorem nec_f_smaller_gap_iff :
  forall kB T, nec_f_heat (kB * T * ln 2) < kB * T * ln 2 <-> 0 < kB * T.
Proof.
  intros kB T. rewrite canonical_reset_heat_exact. pose proof ln_two_positive as Hl.
  split; intro H.
  - destruct (Rle_or_lt (kB * T) 0) as [Hle | Hlt]; [| exact Hlt].
    exfalso. assert (kB * T * ln 2 <= 0) by nra. lra.
  - assert (0 < kB * T * ln 2) by (apply Rmult_lt_0_compat; assumption). lra.
Qed.

Theorem nec_f_smaller_gap_negative_pair :
  nec_f_heat ((-1) * (-1) * ln 2) < (-1) * (-1) * ln 2.
Proof. apply nec_f_smaller_gap_iff. lra. Qed.

Theorem nec_f_heat_determines_gap : forall D1 D2, nec_f_heat D1 = nec_f_heat D2 -> D1 = D2.
Proof. intros D1 D2 H. rewrite !canonical_reset_heat_exact in H. lra. Qed.

Theorem nec_f_landauer_gap_unique :
  forall kB T D, nec_f_heat D = kB * T * ln 2 <-> D = 2 * kB * T * ln 2.
Proof.
  intros kB T D. rewrite canonical_reset_heat_exact. split; intro H; [lra | subst; field].
Qed.

Theorem nec_f_scales_always_disagree :
  forall (S : Type) (mu : S -> nat) (a b : R) (s : S),
    a <> b -> mu s <> 0%nat -> mu_energy_at_scale mu a s <> mu_energy_at_scale mu b s.
Proof.
  intros S mu a b s Hab Hmu E. unfold mu_energy_at_scale in E.
  assert (Hp : 0 < INR (mu s)) by (apply lt_0_INR; destruct (mu s); [contradiction | apply Nat.lt_0_succ]).
  apply Hab. apply (Rmult_eq_reg_l (INR (mu s))); [lra | lra].
Qed.

Print Assumptions nec_f_smaller_gap_iff.
Print Assumptions nec_f_smaller_gap_negative_pair.
Print Assumptions nec_f_heat_determines_gap.
Print Assumptions nec_f_landauer_gap_unique.
Print Assumptions nec_f_scales_always_disagree.
