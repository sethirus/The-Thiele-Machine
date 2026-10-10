(** Two-state calorimeter definitions. *)

From Coq Require Import Reals.
Local Open Scope R_scope.

(* SCOPE NOTE: standalone proof scope.  The parameters are physical inputs;
   no machine ledger fixes their units. *)

Definition two_state_hamiltonian (Delta : R) (excited : bool) : R :=
  if excited then Delta else 0.

Definition mean_register_energy (Delta p_excited : R) : R :=
  Delta * p_excited.

Definition master_next
    (dt k01 k10 p_excited : R) : R :=
  p_excited + dt * (k01 * (1 - p_excited) - k10 * p_excited).

Definition bath_heat_fixed_hamiltonian
    (Delta p_before p_after : R) : R :=
  mean_register_energy Delta p_before - mean_register_energy Delta p_after.

Definition canonical_reset_before : R := / 2.
(* SAFE: a completed reset leaves the register in the ground state, so the
   excited-state probability after the step is zero. *)
Definition canonical_reset_after : R := 0.
Definition canonical_reset_dt : R := 1.
(* These rates are bookkeeping numbers: they satisfy detailed balance at no
   finite gap and positive temperature ([canonical_rates_break_detailed_balance]).
   The driven protocol below is the one with a thermal premise. *)
(* SAFE: the canonical reset drives only the downward transition; the upward
   rate is zero by construction. *)
Definition canonical_reset_k01 : R := 0.
Definition canonical_reset_k10 : R := 1.
Definition canonical_reset_mu : nat := 1.

(** * The driven reset, with a thermal premise *)

(* Below, kT is the product k_B * T, the bath's thermal energy. *)

(** The excited population at equilibrium with the bath at gap Delta. *)
Definition gibbs_excited (kT Delta : R) : R := / (1 + exp (Delta / kT)).

(** The register's free energy at gap Delta, measured so that the ground
    state has energy 0: - kT ln (1 + exp (- Delta / kT)). *)
Definition two_state_free_energy (kT Delta : R) : R :=
  - kT * ln (1 + exp (- (Delta / kT))).

(** Detailed balance at gap Delta: the up rate is the down rate times the
    Boltzmann factor. *)
Definition detailed_balance (kT Delta k01 k10 : R) : Prop :=
  k01 = k10 * exp (- (Delta / kT)).

(** The driven reset along a gap schedule g. Step m raises the gap from
    g m to g (S m) while the population holds at its equilibrium value for
    g m (the work done on the register), then the register settles at the
    new gap to its equilibrium population (the heat to the bath). *)
Fixpoint driven_work (kT : R) (g : nat -> R) (n : nat) : R :=
  match n with
  | O => 0
  | S m => driven_work kT g m + gibbs_excited kT (g m) * (g (S m) - g m)
  end.

Fixpoint driven_heat (kT : R) (g : nat -> R) (n : nat) : R :=
  match n with
  | O => 0
  | S m => driven_heat kT g m
             + g (S m) * (gibbs_excited kT (g m) - gibbs_excited kT (g (S m)))
  end.

(** N equal raises from gap 0 to gap D. *)
Definition uniform_schedule (D : R) (N : nat) (m : nat) : R := D * INR m / INR N.
