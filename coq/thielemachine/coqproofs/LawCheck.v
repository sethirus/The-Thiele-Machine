Require Import Coq.QArith.QArith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Zbool.
Require Import Coq.Lists.List.

Import ListNotations.

Local Open Scope Q_scope.
Local Open Scope Z_scope.

Record UpdateCoefficients := {
  uc_tp1 : Q;
  uc_t : Q;
  uc_tm1 : Q;
  uc_sp : Q;
  uc_sm : Q
}.

Record LagrangianCoefficients := {
  lag_kinetic : Q;
  lag_potential : Q
}.

Definition scale_update (scale : Q) (coeffs : UpdateCoefficients) : UpdateCoefficients :=
  {| uc_tp1 := scale * coeffs.(uc_tp1);
     uc_t := scale * coeffs.(uc_t);
     uc_tm1 := scale * coeffs.(uc_tm1);
     uc_sp := scale * coeffs.(uc_sp);
     uc_sm := scale * coeffs.(uc_sm) |}.

Definition derived_from_lagrangian (lag : LagrangianCoefficients) : UpdateCoefficients :=
  {| uc_tp1 := lag.(lag_kinetic);
     uc_t := 0;
     uc_tm1 := lag.(lag_kinetic);
     uc_sp := - lag.(lag_potential);
     uc_sm := - lag.(lag_potential) |}.

Definition update_equal (u v : UpdateCoefficients) : Prop :=
  uc_tp1 u == uc_tp1 v /\
  uc_t u == uc_t v /\
  uc_tm1 u == uc_tm1 v /\
  uc_sp u == uc_sp v /\
  uc_sm u == uc_sm v.

Fixpoint difference_constant_aux (xs ys : list Q) (d : Q) : Prop :=
  match xs, ys with
  | [], [] => True
  | x :: xs', y :: ys' => (x - y) == d /\ difference_constant_aux xs' ys' d
  | _, _ => False
  end.

Definition difference_constant (xs ys : list Q) : Prop :=
  match xs, ys with
  | [], [] => True
  | x :: xs', y :: ys' => difference_constant_aux xs' ys' (x - y)
  | _, _ => False
  end.

Fixpoint recursion_matches (a b : Q) (energies momenta fluxes : list Q) : Prop :=
  match energies, momenta, fluxes with
  | [], [], [] => True
  | e :: es, m :: ms, f :: fs =>
      f == a * e + b * m /\ recursion_matches a b es ms fs
  | _, _, _ => False
  end.

Definition StepTerm := (Z * Z * Q)%type.

Fixpoint coeff_lookup (dt dx : Z) (poly : list StepTerm) : Q :=
  match poly with
  | [] => 0
  | (dt', dx', coeff) :: rest =>
      if Z.eqb dt dt' && Z.eqb dx dx'
      then coeff + coeff_lookup dt dx rest
      else coeff_lookup dt dx rest
  end.

Definition pair_eqb (p q : Z * Z) : bool :=
  Z.eqb (fst p) (fst q) && Z.eqb (snd p) (snd q).

Fixpoint add_support (pair : Z * Z) (support : list (Z * Z)) : list (Z * Z) :=
  match support with
  | [] => [pair]
  | head :: tail =>
      if pair_eqb pair head
      then head :: tail
      else head :: add_support pair tail
  end.

Fixpoint support_of (poly : list StepTerm) : list (Z * Z) :=
  match poly with
  | [] => []
  | (dt, dx, _) :: rest => add_support (dt, dx) (support_of rest)
  end.

Fixpoint support_union (polys : list (list StepTerm)) : list (Z * Z) :=
  match polys with
  | [] => []
  | p :: ps => fold_right add_support (support_union ps) (support_of p)
  end.

Fixpoint coeffs_match (update laxL laxM : list StepTerm) (pairs : list (Z * Z)) : Prop :=
  match pairs with
  | [] => True
  | (dt, dx) :: rest =>
      coeff_lookup dt dx update == coeff_lookup dt dx laxL - coeff_lookup dt dx laxM /\
      coeffs_match update laxL laxM rest
  end.

Record LawSummary := {
  summary_update : UpdateCoefficients;
  summary_lagrangian : LagrangianCoefficients;
  summary_scale : Q;
  summary_energy : list Q;
  summary_momentum : list Q;
  summary_flux : list Q;
  summary_recursion : Q * Q;
  summary_update_poly : list StepTerm;
  summary_lax_L : list StepTerm;
  summary_lax_M : list StepTerm
}.

Definition scale_consistent (summary : LawSummary) : Prop :=
  update_equal
    summary.(summary_update)
    (scale_update summary.(summary_scale)
      (derived_from_lagrangian summary.(summary_lagrangian))).

Definition energy_momentum_difference_constant (summary : LawSummary) : Prop :=
  difference_constant summary.(summary_energy) summary.(summary_momentum).

Definition recursion_witness (summary : LawSummary) : Prop :=
  let '(a, b) := summary.(summary_recursion) in
  recursion_matches a b
    summary.(summary_energy)
    summary.(summary_momentum)
    summary.(summary_flux).

Definition update_matches_lax (summary : LawSummary) : Prop :=
  coeffs_match
    summary.(summary_update_poly)
    summary.(summary_lax_L)
    summary.(summary_lax_M)
    (support_union
       [summary.(summary_update_poly);
        summary.(summary_lax_L);
        summary.(summary_lax_M)]).

Definition law_summary_verified (summary : LawSummary) : Prop :=
  scale_consistent summary /\
  energy_momentum_difference_constant summary /\
  recursion_witness summary /\
  update_matches_lax summary.

Close Scope Z_scope.
Close Scope Q_scope.
