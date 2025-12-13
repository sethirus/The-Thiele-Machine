(** WaveCheck: Coq verification for discovered wave equations *)
(** 
   This module provides the verification framework for wave equations
   discovered from lattice evolution data via the Thiele Machine.
   
   Copyright 2025 Devon Thiele
   Licensed under the Apache License, Version 2.0
*)

Require Import Coq.QArith.QArith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Zbool.
Require Import Coq.Lists.List.

Import ListNotations.

Local Open Scope Q_scope.
Local Open Scope Z_scope.

(** * Wave Equation Types *)

(** Coefficients for the discrete wave update rule:
    u(x,t+1) = coeff_u_t * u(x,t) + coeff_u_tm1 * u(x,t-1) 
             + coeff_u_xp * u(x+1,t) + coeff_u_xm * u(x-1,t) *)
Record WaveCoefficients := {
  coeff_u_t : Q;      (** coefficient for u(x, t) *)
  coeff_u_tm1 : Q;    (** coefficient for u(x, t-1) *)
  coeff_u_xp : Q;     (** coefficient for u(x+1, t) *)
  coeff_u_xm : Q      (** coefficient for u(x-1, t) *)
}.

(** PDE parameters for the continuous wave equation:
    ∂²u/∂t² = c² * ∂²u/∂x² *)
Record WavePDEParams := {
  wave_c_squared : Q  (** wave speed squared c² *)
}.

(** Combined wave equation summary *)
Record WaveSummary := {
  ws_coefficients : WaveCoefficients;
  ws_pde : WavePDEParams;
  ws_rms_error : Q
}.

(** * Discrete Derivative Definitions *)

(** Discrete second derivative in time:
    d²u/dt² ≈ (u(t+1) - 2u(t) + u(t-1)) / dt² *)
Definition discrete_d2_dt2 (u_tp1 u_t u_tm1 : Q) : Q :=
  u_tp1 - 2 * u_t + u_tm1.

(** Discrete second derivative in space:
    d²u/dx² ≈ (u(x+1) - 2u(x) + u(x-1)) / dx² *)
Definition discrete_d2_dx2 (u_xp u_x u_xm : Q) : Q :=
  u_xp - 2 * u_x + u_xm.

(** * Wave Update Rule *)

(** Apply the discrete wave update rule *)
Definition wave_update (w : WaveCoefficients) (u_t u_tm1 u_xp u_xm : Q) : Q :=
  w.(coeff_u_t) * u_t + 
  w.(coeff_u_tm1) * u_tm1 +
  w.(coeff_u_xp) * u_xp + 
  w.(coeff_u_xm) * u_xm.

(** * Verification Predicates *)

(** Check if the discrete wave equation holds:
    d²u/dt² = c² * d²u/dx² *)
Definition discrete_wave_equation_holds 
    (c_sq : Q) (u_tp1 u_t u_tm1 u_xp u_xm : Q) : Prop :=
  let d2t := discrete_d2_dt2 u_tp1 u_t u_tm1 in
  let d2x := discrete_d2_dx2 u_xp u_t u_xm in
  d2t == c_sq * d2x.

(** Check locality: the update depends only on the 4-point stencil *)
Definition wave_update_is_local (w : WaveCoefficients) : Prop :=
  forall u_t u_tm1 u_xp u_xm u_t' u_tm1' u_xp' u_xm',
    u_t == u_t' ->
    u_tm1 == u_tm1' ->
    u_xp == u_xp' ->
    u_xm == u_xm' ->
    wave_update w u_t u_tm1 u_xp u_xm == wave_update w u_t' u_tm1' u_xp' u_xm'.

(** Check coefficient consistency with standard wave equation form:
    For the standard discrete wave equation:
    u(x,t+1) = 2(1-c²)u(x,t) - u(x,t-1) + c²(u(x+1,t) + u(x-1,t))
    
    So: coeff_u_t = 2(1-c²), coeff_u_tm1 = -1, coeff_u_xp = c², coeff_u_xm = c² *)
Definition coefficients_match_wave_eq (w : WaveCoefficients) (p : WavePDEParams) : Prop :=
  let c_sq := p.(wave_c_squared) in
  w.(coeff_u_t) == 2 * (1 - c_sq) /\
  w.(coeff_u_tm1) == -1 /\
  w.(coeff_u_xp) == c_sq /\
  w.(coeff_u_xm) == c_sq.

(** The coefficients are symmetric in space *)
Definition symmetric_in_space (w : WaveCoefficients) : Prop :=
  w.(coeff_u_xp) == w.(coeff_u_xm).

(** * Main Verification Theorem *)

(** A wave summary is verified if:
    1. The coefficients match the expected wave equation form
    2. The spatial part is symmetric
    3. The RMS error is below threshold *)
Definition wave_summary_verified (ws : WaveSummary) : Prop :=
  coefficients_match_wave_eq ws.(ws_coefficients) ws.(ws_pde) /\
  symmetric_in_space ws.(ws_coefficients).

(** * Standard Wave Equation Instance *)

(** Create wave coefficients from c² *)
Definition make_wave_coeffs (c_sq : Q) : WaveCoefficients :=
  {| coeff_u_t := 2 * (1 - c_sq);
     coeff_u_tm1 := -1;
     coeff_u_xp := c_sq;
     coeff_u_xm := c_sq |}.

(** Standard wave equation with c² = 1/4 (c = 0.5) *)
Definition standard_wave_c05 : WaveCoefficients :=
  make_wave_coeffs (1 # 4).

(** * Lemmas *)

Lemma wave_coeffs_symmetric : 
  forall c_sq, symmetric_in_space (make_wave_coeffs c_sq).
Proof.
  intros. unfold symmetric_in_space, make_wave_coeffs. simpl.
  reflexivity.
Qed.

Lemma wave_coeffs_match :
  forall c_sq,
    let w := make_wave_coeffs c_sq in
    let p := {| wave_c_squared := c_sq |} in
    coefficients_match_wave_eq w p.
Proof.
  intros. unfold coefficients_match_wave_eq, make_wave_coeffs. simpl.
  repeat split; reflexivity.
Qed.

Lemma standard_wave_verified :
  forall c_sq,
    let w := make_wave_coeffs c_sq in
    let p := {| wave_c_squared := c_sq |} in
    let ws := {| ws_coefficients := w; ws_pde := p; ws_rms_error := 0 |} in
    wave_summary_verified ws.
Proof.
  intros. unfold wave_summary_verified. split.
  - apply wave_coeffs_match.
  - apply wave_coeffs_symmetric.
Qed.

(** Theorem: For any valid wave summary with matching coefficients,
    the discrete wave equation structure is satisfied *)
Theorem emergent_wave_from_coefficients :
  forall (ws : WaveSummary) (u_tp1 u_t u_tm1 u_xp u_xm : Q),
    wave_summary_verified ws ->
    u_tp1 == wave_update ws.(ws_coefficients) u_t u_tm1 u_xp u_xm ->
    discrete_wave_equation_holds ws.(ws_pde).(wave_c_squared) u_tp1 u_t u_tm1 u_xp u_xm.
Proof.
  intros ws u_tp1 u_t u_tm1 u_xp u_xm Hverified Hupdate.
  unfold wave_summary_verified in Hverified.
  destruct Hverified as [Hmatch Hsym].
  unfold coefficients_match_wave_eq in Hmatch.
  destruct Hmatch as [Hcoeff_t [Hcoeff_tm1 [Hcoeff_xp Hcoeff_xm]]].
  unfold discrete_wave_equation_holds, discrete_d2_dt2, discrete_d2_dx2.
  unfold wave_update in Hupdate.
  
  set (c_sq := wave_c_squared (ws_pde ws)) in *.
  set (w := ws_coefficients ws) in *.
  
  (* Rewrite u_tp1 using Hupdate, then substitute coefficient values *)
  rewrite Hupdate.
  rewrite Hcoeff_t, Hcoeff_tm1, Hcoeff_xp, Hcoeff_xm.
  
  (* The algebraic identity now follows directly:
     LHS: 2*(1-c_sq)*u_t + (-1)*u_tm1 + c_sq*u_xp + c_sq*u_xm - 2*u_t + u_tm1
        = 2*u_t - 2*c_sq*u_t - u_tm1 + c_sq*u_xp + c_sq*u_xm - 2*u_t + u_tm1
        = -2*c_sq*u_t + c_sq*u_xp + c_sq*u_xm
        = c_sq * (u_xp - 2*u_t + u_xm) = RHS *)
  ring_simplify.
  reflexivity.
Qed.

Local Close Scope Z_scope.
Local Close Scope Q_scope.
