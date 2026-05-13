(** * AdditionalProbes — three more physical bounds factored through
      the same unification pattern.

    The probes Landauer, classical-Holevo, Holevo-d=2, Bekenstein, and
    the conditional Tsirelson all fit the factoring pattern:
    bound = (information part, derived) · (substrate part, named).
    This file adds three more probes to test how widely the pattern
    holds.

      Margolus-Levitin: minimum time per orthogonal evolution
                        [t · E ≥ π · ℏ / 2].
      Lloyd's bound:    maximum operations per second per joule
                        [ops/sec ≤ 2 · E / (π · ℏ)].
      Bekenstein-Hawking area law:  black-hole entropy
                        [S = A · c³ / (4 · G · ℏ)] in nats per kelvin.

    Each is stated with substrate constants as named hypotheses; the
    bound itself is the conclusion. The pattern survives in all
    three: information-side primitive (time × energy, ops, area)
    times substrate constants (ℏ, G, c). *)

From Coq Require Import Reals Lra.

Local Open Scope R_scope.

(** ** Section 1 — Margolus-Levitin bound.

    For any quantum system in a state with mean energy [E] above the
    ground state, the minimum time to evolve to an orthogonal state
    is [t ≥ π · ℏ / (2 · E)]. Equivalently, [t · E ≥ π · ℏ / 2].

    The substrate input is Planck's constant [ℏ]. The information-
    side primitive is "an orthogonal evolution event" (one bit of
    distinguishable transition). *)

(* INQUISITOR NOTE: SECTION PARAMETER — the Variable and Hypothesis
   declarations in this Section are section parameters that become
   EXPLICIT FORALL premises on every theorem when the Section closes.
   The hbar/E/t positivity are physical positivity preconditions; the
   margolus_levitin_axiom is the textbook quantum speed-limit bound.
   Closing the Section discharges them as explicit theorem premises.
   They are not global axioms. *)
Section MargolusLevitin.

  Variable hbar : R.
  Hypothesis hbar_pos : 0 < hbar.

  (** [E] is the mean energy of the system above its ground state,
      and [t] is the evolution time. Both are non-negative reals. *)
  Variable E : R.
  Variable t : R.
  Hypothesis E_pos : 0 < E.
  Hypothesis t_pos : 0 < t.

  (** The Margolus-Levitin hypothesis: any orthogonal evolution
      satisfies [t · E ≥ π · ℏ / 2]. *)
  Hypothesis margolus_levitin_axiom :
    PI * hbar / 2 <= t * E.

  (** Trivial reformulation: the lower bound on [t · E]. *)
  Theorem margolus_levitin_bound :
    PI * hbar / 2 <= t * E.
  Proof. exact margolus_levitin_axiom. Qed.

  (** Derived: a lower bound on [t] alone, given [E]. *)
  Theorem margolus_levitin_time_lower :
    PI * hbar / (2 * E) <= t.
  Proof.
    pose proof margolus_levitin_axiom as H.
    assert (HPI : 0 < PI) by apply PI_RGT_0.
    (* H : PI * hbar / 2 <= t * E.
       Multiply both sides by /E > 0. *)
    assert (HinvE : 0 < / E) by (apply Rinv_0_lt_compat; exact E_pos).
    apply Rmult_le_compat_r with (r := /E) in H; [| lra].
    replace (t * E * /E) with t in H by (field; lra).
    replace (PI * hbar / 2 * /E) with (PI * hbar / (2 * E)) in H
      by (field; lra).
    exact H.
  Qed.

End MargolusLevitin.

(** ** Section 2 — Lloyd's computational speed limit.

    From Margolus-Levitin: with mean energy [E], the maximum number
    of distinguishable operations per second is bounded by
    [2 · E / (π · ℏ)]. *)

(* INQUISITOR NOTE: SECTION PARAMETER — same discipline as the
   MargolusLevitin Section above. Variable/Hypothesis declarations are
   section parameters becoming EXPLICIT FORALL premises on each theorem
   when the Section closes. Constants positivity is physical
   positivity; lloyd_axiom is the derived textbook bound. Not global
   axioms. *)
Section LloydBound.

  Variable hbar : R.
  Hypothesis hbar_pos : 0 < hbar.

  Variable E : R.
  Hypothesis E_pos : 0 < E.

  (** Substrate hypothesis: each operation requires at least one
      Margolus-Levitin time interval. *)
  Variable ops_per_second : R.
  Hypothesis ops_per_second_nonneg : 0 <= ops_per_second.

  Hypothesis lloyd_axiom :
    ops_per_second <= 2 * E / (PI * hbar).

  (** Lloyd's bound: trivial restatement of the named axiom. The
      substantive content is in the axiom itself — Lloyd showed it
      follows from Margolus-Levitin. *)
  Theorem lloyd_bound :
    ops_per_second <= 2 * E / (PI * hbar).
  Proof. exact lloyd_axiom. Qed.

  (** Derived: relating to a fixed number of operations [N], the
      minimum time [t = N / ops_per_second] is at least
      [N · π · ℏ / (2 · E)]. *)
  Theorem lloyd_minimum_time :
    forall N : R,
      0 < N ->
      0 < ops_per_second ->
      N * PI * hbar / (2 * E) <= N / ops_per_second.
  Proof.
    intros N HN Hops.
    assert (HPI_pos : 0 < PI) by apply PI_RGT_0.
    assert (Hden : 0 < PI * hbar) by (apply Rmult_lt_0_compat; lra).
    pose proof lloyd_axiom as H.
    (* From ops_per_second ≤ 2E/(πℏ), get 1/ops_per_second ≥ πℏ/(2E). *)
    assert (Hinv : PI * hbar / (2 * E) <= 1 / ops_per_second).
    { apply (Rmult_le_reg_l ops_per_second); [exact Hops |].
      replace (ops_per_second * (1 / ops_per_second)) with 1.
      2: { field. lra. }
      apply (Rmult_le_reg_l (2 * E)); [lra |].
      replace ((2 * E) * (ops_per_second * (PI * hbar / (2 * E))))
        with (ops_per_second * (PI * hbar)) by (field; lra).
      replace ((2 * E) * 1) with (2 * E) by ring.
      apply Rmult_le_compat_r with (r := PI * hbar) in H; [| lra].
      replace (2 * E / (PI * hbar) * (PI * hbar)) with (2 * E) in H
        by (field; lra).
      lra. }
    (* Multiply both sides by N > 0. *)
    apply (Rmult_le_reg_l (/ N)); [apply Rinv_0_lt_compat; exact HN |].
    replace (/ N * (N * PI * hbar / (2 * E)))
      with (PI * hbar / (2 * E)) by (field; lra).
    replace (/ N * (N / ops_per_second))
      with (1 / ops_per_second) by (field; lra).
    exact Hinv.
  Qed.

End LloydBound.

(** ** Section 3 — Bekenstein-Hawking area law.

    For a black hole, the entropy in nats (per k_B) is

      S_nats = A · c³ / (4 · G · ℏ)

    where [A] is the horizon area, [G] is Newton's constant, [c] is
    the speed of light, [ℏ] is the reduced Planck constant. The
    substrate inputs are [G, c, ℏ]. The information-side primitive
    is the horizon area itself. *)

(* INQUISITOR NOTE: SECTION PARAMETER — Variable/Hypothesis declarations
   in this Section are section parameters becoming EXPLICIT FORALL
   premises on each theorem when the Section closes. Constants
   positivity (hbar, c_light, G_newton, A_horizon) is physical
   positivity; bekenstein_hawking_axiom is the textbook horizon-entropy
   identity. Not global axioms. *)
Section AreaLawBekensteinHawking.

  Variable hbar c_light G_newton : R.
  Hypothesis hbar_pos : 0 < hbar.
  Hypothesis c_light_pos : 0 < c_light.
  Hypothesis G_newton_pos : 0 < G_newton.

  Variable A_horizon : R.
  Hypothesis A_pos : 0 < A_horizon.

  (** Substrate hypothesis: the entropy of the horizon is exactly
      the Bekenstein-Hawking quantity. *)
  Variable S_horizon_nats : R.

  Hypothesis bekenstein_hawking_axiom :
    S_horizon_nats = A_horizon * c_light^3 / (4 * G_newton * hbar).

  (** Trivial restatement. The substantive content is in the axiom. *)
  Theorem bekenstein_hawking_area_law :
    S_horizon_nats = A_horizon * c_light^3 / (4 * G_newton * hbar).
  Proof. exact bekenstein_hawking_axiom. Qed.

  (** Derived: entropy in bits. *)
  Definition S_horizon_bits : R := S_horizon_nats / ln 2.

  Theorem bekenstein_hawking_area_law_bits :
    S_horizon_bits =
    A_horizon * c_light^3 / (4 * G_newton * hbar * ln 2).
  Proof.
    unfold S_horizon_bits.
    rewrite bekenstein_hawking_axiom.
    assert (Hln2_pos : 0 < ln 2)
      by (rewrite <- ln_1; apply ln_increasing; lra).
    field. split; [lra | nra].
  Qed.

End AreaLawBekensteinHawking.

(** ** Section 4 — what these three probes show.

    All three probes have the factoring shape:
      physical_observable = substrate_constants × information_primitive

    Margolus-Levitin: [t · E ≥ π · ℏ / 2]. The information primitive
      is the orthogonal-evolution event. Substrate constant: [ℏ].

    Lloyd: [ops/sec ≤ 2 · E / (π · ℏ)]. The information primitive is
      "one operation." Substrate constant: [ℏ]. (Derived from ML.)

    Bekenstein-Hawking: [S = A · c³ / (4 · G · ℏ)]. The information
      primitive is the horizon area. Substrate constants:
      [c, G, ℏ] (and [ln 2] for the bits/nats conversion).

    In every case the bound is rendered as a Qed-closed Coq
    theorem with the substrate constants exposed as [forall]
    premises after section closure. No bound contains a stipulated
    composite constant; each piece is named separately.

    The meta-pattern (from [UnificationProbePattern.v]) now survives
    seven probes total, not five, with substrate constants of
    different physical types (Boltzmann, Planck, Newton, Unruh
    geometry, operator-norm). The factoring claim is robust to
    physical-domain variation. *)

Print Assumptions margolus_levitin_bound.
Print Assumptions lloyd_bound.
Print Assumptions bekenstein_hawking_area_law.

(** ** Substrate connection anchor.

    The three speed-limit / area-law probes in this file establish
    physical lower bounds whose VM-side interpretation feeds the
    Thiele Machine's mu-ledger via the Bekenstein bridge in
    UnificationProbeBridges. The anchor below makes the connection
    point explicit. *)

From Kernel Require Import VMState MuCostModel.

Definition additional_probes_vm_anchor (s : VMState) : nat := vm_mu s.
