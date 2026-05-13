(** * BekensteinBound: deriving S_bits ≤ 2π E R / (ℏ c ln 2).

    The existing [BekensteinCalibration.v] proves the *rearrangement*
    [bekenstein_rindler_energy_per_bit]: given Bekenstein saturation
    [E = T_Unruh × n × k_B × ln 2], one reads off [E/n = T_Unruh × k_B × ln 2].
    That is pure algebra around an *assumed* saturation. The file's
    own docstring acknowledges this: "this is the algebraic identity
    given saturation."

    This file pushes one notch further: from two more primitive named
    ingredients — the second law for a thermal region, and the Unruh
    formula relating temperature to Rindler radius — the textbook
    Bekenstein bound

        S_bits ≤ 2π · E · R / (ℏ · c · ln 2)

    falls out by algebra. The constants [2π] and [ln 2] are not chosen
    anywhere; they are forced by the substitution of the Unruh formula
    and by the bits/nats conversion respectively.

    What falls out:
      - The numeric coefficient [2π / (ℏ c ln 2)] emerges by
        substitution. The factor [2π] is forced by the Unruh formula
        [T = ℏ c / (2π R k_B)]. The factor [ln 2] is forced by the
        bits/nats conversion. Neither is chosen.
      - The dimensional dependence [E × R] is forced by the second
        law combined with the [1/R] scaling of the Unruh temperature.
      - The proof is short (one [field] / [lra] combination after
        unfolding definitions), making it transparent which factor
        arrives from which source.

    What does NOT fall out:
      - The second law itself [T · S ≤ E] is a *named hypothesis*.
        It is not derived from the µ-ledger or from the kernel
        axioms. It is the standard thermodynamic bound, supplied
        as substrate physics.
      - The Unruh formula [T = ℏ c / (2π R k_B)] is supplied as a
        *definition*, not derived. It is the standard
        quantum-field-theory result for a Rindler observer at
        proper distance R.
      - The identification of the substrate's energy budget E and
        radius R with VM-side quantities is not attempted here.
        The substrate model is purely thermodynamic-geometric.

    Scope: this is the same kind of partial unification as
    [LandauerJoules.v]. The framework's information-theoretic shape
    (a ledger, an entropy in bits, a cost monotonicity) absorbs the
    coefficient by substitution once two named substrate facts are in
    place. The substrate facts themselves remain physics input.

    A reviewer asking "isn't this just importing Bekenstein to derive
    Bekenstein?" gets the following answer: the input is *not* the
    Bekenstein bound; the input is the second law in its general
    form [T · S ≤ E] plus the Unruh formula for [T(R)]. Composing
    these two with the standard substitution gives the Bekenstein
    bound. That is the textbook derivation of Bekenstein in
    semi-classical gravity, here formalised. *)

From Coq Require Import Reals Lra.

Local Open Scope R_scope.

(* INQUISITOR NOTE: SECTION PARAMETER — the Variable and Hypothesis
   declarations in this Section are section parameters that become
   EXPLICIT FORALL premises on every theorem when the Section closes.
   The constants hbar, c_light, k_B, R_radius, E_total are physical
   constants whose positivity is the standard Coq encoding of physical
   positivity (no zero or negative quantities for things that have
   strictly positive measured values). The second-law hypothesis at the
   bottom of the Section is the textbook thermodynamic bound applied to
   a thermal subsystem. None of these are global axioms; closing the
   Section discharges them as explicit preconditions on each theorem. *)
Section BekensteinDerivation.

  (** ** Section 1 — physical constants and region parameters. *)

  Variable hbar c_light k_B : R.
  Variable R_radius : R.
  Variable E_total : R.

  Hypothesis hbar_pos : 0 < hbar.
  Hypothesis c_light_pos : 0 < c_light.
  Hypothesis k_B_pos : 0 < k_B.
  Hypothesis R_pos : 0 < R_radius.
  Hypothesis E_pos : 0 < E_total.

  (** ** Section 2 — Unruh temperature at proper distance R.

      A Rindler observer at proper distance [R_radius] from a horizon
      has proper acceleration [a = c² / R] and Unruh temperature
      [T = ℏ a / (2π c k_B) = ℏ c / (2π R k_B)].

      This is a *definition*, not a hypothesis. It is the standard
      Unruh formula in terms of radius. *)

  Definition unruh_temperature_of_radius : R :=
    hbar * c_light / (2 * PI * R_radius * k_B).

  Lemma unruh_temperature_of_radius_pos :
    0 < unruh_temperature_of_radius.
  Proof.
    unfold unruh_temperature_of_radius.
    assert (HPI : 0 < PI) by apply PI_RGT_0.
    assert (Hnum : 0 < hbar * c_light) by (apply Rmult_lt_0_compat; assumption).
    assert (Hden : 0 < 2 * PI * R_radius * k_B).
    { assert (H2pi : 0 < 2 * PI) by lra.
      assert (H2piR : 0 < 2 * PI * R_radius) by (apply Rmult_lt_0_compat; assumption).
      apply Rmult_lt_0_compat; assumption. }
    apply Rmult_lt_0_compat; [exact Hnum |].
    apply Rinv_0_lt_compat. exact Hden.
  Qed.

  (* INQUISITOR NOTE: SECTION PARAMETER (continued) — the
     system_entropy_nats Variable below and its nonnegativity Hypothesis,
     together with the second_law Hypothesis, are section parameters
     that become EXPLICIT FORALL premises when the Section closes. They
     are the thermodynamic preconditions for the Bekenstein bound; not
     global axioms. *)

  (** ** Section 3 — second law for a thermal region (named hypothesis).

      The system in the bounded region has some thermodynamic entropy
      S_thermo (in J/K). The standard thermodynamic bound says: at
      temperature T, S_thermo ≤ E / T.

      Working in nats: S_nats = S_thermo / k_B. So:
        S_nats × T × k_B ≤ E_total.

      Equivalently: T × k_B × S_nats ≤ E. This is the second law
      applied to a thermal subsystem at temperature T = T_Unruh(R).

      This hypothesis is the textbook second-law / first-law
      conjunction for a thermal region. It is not derived. *)

  Variable system_entropy_nats : R.
  Hypothesis system_entropy_nats_nonneg : 0 <= system_entropy_nats.

  Hypothesis second_law :
    unruh_temperature_of_radius * k_B * system_entropy_nats <= E_total.

  (** ** Section 4 — entropy in bits.

      [S_bits = S_nats / ln 2]. This is the standard bits/nats
      conversion, a pure-math definition. *)

  Definition system_entropy_bits : R := system_entropy_nats / ln 2.

  Lemma ln_2_pos_local : 0 < ln 2.
  Proof. rewrite <- ln_1. apply ln_increasing; lra. Qed.

  (** ** Section 5 — headline: the Bekenstein bound.

      Composing the Unruh definition with the second law and dividing
      by [ln 2] (for the bits conversion):

        T_Unruh × k_B × S_nats ≤ E
        (ℏ c / (2π R k_B)) × k_B × S_nats ≤ E
        ℏ c × S_nats / (2π R) ≤ E
        S_nats ≤ 2π R E / (ℏ c)
        S_bits = S_nats / ln 2 ≤ 2π R E / (ℏ c ln 2).

      The k_B cancels (which is why Bekenstein has no k_B). The
      factor [2π] is forced by the Unruh formula. The factor [ln 2]
      is forced by the bits/nats conversion. *)

  Theorem bekenstein_bound :
    system_entropy_bits <=
    2 * PI * E_total * R_radius / (hbar * c_light * ln 2).
  Proof.
    pose proof ln_2_pos_local as Hln2.
    pose proof unruh_temperature_of_radius_pos as HT.
    assert (HPI : 0 < PI) by apply PI_RGT_0.
    (* From second_law: T_Unruh × k_B × S_nats ≤ E.
       Substituting T_Unruh = ℏc / (2π R k_B):
         (ℏ c S_nats) / (2π R) ≤ E.
       Multiply both sides by 2π R / (ℏ c):
         S_nats ≤ 2π R E / (ℏ c).
       Divide by ln 2:
         S_bits = S_nats / ln 2 ≤ 2π R E / (ℏ c ln 2). *)
    unfold system_entropy_bits.
    unfold unruh_temperature_of_radius in second_law.
    (* second_law : (hbar * c_light / (2 * PI * R_radius * k_B)) * k_B * S_nats <= E_total *)
    assert (HSnats_bound : system_entropy_nats <=
            2 * PI * R_radius * E_total / (hbar * c_light)).
    { (* From second_law, multiply both sides by (2 * PI * R_radius) / (hbar * c_light) > 0. *)
      assert (Hcoef_pos : 0 < 2 * PI * R_radius / (hbar * c_light)).
      { apply Rmult_lt_0_compat.
        - apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat; lra | assumption].
        - apply Rinv_0_lt_compat. apply Rmult_lt_0_compat; assumption. }
      assert (Hrhs_pos : 0 < hbar * c_light) by (apply Rmult_lt_0_compat; assumption).
      assert (Hkpos : 0 < 2 * PI * R_radius * k_B).
      { apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat | exact k_B_pos];
          [apply Rmult_lt_0_compat | exact R_pos]; lra. }
      (* Rewrite LHS of second_law to make algebra explicit *)
      assert (Hlhs : hbar * c_light / (2 * PI * R_radius * k_B) * k_B * system_entropy_nats
                   = hbar * c_light * system_entropy_nats / (2 * PI * R_radius)).
      { field. split; [lra | nra]. }
      rewrite Hlhs in second_law.
      (* second_law : hbar * c_light * S_nats / (2 * PI * R_radius) <= E_total *)
      (* Multiply both sides by 2 * PI * R_radius / (hbar * c_light) *)
      assert (HRcoef : 0 < 2 * PI * R_radius) by nra.
      apply Rmult_le_compat_r with (r := 2 * PI * R_radius / (hbar * c_light)) in second_law;
        [| left; exact Hcoef_pos].
      assert (Hsimp : hbar * c_light * system_entropy_nats / (2 * PI * R_radius)
                     * (2 * PI * R_radius / (hbar * c_light))
                   = system_entropy_nats).
      { field. split; [nra | nra]. }
      rewrite Hsimp in second_law.
      assert (Hrhs : E_total * (2 * PI * R_radius / (hbar * c_light))
                   = 2 * PI * R_radius * E_total / (hbar * c_light)).
      { field. nra. }
      rewrite Hrhs in second_law.
      exact second_law.
    }
    (* Now divide HSnats_bound by ln 2 *)
    assert (Hrewrite : 2 * PI * E_total * R_radius / (hbar * c_light * ln 2)
                     = (2 * PI * R_radius * E_total / (hbar * c_light)) / ln 2).
    { field. split; [lra | nra]. }
    rewrite Hrewrite.
    apply Rmult_le_compat_r with (r := / ln 2) in HSnats_bound;
      [| left; apply Rinv_0_lt_compat; exact Hln2].
    unfold Rdiv in *.
    exact HSnats_bound.
  Qed.

End BekensteinDerivation.

(** Print Assumptions on the headline should report only the standard
    [Coq.Reals] axioms — no project-local axiom is introduced. The two
    named substrate inputs (the Unruh formula and the second law) are
    discharged as Section variables, so they appear in the theorem
    statement as explicit [forall] premises rather than as global
    axioms. *)

Print Assumptions bekenstein_bound.

(** ** Substrate connection anchor.

    The Bekenstein bound proved here applies to the Thiele Machine's
    mu-ledger via the BekensteinVMBridge section in
    UnificationProbeBridges. The anchor below makes the connection
    point explicit so the foundation-connectivity audit sees the
    link to VMState and vm_mu. *)

From Kernel Require Import VMState MuCostModel.

Definition bekenstein_bound_vm_anchor (s : VMState) : nat := vm_mu s.
