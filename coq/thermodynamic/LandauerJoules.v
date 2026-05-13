(** * LandauerJoules: closing the bits-to-joules gap in Landauer's principle.

    The two existing Landauer files in this directory
    ([LandauerDerived.v], [ThermodynamicBridge.v]) prove Landauer "in
    Landauer units" — that is, in units where the conversion factor
    [k_B * T * ln 2] is set to 1. Both files explicitly state that the
    bits-to-joules conversion is not derived; in [LandauerDerived.v] the
    comment reads:

      "What this file does NOT derive: the physical conversion factor
       k_B · T · ln 2 between bits and joules. That conversion is the
       external bridge between Shannon entropy and Boltzmann entropy."

    This file closes that gap, with the following honesty discipline:

      The constant [k_B * T * ln 2] does NOT appear as a single literal
      anywhere in any hypothesis. Each of its three factors is introduced
      separately, from a distinct named source:

        ln 2 : the Shannon entropy of a uniform distribution over [2^n]
               outcomes is [n * ln 2] nats. This is a pure-mathematics
               identity ([shannon_entropy_binary_uniform_nats] below) —
               no axiom is introduced. It comes from
               [ln (INR (2^n)) = INR n * ln 2], i.e. log of a power.

        k_B  : the substrate's thermodynamic entropy in J/K is related to
               its information entropy in nats by [S_thermo = k_B * S_info].
               This is Boltzmann's identification. It is introduced as
               the single named hypothesis [boltzmann_bridge].

        T    : for a process that decreases the system's thermodynamic
               entropy by [dS] while in thermal contact with a bath at
               temperature T, the bath absorbs at least [T * dS] of heat.
               This is the Clausius form of the second law for a thermal
               bath. It is introduced as the second named hypothesis
               [second_law_thermal_bath].

    The headline [landauer_joules] then composes these three sources
    into [Q >= k_B * T * ln 2 * n]. The combined coefficient is not
    chosen anywhere — it emerges as the product of the three factors.

    What falls out:
      - The factor [ln 2] is *forced* by the binary structure of bit
        erasure. It is derived from [ln (2^n) = n * ln 2], not chosen.
      - The factor [T] is the bath parameter; the second law makes
        its appearance compulsory by composing with system entropy.
      - The product [k_B * T * ln 2 * n] emerges by composition.

    What does NOT fall out:
      - The constant [k_B] itself. It enters through Boltzmann's
        formula [S = k_B * ln Omega] as the unit-conversion factor
        between microstate counting (information-theoretic) and
        thermodynamic entropy (J/K). Boltzmann's formula is not
        derivable from the VM cost ledger.
      - That the substrate is in thermal contact with a bath. This is
        a substrate property, supplied as a hypothesis.

    The remaining gap requires Boltzmann's formula from more primitive
    substrate axioms (counting + ergodicity). That is a project in
    statistical mechanics, out of scope here.

    Structurally:
      - The constant [k_B * T * ln 2] does not appear as a single
        chosen literal anywhere. It is built up factor-by-factor.
      - The factor [ln 2] is derived rather than chosen.
      - The two non-VM facts (Boltzmann's formula and the second law)
        are named, isolated, and visible to [Print Assumptions]. *)

From Coq Require Import Reals Lra Lia Arith.
From Thermodynamic Require Import LandauerDerived.

Local Open Scope R_scope.

(* INQUISITOR NOTE: SECTION PARAMETER — Variable and Hypothesis
   declarations across this Section are section parameters that become
   EXPLICIT FORALL premises on every theorem when the Section closes.
   T_pos and k_B_pos are physical positivity for thermodynamic
   temperature and Boltzmann's constant. The boltzmann_bridge and
   second_law_thermal_bath hypotheses appearing later in the Section
   are textbook physics inputs (Boltzmann's identification,
   second-law for a thermal bath). None are global axioms; closing
   the Section discharges them as explicit theorem premises. *)
Section LandauerJoulesDerivation.

  (** ** Substrate parameters. *)

  Variable T : R.
  Variable k_B : R.
  Hypothesis T_pos : 0 < T.
  Hypothesis k_B_pos : 0 < k_B.

  (** ** Section 1 — bits to nats, pure mathematics.

      Shannon entropy of a uniform distribution over [Omega] outcomes is
      [ln Omega] nats. For a binary state space of size [2^n] this equals
      [n * ln 2]. The [ln 2] factor comes from [ln (2^n) = n * ln 2], a
      mathematical identity — no axiom is involved. *)

  Definition shannon_entropy_nats (omega : nat) : R := ln (INR omega).

  (** [ln] of a real power: derived by straightforward induction from
      [ln_1] and [ln_mult]. *)
  Lemma ln_pow_nat : forall (x : R) (n : nat),
    0 < x -> ln (x ^ n) = INR n * ln x.
  Proof.
    intros x n Hx. induction n as [|n IH].
    - simpl. rewrite ln_1. lra.
    - simpl. rewrite ln_mult; [| exact Hx | apply pow_lt; exact Hx].
      rewrite IH.
      destruct n as [|n']; simpl; lra.
  Qed.

  (** Headline math lemma: the Shannon entropy of a uniform binary state
      space of [n] bits equals [n * ln 2] nats. Derived from [pow_INR]
      and [ln_pow_nat], not stipulated. *)
  Lemma shannon_entropy_binary_uniform_nats :
    forall n : nat,
      shannon_entropy_nats (2 ^ n) = INR n * ln 2.
  Proof.
    intro n. unfold shannon_entropy_nats.
    rewrite pow_INR.
    rewrite ln_pow_nat.
    - replace (INR 2) with 2 by (simpl; ring). reflexivity.
    - replace (INR 2) with 2 by (simpl; ring). lra.
  Qed.

  (** Positivity of [ln 2]: follows from [ln 1 = 0] and monotonicity. *)
  Lemma ln_2_pos : 0 < ln 2.
  Proof. rewrite <- ln_1. apply ln_increasing; lra. Qed.

  (** ** Section 2 — information entropy for an erasure (a definition).

      For an erasure of [n] bits, the system's Shannon information
      entropy decrease in nats is, by definition, the entropy of a
      uniform distribution over [2^n] outcomes — i.e. [ln (2^n)] nats.
      This is a *definition* (the uniform-prior Shannon entropy
      decrease), not a substrate hypothesis. *)

  Definition info_entropy_decrease_nats (pe : PhysicalErasure) : R :=
    shannon_entropy_nats (2 ^ bits_erased (erasure_op pe)).

  Lemma info_entropy_decrease_value :
    forall pe : PhysicalErasure,
      info_entropy_decrease_nats pe =
      INR (bits_erased (erasure_op pe)) * ln 2.
  Proof.
    intro pe. unfold info_entropy_decrease_nats.
    apply shannon_entropy_binary_uniform_nats.
  Qed.

  (** ** Section 3 — Boltzmann bridge (named hypothesis).

      The substrate's thermodynamic entropy decrease in J/K equals
      [k_B] times its Shannon information entropy decrease in nats.

      This hypothesis contains no [ln 2] and no bit count. It is the
      Boltzmann identification in its bare form: thermodynamic entropy
      equals Boltzmann's constant times information entropy (in nats).
      The [ln 2] factor that ultimately appears in [landauer_joules]
      does NOT enter through this hypothesis — it enters through
      [info_entropy_decrease_value], which is pure mathematics. *)

  (* INQUISITOR NOTE: SECTION PARAMETER (continued) — the Variable
     system_thermo_entropy_decrease and the boltzmann_bridge Hypothesis
     are section parameters that become EXPLICIT FORALL premises on
     each theorem when the Section closes. boltzmann_bridge is the
     textbook Boltzmann identification of thermodynamic entropy with
     Shannon information entropy (in nats), times k_B. Not a global
     axiom. *)
  Variable system_thermo_entropy_decrease : PhysicalErasure -> R.

  Hypothesis boltzmann_bridge :
    forall pe : PhysicalErasure,
      system_thermo_entropy_decrease pe =
      k_B * info_entropy_decrease_nats pe.

  (** ** Section 4 — Second law for a thermal bath (named hypothesis).

      For a process that decreases the system's thermodynamic entropy
      by [dS] while in thermal contact with a bath at [T], the bath
      absorbs at least [T * dS] of heat. This is Clausius's statement of
      the second law applied to a bath of fixed temperature.

      This hypothesis contains no [k_B] and no [ln 2] — just [T]. *)

  (* INQUISITOR NOTE: SECTION PARAMETER (continued) — heat_to_bath
     Variable and second_law_thermal_bath Hypothesis are section
     parameters that become EXPLICIT FORALL premises on every theorem
     when the Section closes. The hypothesis is Clausius's statement
     of the second law applied to a bath at fixed temperature. Not a
     global axiom. *)
  Variable heat_to_bath : PhysicalErasure -> R.

  Hypothesis second_law_thermal_bath :
    forall pe : PhysicalErasure,
      0 <= system_thermo_entropy_decrease pe ->
      T * system_thermo_entropy_decrease pe <= heat_to_bath pe.

  (** ** Section 5 — Headline.

      Composing the three sources, the heat released to the bath by any
      erasure of [n] bits is at least [k_B * T * ln 2 * n]. The constant
      [k_B * T * ln 2] is not chosen anywhere — it is the algebraic
      product of three factors that each arrive separately:
        [k_B]  from [boltzmann_bridge]      (no ln 2 in its statement),
        [T]    from [second_law_thermal_bath] (no k_B in its statement),
        [ln 2] from [info_entropy_decrease_value] (a pure-math lemma,
               no hypothesis attached). *)

  Theorem landauer_joules :
    forall pe : PhysicalErasure,
      k_B * T * INR (bits_erased (erasure_op pe)) * ln 2 <= heat_to_bath pe.
  Proof.
    intro pe.
    pose proof ln_2_pos as Hln2.
    assert (Hbits_nn : 0 <= INR (bits_erased (erasure_op pe))) by apply pos_INR.
    assert (HdS_nn : 0 <= system_thermo_entropy_decrease pe).
    { rewrite boltzmann_bridge.
      rewrite info_entropy_decrease_value.
      apply Rmult_le_pos.
      - lra.
      - apply Rmult_le_pos; [exact Hbits_nn | lra]. }
    pose proof (second_law_thermal_bath pe HdS_nn) as Hlaw.
    rewrite boltzmann_bridge in Hlaw.
    rewrite info_entropy_decrease_value in Hlaw.
    apply Rle_trans with (T * (k_B * (INR (bits_erased (erasure_op pe)) * ln 2)));
      [apply Req_le; ring | exact Hlaw].
  Qed.

  (** ** Section 5 — Specialisation to one-bit erasure.

      The single-bit case: [Q >= k_B * T * ln 2]. This is the textbook
      Landauer bound. Note that the right-hand side here has each factor
      coming from a separately-cited source, not assembled as a single
      chosen constant. *)

  Corollary landauer_joules_one_bit :
    k_B * T * ln 2 <= heat_to_bath physical_one_bit_reset.
  Proof.
    pose proof (landauer_joules physical_one_bit_reset) as H.
    assert (Hb : INR (bits_erased (erasure_op physical_one_bit_reset)) = 1)
      by (simpl; reflexivity).
    rewrite Hb in H.
    apply Rle_trans with (k_B * T * 1 * ln 2);
      [apply Req_le; ring | exact H].
  Qed.

  (** ** Section 6 — Consistency with the information-side bound.

      The existing [landauer_information_bound] gives
      [env_entropy_increase pe >= bits_erased (erasure_op pe)] in
      information units (bits). Multiplying both sides by the
      [k_B * T * ln 2] coefficient that emerged from sections 1–4 above
      gives the joule-level inequality consistent with [landauer_joules].

      This corollary is a sanity check rather than a new theorem; its
      purpose is to make the relation between the two bounds visible. *)

  Corollary information_bound_in_joule_units :
    forall pe : PhysicalErasure,
      k_B * T * ln 2 * INR (bits_erased (erasure_op pe)) <=
      k_B * T * ln 2 * INR (env_entropy_increase pe).
  Proof.
    intro pe.
    pose proof (landauer_information_bound pe) as Hinfo.
    apply Rmult_le_compat_l.
    - pose proof ln_2_pos as Hln2.
      apply Rmult_le_pos; [apply Rmult_le_pos; lra | lra].
    - apply le_INR. exact Hinfo.
  Qed.

End LandauerJoulesDerivation.

(** ** Assumption checks.

    The three theorems below should report exactly the two named
    substrate hypotheses ([boltzmann_bridge] and
    [second_law_thermal_bath]) as their only non-trivial dependencies,
    plus the positivity hypotheses on [T] and [k_B]. Everything else
    (including the [ln 2] factor) is closed under the global context. *)

Print Assumptions landauer_joules.
Print Assumptions landauer_joules_one_bit.
Print Assumptions shannon_entropy_binary_uniform_nats.
