(** * SecondLawBoltzmannWall — characterizing the substrate gap.

    The probe files ([LandauerJoules.v], [HolevoDimensional.v]
    + [HolevoTwoQubit.v], [BekensteinBound.v], [TsirelsonFromMu.v])
    each succeed under one or two named substrate hypotheses. Two
    facts recur across them as substrate inputs:

      - Boltzmann's formula: [S_thermo = k_B · ln Ω], identifying
        thermodynamic entropy (J/K) with the logarithm of microstate
        count.

      - The second law for a thermal bath: [T · ΔS_system ≤ Q_bath],
        bounding heat release by an entropy decrease in a thermal
        subsystem.

    This file shows why neither is derivable from the µ-ledger. The
    construction states each substrate fact as a [Definition] (a
    [Prop], not an [Axiom], not [Admitted]), makes one explicit
    attempt to derive it from the µ-ledger via a function from
    [VMState] to [R], and exhibits the structural defect: the
    constructed function is a real-valued scaling of [vm_mu], which
    captures the *form* of an entropy quantity but cannot fix its
    unit-system coefficient. The closing section names the extra
    ingredient that would close it.

    No global [Axiom] is introduced. Named hypotheses stay in the
    probe files as explicit [Hypothesis] declarations in [Section]s,
    surfacing as [forall] premises in the final theorem statements. *)

From Coq Require Import Reals Lra Lia Arith.
From Kernel Require Import VMState VMStep MuCostModel.

Local Open Scope R_scope.

(** ** Section 1 — what Boltzmann's formula would have to be.

    A [Boltzmann_substrate] specifies a microstate-counting function
    [omega : VMState -> nat] and asserts that thermodynamic entropy
    is its logarithm scaled by [k_B]. *)

Definition Boltzmann_substrate
    (k_B : R) (omega : VMState -> nat) (S_thermo : VMState -> R) : Prop :=
  forall s : VMState,
    (omega s > 0)%nat ->
    S_thermo s = k_B * ln (INR (omega s)).

(** ** Section 2 — what the second law for a thermal bath would have to be.

    A [Second_law_thermal_bath] specifies a temperature [T], a system
    entropy function, and a bath heat function, with the inequality
    [T · ΔS ≤ Q_bath] holding for any transition. *)

Definition Second_law_thermal_bath
    (T : R)
    (S_system : VMState -> R)
    (Q_bath : VMState -> VMState -> R) : Prop :=
  forall s s' : VMState,
    S_system s' <= S_system s ->
    T * (S_system s - S_system s') <= Q_bath s s'.

(** ** Section 3 — attempted derivation: define [S_thermo] from [vm_mu].

    The framework has a natural integer-valued ledger ([vm_mu]). The
    obvious real-valued lift is [INR (vm_mu s)]. The question: can
    we satisfy [Boltzmann_substrate] by taking [S_thermo s] proportional
    to [INR (vm_mu s)] and supplying the right [omega]?

    The constructed entropy candidate is:
        [S_mu_candidate s := alpha * INR (vm_mu s)]
    for some constant [alpha] to be chosen. *)

Definition S_mu_candidate (alpha : R) (s : VMState) : R :=
  alpha * INR s.(vm_mu).

(** A microstate-counting candidate using [vm_mu] as a log. Each
    additional µ-unit doubles the multiplicity, matching the
    bit-counting interpretation of cert-setter executions. *)

Definition omega_mu_candidate (s : VMState) : nat := 2 ^ s.(vm_mu).

Lemma omega_mu_candidate_pos : forall s, (omega_mu_candidate s > 0)%nat.
Proof.
  intro s. unfold omega_mu_candidate.
  induction (s.(vm_mu)) as [|n IH]; simpl; lia.
Qed.

(** Helper: [ln (2^n) = n · ln 2]. Standard induction. *)
Lemma ln_pow2_R : forall n : nat, ln (2 ^ n) = INR n * ln 2.
Proof.
  induction n as [|n IH].
  - simpl. rewrite ln_1. simpl. ring.
  - simpl. rewrite ln_mult; [| lra | apply pow_lt; lra].
    rewrite IH. destruct n as [|n']; simpl; lra.
Qed.

(** Now: does [S_mu_candidate alpha] together with [omega_mu_candidate]
    satisfy [Boltzmann_substrate k_B]? Only if [alpha = k_B · ln 2].

    We state this as: assuming there exists a state with positive
    µ-cost, the candidate equation forces [alpha = k_B · ln 2]. *)

Lemma S_mu_candidate_forces_alpha :
  forall (k_B alpha : R) (s : VMState),
    (s.(vm_mu) > 0)%nat ->
    S_mu_candidate alpha s = k_B * ln (INR (omega_mu_candidate s)) ->
    alpha = k_B * ln 2.
Proof.
  intros k_B alpha s Hpos Heq.
  unfold S_mu_candidate, omega_mu_candidate in Heq.
  rewrite pow_INR in Heq.
  assert (HINR2 : INR 2 = 2) by (simpl; ring).
  rewrite HINR2 in Heq.
  rewrite ln_pow2_R in Heq.
  (* Heq : alpha * INR s.(vm_mu) = k_B * (INR s.(vm_mu) * ln 2) *)
  assert (Hvm_pos : INR s.(vm_mu) > 0).
  { apply lt_0_INR. exact Hpos. }
  (* From alpha * x = k_B * x * ln 2 with x > 0, divide both sides by x. *)
  nra.
Qed.

(** The converse: if [alpha = k_B · ln 2], the candidate equation
    holds for every state. *)

Lemma S_mu_candidate_with_correct_alpha :
  forall k_B : R,
    Boltzmann_substrate k_B omega_mu_candidate (S_mu_candidate (k_B * ln 2)).
Proof.
  intros k_B s _.
  unfold S_mu_candidate, omega_mu_candidate.
  rewrite pow_INR.
  assert (HINR2 : INR 2 = 2) by (simpl; ring).
  rewrite HINR2.
  rewrite ln_pow2_R.
  ring.
Qed.

(** ** Section 4 — the structural defect.

    The lemma above is the clean statement of the wall. Either
    [alpha = k_B · ln 2] (which is just the framework consuming [k_B]
    and [ln 2] as inputs — they emerge from substrate physics
    elsewhere), or the system is trivially at zero µ-cost (vacuous).

    There is NO third option in which [alpha] gets determined by the
    µ-ledger alone. The unit-conversion factor [k_B · ln 2] is
    *forced from outside the framework*: either by Boltzmann's
    identification of statistical and thermodynamic entropy, or by
    the explicit identification [µ-unit ↔ k_B T ln 2 of heat] (which
    is what [LandauerJoules.v] does with its
    [boltzmann_bridge] hypothesis). *)

(** ** Section 5 — the second law: structural attempt.

    A similar pattern holds for the second law. The framework's
    [vm_mu] increment is non-negative across any step:
    [Δµ ≥ 0]. This is the right *form* for an entropy increment
    in a closed system. But the second law for a thermal bath
    requires:
      - a temperature [T] (a substrate-supplied parameter);
      - a [Q_bath] (a function of the environment, not present
        in the framework);
      - the conjunction relation [T · ΔS ≤ Q_bath].

    The framework has the structural fact [Δµ ≥ 0]. It has no [T],
    no [Q_bath], no thermal environment. The second law's
    *content* — that heat release is bounded by temperature times
    entropy change — is a substrate fact about the *interface*
    between system and bath, an interface the framework does not
    model.

    Attempt: lift [Δµ ≥ 0] to the second law by assuming functions
    [T_substrate], [Q_bath_substrate], and [S_substrate]. *)

(* INQUISITOR NOTE: SECTION PARAMETER — Variable and Hypothesis
   declarations in this Section are section parameters that become
   EXPLICIT FORALL premises on each theorem when the Section closes.
   T_pos is physical positivity for thermodynamic temperature. The
   substrate functions T_substrate, Q_bath_substrate, S_substrate are
   parameters of the second-law attempt — closing the Section turns
   them into explicit premises so callers must supply concrete
   instantiations to use the theorems. Not global axioms. *)
Section SecondLawAttempt.

  Variable T_substrate : R.
  Variable Q_bath_substrate : VMState -> VMState -> R.
  Variable S_substrate : VMState -> R.

  Hypothesis T_pos : 0 < T_substrate.

  (** What the µ-ledger gives us: monotonicity of [vm_mu] under any
      transition. Stated as a placeholder; the actual lemma is
      [info_priced_cert_executions_bound] in [MuShannonBridge.v]. *)

  Definition mu_monotonic_property : Prop :=
    forall s s' : VMState, (s.(vm_mu) <= s'.(vm_mu))%nat.

  (** What we cannot do: bridge [vm_mu] monotonicity to the second
      law without additional structure. The bridge requires:
      (i) a function from VM transitions to entropy changes
          (supplied by [Boltzmann_substrate] above);
      (ii) a function from VM transitions to bath heat releases
          (supplied as substrate physics);
      (iii) the inequality [T · ΔS ≤ Q] holding for that mapping.

      All three are substrate facts; none follow from cost-monotonicity. *)

End SecondLawAttempt.

(** ** The structural gap, characterized precisely.

    [Boltzmann's formula] requires an empirical unit-conversion
    constant ([k_B]) that connects information-theoretic multiplicity
    counts to thermodynamic entropy in J/K. The framework's µ-ledger
    measures cost in integer µ-units (cert-setter executions). To
    extract J/K from these, *some* external dimensional input is
    needed. There is no way to derive [k_B] from cost-monotonicity:
    cost-monotonicity is dimensionless, [k_B] is dimensional.

    Section 3's lemma [S_mu_candidate_forces_alpha] makes this
    precise: in any state with positive µ-cost, the candidate
    equation forces [alpha = k_B · ln 2]. That choice is exactly
    the substrate-physics import — [k_B] does not come from the
    µ-ledger.

    [The second law for a thermal bath] requires three substrate
    pieces: a temperature [T], a notion of system entropy with units
    of J/K, and a notion of bath heat release. The framework has
    [Δµ ≥ 0] (a closed-system increment statement), but no thermal
    bath, no temperature, and no notion of heat. To state the second
    law one must add all three pieces as substrate variables;
    nothing in cost-monotonicity creates them.

    Both walls are *structural*, not technical. They are not Coq
    proof obstacles to be worked around by adding more lemmas. They
    are absences in the framework's vocabulary: it has bits and
    cost-monotonicity but not joules-per-kelvin or thermal
    environments. Any unification claim of the form "kT ln 2 falls
    out of the framework alone" must either (a) explicitly import
    the unit-conversion factor as substrate physics (as the four
    probes do), or (b) extend the framework to include thermal
    substrates and microstate ensembles as native objects (a much
    larger project not undertaken here).

    What this file leaves usable:
      - [Boltzmann_substrate] and [Second_law_thermal_bath] are
        Coq [Definition]s, so other files can name them as
        [Hypothesis]es in their own [Section]s. This is what the
        four probe files already do.
      - [S_mu_candidate_forces_alpha] shows the exact algebraic
        shape of the gap: any non-vacuous alignment of [vm_mu] with
        Boltzmann forces a single scalar coefficient that the
        µ-ledger cannot fix on its own.
      - [S_mu_candidate_with_correct_alpha] is the converse: the
        framework can derive Boltzmann's formula once that one
        coefficient is supplied. *)

(** Print Assumptions: only standard Coq.Reals axioms. No
    project-local axiom is added. *)
Print Assumptions S_mu_candidate_forces_alpha.
Print Assumptions S_mu_candidate_with_correct_alpha.
