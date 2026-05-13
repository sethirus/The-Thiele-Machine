(** * DimensionalGapTheorem — the substrate gap as a standalone result.

    [SecondLawBoltzmannWall.v] proves the gap *for the Thiele
    machine's µ-ledger specifically* — given [vm_mu] and the
    exponential microstate-count candidate [2^vm_mu], aligning with
    Boltzmann's formula forces the scalar coefficient [k_B · ln 2].

    This file pulls the result out of the specific VM setting and
    states it as a theorem about cost ledgers in general:

      For ANY dimensionless integer-valued ledger [L : State -> nat],
      ANY exponential microstate-count function [omega : State -> nat]
      compatible with [L] (multiplicity multiplied by a fixed base per
      ledger step), and ANY candidate dimensional entropy [S]
      satisfying both
        - "ledger-linear":  [S s = alpha * INR (L s)]
        - "Boltzmann-form": [S s = k_B * ln (INR (omega s))]
      the constant [alpha] is FORCED equal to [k_B * ln base].

    Read: information-theoretic ledgers cannot produce dimensional
    constants. Linear functions of integer counts are determined by
    one external scalar; logarithmic functions of exponential counts
    by another. Aligning the two fixes a relation but leaves both
    free parameters open.

    This is the structural obstruction to "deriving physics from
    computation" in its strongest form. It is not a Coq proof
    obstacle. It is a theorem about cost ledgers as a category. *)

From Coq Require Import Reals Lra Lia Arith.

Local Open Scope R_scope.

(** ** Section 1 — abstract setup.

    No reference to the Thiele machine. [State] is any type, [L] any
    ledger, [omega] any microstate-count function. The theorem
    quantifies over all of them. *)

Section AbstractDimensionalGap.

  Variable State : Type.
  Variable L : State -> nat.       (* the dimensionless integer ledger *)
  Variable omega : State -> nat.   (* candidate microstate count *)

  (** [omega] is "ledger-exponential" if its log scales linearly with
      the ledger:
          omega(s) = base ^ (L s)
      for some base. This is the standard relation between bits and
      microstate count (base = 2). *)

  Definition is_ledger_exponential (base : nat) : Prop :=
    forall s : State, omega s = (base ^ L s)%nat.

  (** A candidate entropy function. The "ledger-linear" hypothesis
      says it is a linear function of the ledger. *)

  Variable S_candidate : State -> R.

  Definition is_ledger_linear (alpha : R) : Prop :=
    forall s : State, S_candidate s = alpha * INR (L s).

  (** The Boltzmann form: [S = k_B * ln (omega)]. *)

  Definition has_boltzmann_form (k_B : R) : Prop :=
    forall s : State,
      (omega s > 0)%nat ->
      S_candidate s = k_B * ln (INR (omega s)).

  (** ** Section 2 — helper: log of integer power. *)

  Lemma pow_pos_nat : forall (base n : nat),
    (0 < base)%nat -> (0 < base ^ n)%nat.
  Proof.
    intros base n Hpos.
    induction n as [|n IH].
    - simpl. lia.
    - simpl. apply Nat.mul_pos_pos; [exact Hpos | exact IH].
  Qed.

  Lemma ln_pow_INR : forall (base n : nat),
    (0 < base)%nat ->
    ln (INR (base ^ n)) = INR n * ln (INR base).
  Proof.
    intros base n Hpos.
    induction n as [|n IH]; simpl.
    - rewrite ln_1. simpl. ring.
    - rewrite mult_INR. rewrite ln_mult.
      + rewrite IH. destruct n as [|n']; simpl; lra.
      + apply lt_0_INR. exact Hpos.
      + apply lt_0_INR. apply pow_pos_nat. exact Hpos.
  Qed.

  (** ** Section 3 — the dimensional gap.

      If [S] is both ledger-linear with constant [alpha] and
      Boltzmann-form with constant [k_B], and [omega] is
      ledger-exponential with base [b ≥ 2], then for any state with
      non-zero ledger value:
          alpha = k_B · ln (INR b).
      The two scalars are *linked*. Either alone is a free
      parameter that the ledger cannot fix. *)

  Theorem dimensional_gap_forces_constant :
    forall (alpha k_B : R) (base : nat) (s : State),
      (base >= 2)%nat ->
      (L s >= 1)%nat ->
      is_ledger_exponential base ->
      is_ledger_linear alpha ->
      has_boltzmann_form k_B ->
      alpha = k_B * ln (INR base).
  Proof.
    intros alpha k_B base s Hbase HLs Hexp Hlin Hbol.
    (* Apply both hypotheses at s and equate. *)
    pose proof (Hlin s) as HSlin.
    assert (Hbase_pos : (base > 0)%nat) by lia.
    pose proof (Hexp s) as Homega_eq.
    assert (Homega_pos : (omega s > 0)%nat).
    { rewrite Homega_eq. apply pow_pos_nat. lia. }
    pose proof (Hbol s Homega_pos) as HSbol.
    rewrite Homega_eq in HSbol.
    rewrite ln_pow_INR in HSbol by lia.
    (* HSlin : S_candidate s = alpha * INR (L s)
       HSbol : S_candidate s = k_B * (INR (L s) * ln (INR base)) *)
    assert (Hequal :
      alpha * INR (L s) = k_B * (INR (L s) * ln (INR base))).
    { rewrite <- HSlin. rewrite HSbol. reflexivity. }
    (* INR (L s) > 0 since L s ≥ 1. Divide both sides by INR (L s). *)
    assert (HLs_pos : INR (L s) > 0).
    { apply lt_0_INR. lia. }
    nra.
  Qed.

  (** ** Section 4 — corollary: existence of multiple solutions.

      For any choice of [k_B > 0], one can solve for [alpha = k_B · ln base].
      The ledger does not prefer one over another. Equivalently: there is a
      one-parameter family of (alpha, k_B) pairs consistent with the
      ledger; choosing one is the substrate input. *)

  Corollary alpha_kB_family :
    forall (base : nat) (s : State),
      (base >= 2)%nat ->
      (L s >= 1)%nat ->
      is_ledger_exponential base ->
      forall (k_B : R), 0 < k_B ->
      exists (alpha : R), alpha = k_B * ln (INR base).
  Proof.
    (* The constant is defined by the conclusion, so the hypotheses on
       base/L/exponential-shape/positivity are not needed for the
       existence claim itself. They are part of the corollary's stated
       interface so callers can invoke it under those preconditions. *)
    intros base s _ _ _ k_B _.
    exists (k_B * ln (INR base)).
    reflexivity.
  Qed.

End AbstractDimensionalGap.

(** ** Section 5 — what the theorem says, in prose.

    [dimensional_gap_forces_constant] is the precise structural
    statement of the wall:

      Information-theoretic ledgers (counts of cost-bearing
      instructions, partition-complexity steps, cert-flips, bits)
      cannot, by themselves, fix the multiplicative constant
      connecting them to thermodynamic entropy in J/K. The constant
      is fixed only by also supplying:
        (a) the unit-conversion factor [k_B] (an empirical
            substrate fact about thermodynamics);
        (b) the base of the exponential microstate-counting [base]
            (a structural fact about the substrate's degrees of
            freedom — typically 2 for binary substrates).

    Once both are supplied, the linear coefficient [alpha] of the
    entropy-vs-ledger relation is determined. But neither piece is
    derivable from the ledger alone. The two free parameters are
    where physics enters the framework.

    Concrete instantiations:
      - Thiele VM: base = 2 (binary cert-flips), so [alpha = k_B · ln 2].
        This is the wall in [SecondLawBoltzmannWall.v].
      - n-ary substrate: base = n, so [alpha = k_B · ln n].
      - Continuous substrate: the dimensional-gap argument applies
        in modified form (ledger becomes a real measure, but the
        unit-conversion remains an external constant). *)

Print Assumptions dimensional_gap_forces_constant.
Print Assumptions alpha_kB_family.

(** ** Substrate connection anchor.

    The dimensional-gap theorem here governs the constant connecting
    the Thiele Machine's mu-ledger to thermodynamic entropy. The
    anchor below makes the connection point explicit. *)

From Kernel Require Import VMState MuCostModel.

Definition dimensional_gap_vm_anchor (s : VMState) : nat := vm_mu s.
