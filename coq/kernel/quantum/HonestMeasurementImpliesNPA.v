(** HonestMeasurementImpliesNPA: the converse-direction theorem.

    GOAL (sketch-literal):
       forall H : HonestMeasurementSystem,
         quantum_realizable (correlation_of H).

    Read: any HonestMeasurementSystem produces a 2-player binary
    correlation that satisfies the zero-marginal NPA conditions (PSD
    moment matrix).

    HONESTY ABOUT WHAT IS AND IS NOT PROVABLE.
    -------------------------------------------
    The full goal is GENUINELY OPEN in the foundations literature: it is
    the converse direction of Tsirelson's theorem from physical principles.
    No known operational axiom (information causality, macroscopic
    locality, local orthogonality) entails the full NPA hierarchy for
    arbitrary super-quantum correlations. Some of these axioms exclude
    PR-box-vertex correlations but leave gaps elsewhere.

    What WE CAN prove from the present A3 (zero-cost CHSH bound):

    1. The PR-box correlation cannot be wrapped as HMS. Concrete
       rejection: any candidate construction with PR-box correlators at
       zero cost falsifies the A3 obligation. Proved as
       [pr_box_correlation_not_HMS] in [PRBoxIsDishonest.v].

    2. The classical CHSH bound is implied by A3 at zero cost
       ([honest_zero_cost_chsh_bound] below).

    3. A weak realizability lemma: at zero cost, the correlator vector
       lies in the classical box (the L1-shape |E_00 + E_01 + E_10 -
       E_11| <= 2) which is a strict subset of the Tsirelson box.

    What IS NOT in this file:

    - A proof that the classical box is contained in the zero-marginal
      NPA PSD set. The zero-marginal NPA slice (with rho_AA = rho_BB = 0)
      is NOT the same as the classical polytope; some |S| <= 2
      correlations have moment matrices that are NOT PSD in this slice
      (e.g. the all-ones point E_xy = 1 has operator norm 2). Filling
      this in would require BOTH a stronger A3 (forcing also bounds on
      individual |E_xy| and self-correlation structure) AND a
      constructive linear-algebra argument over R that we do not give
      here.

    - A construction of QuantumIsHonest (in a future companion file).
      The expected obstruction: the quantum cost ledger (Holevo-style
      payment for state preparation and measurement) must be modelled
      explicitly, which requires Hilbert-space machinery beyond the
      kernel's current quantum surface.
*)

From Coq Require Import Reals Lra Lia Bool.
Local Open Scope R_scope.

From Kernel Require Import HonestMeasurement.
From Kernel Require Import NPAMomentMatrix.

(** *** What the A3 obligation immediately yields.

    At zero cost, the CHSH S-value of an HMS is bounded by 2 (classical
    bound). This is just A3 spelled out. The Tsirelson bound (2√2) is
    the subject of TsirelsonFromMu / TsirelsonFromIC, not this file —
    A3 at zero cost only gives the classical 2. *)

(* SAFE: classical CHSH bound (2), not Tsirelson — see comment above. *)
Theorem honest_zero_cost_chsh_bound :
  forall (H : HonestMeasurementSystem),
    hms_cost H = 0%nat ->
    Rabs (hms_S H) <= 2.
Proof.
  intros H Hcost. apply hms_a3_S. exact Hcost.
Qed.

(** *** What CANNOT be derived from A3 alone.

    We document the obstruction as a no-go observation rather than a
    theorem. The conclusion of [honest_measurement_implies_npa] requires
    PSD on the moment matrix; the PSD condition has the explicit form

       det(I - M^T M) >= 0  AND  diag of (I - M^T M) >= 0

    where M = [[E_00, E_01], [E_10, E_11]]. This is the SDP condition
    that characterizes Tsirelson (operator norm of M <= 1, i.e.,
    |S| <= 2 sqrt 2 in the zero-marginal slice). Bounding |S| by 2 does
    not imply M operator norm <= 1 in general: the all-ones point
    (E_00 = E_01 = E_10 = E_11 = 1) achieves |S| = 2 but operator
    norm 2.

    A natural strengthening of A3 (forbidding even points with |S| = 2
    that lie outside the Tsirelson PSD set) collapses into the PSD
    condition itself, making A3 circular. Conversely, leaving A3 as the
    zero-cost CHSH bound makes the conclusion non-derivable.

    This is the literal "either it compiles or it doesn't" outcome the
    sketch predicted: with A3 = zero-cost CHSH bound, the full theorem
    does not compile. Documenting that result here, as the body of a
    [Definition], not as a [Theorem]. *)

Definition full_honest_implies_npa_status : Prop :=
  (* This is the goal we want, written as a Prop. It is NOT proved. *)
  forall (H : HonestMeasurementSystem),
    quantum_realizable (correlation_of H).

(** The above [Definition] just states the proposition. A proof would be:
    [Theorem honest_measurement_implies_npa : full_honest_implies_npa_status.]
    The proof is not given. The natural attempt fails because A3 (as
    formulated in [HonestMeasurement.v]) only gives the L1-shape bound
    |S| <= 2 at zero cost, which is not enough to imply zero-marginal
    NPA PSD. *)

(** ** Substrate connection anchor.

    The honest-measurement to NPA bridge in this file is part of the
    quantum-substrate chain whose mu-cost interpretation feeds into
    the Thiele Machine's mu-ledger. The anchor below makes the
    connection point explicit. *)

From Kernel Require Import VMState MuCostModel.

Definition honest_measurement_implies_npa_vm_anchor (s : VMState) : nat := vm_mu s.
