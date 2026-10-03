(** HonestMeasurementImpliesNPA: the converse-direction theorem.

    GOAL:
       forall H : HonestMeasurementSystem,
         npa_psd (correlation_of H).

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

    What IS provable from the present A3 (zero-cost CHSH bound):

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
      constructive linear-algebra argument over R that this file does not
      give.

    - A construction showing that quantum measurement satisfies the honest
      measurement axioms. Such a construction needs the quantum cost ledger
      (Holevo-style payment for state preparation and measurement) modelled
      explicitly, which requires Hilbert-space machinery the kernel does
      not contain.
*)

From Coq Require Import Reals Lra Lia Bool.
Local Open Scope R_scope.

From Kernel Require Import HonestMeasurement.
From Kernel Require Import NPAMomentMatrix.

(** *** What the A3 obligation immediately yields.

    At zero cost, the CHSH S-value of an HMS is bounded by 2 (classical
    bound). This is just A3 spelled out. The Tsirelson bound (2√2) is
    the subject of TsirelsonFromMu / TsirelsonFromIC, not this file;
    A3 at zero cost only gives the classical 2. *)

(* SAFE: classical CHSH bound (2), not Tsirelson; see comment above. *)
Theorem honest_zero_cost_chsh_bound :
  forall (H : HonestMeasurementSystem),
    hms_cost H = 0%nat ->
    Rabs (hms_S H) <= 2.
Proof.
  intros H Hcost. apply hms_a3_S. exact Hcost.
Qed.

(** *** What CANNOT be derived from A3 alone.

    The obstruction is a no-go observation rather than a theorem. The
    conclusion of [full_honest_implies_npa_status] requires
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

    With A3 = zero-cost CHSH bound, the full theorem has no proof here.
    The proposition is recorded as the body of a [Definition], not as a
    [Theorem]. *)

Definition full_honest_implies_npa_status : Prop :=
  (* The converse goal, written as a Prop. It is NOT proved. *)
  forall (H : HonestMeasurementSystem),
    npa_psd (correlation_of H).

(** The above [Definition] just states the proposition. A proof would be:
    [Theorem honest_measurement_implies_npa : full_honest_implies_npa_status.]
    The proof is not given. The natural attempt fails because A3 (as
    formulated in [HonestMeasurement.v]) only gives the L1-shape bound
    |S| <= 2 at zero cost, which is not enough to imply zero-marginal
    NPA PSD. *)

(** ** Substrate connection anchor.

    The honest-measurement to NPA bridge in this file is part of the
    quantum-substrate chain whose mu-cost interpretation feeds into
    the Thiele Machine's mu-ledger. See the scope note below. *)

(* SCOPE NOTE: standalone proof scope (foundation connectivity).

    This file is standalone algebra. It does not engage VM semantics, no
    theorem here mentions [VMState] or [vm_mu], and it imports no kernel
    module. That is deliberate: the results stand on their own, and the
    connection to the mu-ledger is made by the theorems downstream that
    consume them (see UnificationProbeBridges), not by anything in this file.

    The audit is waived here rather than satisfied, because the only way to
    satisfy it from inside would be to add a definition that references
    [vm_mu] without using it; an identity function referenced by nothing
    carries no proof obligation. A link that can be manufactured that way is
    not evidence of one. The boundary is stated here rather than inferred
    from an import. *)
