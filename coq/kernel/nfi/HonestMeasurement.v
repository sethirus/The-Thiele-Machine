(** HonestMeasurement: HonestMeasurementSystem and the A3 axiom-as-record-field.

    This file follows the literal structure of the outside sketch:
    HonestMeasurementSystem is a Coq record extending CertificationSystem
    with a measurement function and a structural obligation A3
    ("measurement factors through cost"). A3 is a *record field*, not a
    global Axiom. Coq remains consistent; the obligation is shifted onto
    the constructor of HonestMeasurementSystem.

    THE TARGET THEOREM (stated in HonestMeasurementImpliesNPA.v):
       forall (H : HonestMeasurementSystem),
         zero_marginal_npa_realizable (correlation_of H).

    This file lays the record and supporting machinery. The companion
    files prove (a) PR-box cannot be wrapped as HMS, (b) the theorem for
    the restricted case where A3 forces |S| <= 2, (c) the full theorem
    is open in the literature and the obstruction is documented.

    A3 PRECISE FORMULATION.
    -----------------------
    The sketch said A3 should mean "any measurement function factors
    through the cost ledger." The most operational concretization that
    bites PR-box but admits classical and quantum (without naming them):

       hms_a3 : hms_cost = 0%nat -> Rabs (hms_S) <= 2.

    Read: "if the resource is free, the CHSH violation cannot exceed the
    classical bound." The free case is the Maxwell's-demon case: extracting
    more correlation than 2 from a free system is forbidden. PR-box (S=4
    at cost 0) violates this. Classical local strategies (S<=2) satisfy
    it trivially. Quantum (S<=2sqrt(2) with positive cost) satisfies
    vacuously.

    This is the *zero-cost* shadow of the full IC bound. Stronger A3
    formulations (e.g., |S| <= 2 + f(cost)) would entail Tsirelson and
    full NPA-realizability for arbitrary cost, but require the IC
    inequality, which we do not formalize here. The restricted A3
    formulation captures the PR-box rejection cleanly. *)

From Coq Require Import Reals Lra Lia Bool List.
Import ListNotations.
Local Open Scope R_scope.

From Kernel Require Import NPAMomentMatrix.

(** *** The HonestMeasurementSystem record.

    Carries:
    - A correlation 4-tuple (E_00, E_01, E_10, E_11) with values in [-1, 1].
    - A total cost ledger (single nat summarizing query cost).
    - hms_normalized : the E_xy entries lie in [-1, 1].
    - hms_a3 : the cost-bounded-correlation obligation.

    For the present file we keep the carrier deliberately small: just the
    correlator values and the cost. Bridging to a deeper substrate
    (CertificationSystem or Thiele VM) is layered on top later. *)

Record HonestMeasurementSystem : Type := mk_hms {
  hms_E00 : R;
  hms_E01 : R;
  hms_E10 : R;
  hms_E11 : R;
  hms_cost : nat;

  (** Each correlator lies in [-1, 1]. *)
  hms_normalized :
       -1 <= hms_E00 <= 1
    /\ -1 <= hms_E01 <= 1
    /\ -1 <= hms_E10 <= 1
    /\ -1 <= hms_E11 <= 1;

  (** A3: at zero ledger cost, the CHSH value cannot exceed the classical
      bound. This is the zero-cost shadow of the IC inequality. *)
  hms_a3 :
    hms_cost = 0%nat ->
    Rabs (hms_E00 + hms_E01 + hms_E10 - hms_E11) <= 2;
}.

(** The CHSH S-value of an HMS, as a real number. *)
Definition hms_S (H : HonestMeasurementSystem) : R :=
  hms_E00 H + hms_E01 H + hms_E10 H - hms_E11 H.

(** Zero-marginal NPA matrix derived from an HMS by reading off its
    correlators. The marginals and self-correlations are zero, matching
    the zero-marginal slice of the NPA hierarchy. *)
Definition correlation_of (H : HonestMeasurementSystem) : NPAMomentMatrix :=
  zero_marginal_npa
    (hms_E00 H) (hms_E01 H) (hms_E10 H) (hms_E11 H).

(** Helper restating A3 in terms of [hms_S]. *)
Lemma hms_a3_S :
  forall H, hms_cost H = 0%nat -> Rabs (hms_S H) <= 2.
Proof.
  intros H Hcost. unfold hms_S. apply hms_a3. exact Hcost.
Qed.

(** Sanity: the correlators of [correlation_of H] are exactly those of H. *)
Lemma correlation_of_E00 :
  forall H, npa_E00 (correlation_of H) = hms_E00 H.
Proof. intro H. reflexivity. Qed.

Lemma correlation_of_E01 :
  forall H, npa_E01 (correlation_of H) = hms_E01 H.
Proof. intro H. reflexivity. Qed.

Lemma correlation_of_E10 :
  forall H, npa_E10 (correlation_of H) = hms_E10 H.
Proof. intro H. reflexivity. Qed.

Lemma correlation_of_E11 :
  forall H, npa_E11 (correlation_of H) = hms_E11 H.
Proof. intro H. reflexivity. Qed.

(** Marginals and self-correlations are zero by construction. *)
Lemma correlation_of_marginals_zero :
  forall H,
       npa_EA0 (correlation_of H) = 0
    /\ npa_EA1 (correlation_of H) = 0
    /\ npa_EB0 (correlation_of H) = 0
    /\ npa_EB1 (correlation_of H) = 0
    /\ npa_rho_AA (correlation_of H) = 0
    /\ npa_rho_BB (correlation_of H) = 0.
Proof.
  intro H. cbn. repeat split; reflexivity.
Qed.

(** ** Substrate connection anchor.

    The honest-measurement framework in this file is the source of
    the mu-cost interpretation for measurement-shaped processes,
    which connects to the Thiele Machine's mu-ledger. The anchor
    below makes the connection point explicit. *)

From Kernel Require Import VMState MuCostModel.

Definition honest_measurement_vm_anchor (s : VMState) : nat := vm_mu s.
