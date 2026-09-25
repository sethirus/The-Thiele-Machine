(** ValidCorrelation: an abstract correlation-box interface for the Bell layer

  This file defines the mathematical interface used by the Bell and CHSH
  arguments: valid boxes are non-negative, normalized, and no-signaling, and
  local boxes are convex combinations of deterministic strategies. The point
  is to separate the abstract correlation calculus from any specific machine
  or physical realization.

  The main theorem in this file is the classical deterministic CHSH bound.
  That result is purely algebraic. Quantum structure enters later, in other
  files, when extra premises are added.

  *)

(* SCOPE NOTE: standalone proof scope. This file stands on its own
   mathematics and does not engage VM semantics. No definition or theorem here
   mentions VMState, vm_step, vm_mu, MuCostModel or instruction_cost, and it
   imports no kernel module.

   The audit is waived rather than satisfied: satisfying it from inside would
   mean importing the kernel without using it, which asserts a bridge that is
   not here. Where these results feed the mu-ledger, they do so through the
   theorems downstream that consume them. The standalone boundary is stated
   here rather than inferred from an import. *)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.Lists.List.
Require Import Psatz.

Local Open Scope Q_scope.

(**
    CORRELATION BOX ABSTRACTION
    *)

(** [Box] is a four-index rational-valued correlation function. *)

(** The indices are used as input and output labels; the type does not supply a physical apparatus. *)

(** Rational arithmetic keeps this interface exact and avoids introducing a real-number representation here. *)
Definition Box := nat -> nat -> nat -> nat -> Q.

(**
    VALID CORRELATION PROPERTIES
    *)

(** [non_negative] requires every rational box entry to be nonnegative. *)
Definition non_negative (B : Box) : Prop :=
  forall x y a b, 0 <= B x y a b.

(** [normalized] requires the four binary-output entries to sum to one for every input pair. *)
Definition normalized (B : Box) : Prop :=
  forall x y, (B x y 0%nat 0%nat + B x y 0%nat 1%nat +
               B x y 1%nat 0%nat + B x y 1%nat 1%nat) == 1.

(**
    MARGINAL DISTRIBUTIONS
    *)

(** [marginal_a] adds the two entries with a fixed Alice output. *)
Definition marginal_a (B : Box) (x y a : nat) : Q :=
  B x y a 0%nat + B x y a 1%nat.

(** [marginal_b] adds the two entries with a fixed Bob output. *)
Definition marginal_b (B : Box) (x y b : nat) : Q :=
  B x y 0%nat b + B x y 1%nat b.

(**
    NO-SIGNALING CONDITION
    *)

(** [no_signaling] requires Alice's marginal to be independent of Bob's index and Bob's marginal to be independent of Alice's index. *)

(** The predicate is an algebraic condition on [Box] and does not by itself establish a relativistic or quantum interpretation. *)
Definition no_signaling (B : Box) : Prop :=
  (forall x y1 y2 a, marginal_a B x y1 a == marginal_a B x y2 a) /\
  (forall x1 x2 y b, marginal_b B x1 y b == marginal_b B x2 y b).

(**
    LOCAL BOXES (BELL'S TARGET)
    *)

(** [deterministic_box] requires the displayed point-mass form for two response functions. *)

(** [local_box] later packages a finite weighted list of such boxes. *)
Definition deterministic_box (B : Box) : Prop :=
  exists (fA fB : nat -> nat),
    forall x y a b, B x y a b ==
      (if (Nat.eqb a (fA x)) && (Nat.eqb b (fB y)) then 1 else 0).

(** [local_box] requires finite weights, matching list lengths, normalized weights, and pointwise weighted reconstruction. *)

(** The definition is the formal local-box witness used by later arguments. *)
Definition local_box (B : Box) : Prop :=
  exists (weights : list Q) (det_boxes : list Box),
    (forall db, In db det_boxes -> deterministic_box db) /\
    (forall w, In w weights -> 0 <= w) /\
    (length weights = length det_boxes) /\
    (fold_right Qplus 0 weights == 1) /\
    (forall x y a b, B x y a b == fold_right Qplus 0
      (map (fun '(w, db) => w * db x y a b) (combine weights det_boxes))).

(**
    BELL'S THEOREM (MATHEMATICAL CORE)
    *)

(** [bell_math_deterministic] proves the rational CHSH interval for four response values restricted to ±1. *)

(** The proof is exhaustive case analysis over those four disjunctions. *)

(** It is an algebraic theorem about the supplied rational functions, not a complete Bell experiment or quantum no-go theorem. *)
Theorem bell_math_deterministic :
  forall (gA gB : nat -> Q),
    (forall x, gA x == 1 \/ gA x == -1) ->
    (forall y, gB y == 1 \/ gB y == -1) ->
    Qabs (gA 0%nat * gB 0%nat + gA 0%nat * gB 1%nat +
          gA 1%nat * gB 0%nat - gA 1%nat * gB 1%nat) <= 2.
Proof.
  intros gA gB HgA HgB.

  (* === Exhaustive case analysis: 2^4 = 16 deterministic strategies === *)
  (* For each of gA(0), gA(1), gB(0), gB(1), branch on ±1 *)
  destruct (HgA 0%nat) as [A0 | A0]; destruct (HgA 1%nat) as [A1 | A1];
  destruct (HgB 0%nat) as [B0 | B0]; destruct (HgB 1%nat) as [B1 | B1];

  (* Substitute the ±1 values *)
  rewrite A0, A1, B0, B1;

  (* Simplify arithmetic and verify |S| ≤ 2 *)
  try field_simplify;   (* Algebraic simplification *)
  try apply Qabs_case;  (* Handle absolute value *)
  nra.                  (* Nonlinear rational arithmetic solver *)
                        (* Verifies the inequality for this case *)

  (* Coq repeats this for all 16 branches. Each succeeds. QED. *)
Qed.

(** This file supplies the rational box interface and one deterministic CHSH bound. *)

(** It does not by itself establish the quantum set, the Tsirelson bound, or a physical realization. *)
