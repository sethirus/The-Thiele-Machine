(** =========================================================================
    Assumption Bundle - Clean Interface for Hard Mathematical Facts
    =========================================================================

    This file bundles all hard-to-prove mathematical assumptions into
    a single Record. Theorems that depend on these get the bundle as
    a parameter, making dependencies explicit.

    ========================================================================= *)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
From Kernel Require Import ValidCorrelation.
From Kernel Require Import AlgebraicCoherence.

(** Box type from ValidCorrelation *)
Definition Box := nat -> nat -> nat -> nat -> Q.

(** Bundle of all hard assumptions

    Usage:
      Section MyProofs.
        Context (A : HardMathFacts).
        (* Now use A.(norm_E_bound), A.(valid_S_4), etc. *)
      End MyProofs.
*)
Record HardMathFacts := {
  (** Assumption 1: Probability theory - correlations are bounded *)
  norm_E_bound : forall (B : Box) (x y : nat),
    (forall x y a b, 0 <= B x y a b) ->
    (forall x y, B x y 0%nat 0%nat + B x y 0%nat 1%nat +
                 B x y 1%nat 0%nat + B x y 1%nat 1%nat == 1) ->
    forall (E : nat -> nat -> Q),
    (E x y = 1 * 1 * B x y 0%nat 0%nat +
             1 * (-1) * B x y 0%nat 1%nat +
             (-1) * 1 * B x y 1%nat 0%nat +
             (-1) * (-1) * B x y 1%nat 1%nat) ->
    Qabs (E x y) <= 1;

  (** Assumption 2: Triangle inequality for CHSH *)
  valid_S_4 : forall (S E00 E01 E10 E11 : Q),
    Qabs E00 <= 1 -> Qabs E01 <= 1 ->
    Qabs E10 <= 1 -> Qabs E11 <= 1 ->
    S = E00 + E01 + E10 - E11 ->
    Qabs S <= 4;

  (** Assumption 3: Bell's CHSH inequality (16-case proof) *)
  local_S_2 : forall (S : Q) (a b : nat -> nat),
    (forall x, a x = 0%nat \/ a x = 1%nat) ->
    (forall y, b y = 0%nat \/ b y = 1%nat) ->
    S = (if Nat.eqb (a 0%nat) (b 0%nat) then 1 else -1) +
        (if Nat.eqb (a 0%nat) (b 1%nat) then 1 else -1) +
        (if Nat.eqb (a 1%nat) (b 0%nat) then 1 else -1) -
        (if Nat.eqb (a 1%nat) (b 1%nat) then 1 else -1) ->
    Qabs S <= 2;

  (** Assumption 4: PR box monogamy *)
  pr_no_ext : forall (pr_box : Box),
    (forall x y a b, pr_box x y a b =
      if Nat.eqb ((a + b) mod 2) ((x * y) mod 2) then 1#2 else 0) ->
    ~ (exists Box3 : nat -> nat -> nat -> nat -> nat -> nat -> Q,
        (forall x y z a b c, 0 <= Box3 x y z a b c) /\
        (forall x y a b,
          Box3 x y 0%nat a b 0%nat + Box3 x y 0%nat a b 1%nat +
          Box3 x y 1%nat a b 0%nat + Box3 x y 1%nat a b 1%nat ==
          pr_box x y a b));

  (** Assumption 5: NPA hierarchy bound *)
  symm_coh_bound : forall (e : Q) (correlators : Q -> Correlators),
    0 <= e ->
    algebraically_coherent (correlators e) ->
    e <= (707107#1000000);  (* 1/√2 ≈ 0.707107 *)

  (** Assumption 6: Tsirelson's theorem *)
  tsir_from_coh : forall (c : Correlators),
    algebraically_coherent c ->
    Qabs (E00 c) <= 1 /\ Qabs (E01 c) <= 1 /\
    Qabs (E10 c) <= 1 /\ Qabs (E11 c) <= 1 ->
    Qabs (S_from_correlators c) <= (28284271#10000000)  (* 2√2 ≈ 2.828427 *)
}.

(** Example: How to use the bundle *)
Section ExampleUsage.
  Context (facts : HardMathFacts).

  (** Any theorem can now explicitly depend on 'facts' *)
  Example correlation_bounded : forall B x y,
    (forall x y a b, 0 <= B x y a b) ->
    (forall x y, B x y 0%nat 0%nat + B x y 0%nat 1%nat +
                 B x y 1%nat 0%nat + B x y 1%nat 1%nat == 1) ->
    exists E : nat -> nat -> Q,
      E x y = 1 * 1 * B x y 0%nat 0%nat +
              1 * (-1) * B x y 0%nat 1%nat +
              (-1) * 1 * B x y 1%nat 0%nat +
              (-1) * (-1) * B x y 1%nat 1%nat /\
      Qabs (E x y) <= 1.
  Proof.
    intros Hnn Hnorm.
    exists (fun x y => 1 * 1 * B x y 0%nat 0%nat +
                       1 * (-1) * B x y 0%nat 1%nat +
                       (-1) * 1 * B x y 1%nat 0%nat +
                       (-1) * (-1) * B x y 1%nat 1%nat).
    split; [reflexivity |].
    apply (norm_E_bound facts); assumption.
  Qed.

End ExampleUsage.

(** Print Assumptions will show exactly which facts are used *)
(* Print Assumptions correlation_bounded. *)
(* Expected output: Axioms: facts : HardMathFacts *)
