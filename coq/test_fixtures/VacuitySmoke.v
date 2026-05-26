(** * VacuitySmoke.v — fixture for the kernel-conversion vacuity gate.

    Each [Theorem]/[Lemma] below carries a comment annotation:
      - (* EXPECT_VACUOUS_TRUE *)  : the gate's probe (a) should accept it
      - (* EXPECT_VACUOUS_HYP *)   : the gate's probe (b) should accept it
      - (* EXPECT_CLEAR *)         : neither probe should accept it

    The gate is sound (a positive probe is conclusive), so the
    EXPECT_VACUOUS_* fixtures must always flag. The gate is incomplete,
    so we only require EXPECT_CLEAR fixtures to be theorems we have no
    reason to expect the gate flags — if it does, that is a false positive
    in the gate, not in the fixture. *)

From Coq Require Import Arith.PeanoNat.

(** A definition the gate is required to unfold during probing. *)
Definition VacuouslyTrueProp : Prop := True.

(** A definition that does NOT reduce to True. *)
Definition GenuineEquality (n : nat) : Prop := S n = S n.

(** ** Vacuous theorems — gate MUST flag these. *)

(* EXPECT_VACUOUS_TRUE *)
Theorem smoke_literal_true : True.
Proof. exact I. Qed.

(* EXPECT_VACUOUS_TRUE *)
Theorem smoke_unfolds_to_true : VacuouslyTrueProp.
Proof. unfold VacuouslyTrueProp. exact I. Qed.

(* EXPECT_VACUOUS_TRUE *)
Theorem smoke_quantified_true : forall (n : nat), True.
Proof. intros _. exact I. Qed.

(* EXPECT_VACUOUS_HYP *)
Theorem smoke_identity : forall (P : Prop), P -> P.
Proof. intros P p. exact p. Qed.

(* EXPECT_VACUOUS_HYP *)
Theorem smoke_two_hyps_pick_first :
  forall (P Q : Prop), P -> Q -> P.
Proof. intros P Q p _. exact p. Qed.

(** ** Genuine theorems — gate MUST NOT flag these.

    These are simple but non-vacuous: the conclusion is neither True
    nor convertible to a hypothesis, even after [lazy] reduction. *)

(* EXPECT_CLEAR *)
Theorem smoke_addnSm : forall (n m : nat), S n + m = S (n + m).
Proof. intros. reflexivity. Qed.

(* EXPECT_CLEAR *)
Theorem smoke_succ_nonzero : forall (n : nat), S n <> 0.
Proof. intros n H. discriminate. Qed.

(* EXPECT_CLEAR *)
Theorem smoke_genuine_equality : forall n, GenuineEquality n.
Proof. intros n. unfold GenuineEquality. reflexivity. Qed.

(* EXPECT_CLEAR *)
Theorem smoke_modus_ponens :
  forall (P Q : Prop), (P -> Q) -> P -> Q.
Proof. intros P Q HPQ p. apply HPQ. exact p. Qed.
