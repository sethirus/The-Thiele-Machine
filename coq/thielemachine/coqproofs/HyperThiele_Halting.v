From Coq Require Import List Arith Bool Nat.
Import ListNotations.

From ThieleMachine Require Import HyperThiele_Oracle.
Import HyperThieleOracleMinimal.

Module HyperThiele_Halting.

  (**
    # HyperThiele halting oracle – experimental only

    The statements in this module assume a perfect halting oracle for the
    minimal HyperThiele language.  None of the lemmas below are part of the
    `make -C coq core` target; they live behind the dedicated ``make oracle``
    entry point so downstream work cannot accidentally rely on the hypothesis.
  *)

  Section OracleHypothesis.

    (** Postulate a hyper-oracle `H` and an abstract halting predicate.
        This isolates the non-computable assumption in one place and ensures
        downstream developments must import the section explicitly when they
        wish to reason under the oracle hypothesis. *)
    Context (H : Oracle) (Halts : nat -> Prop).

    Hypothesis H_correct : forall e, H e = true <-> Halts e.

    (** A tiny high-level Thiele program that queries the oracle on `e`. *)
    Definition halting_solver (e : nat) : Program := [ Ask e ].

    (** The solver returns `[true]` exactly when `Halts e` holds. *)
    Theorem hyper_thiele_decides_halting_bool :
      forall e,
        run_program H (halting_solver e) = [true] <-> Halts e.
    Proof.
      intros e. simpl. unfold halting_solver. simpl.
      split; intros Hres.
      - destruct (H e) eqn:Heq.
        + apply H_correct. assumption.
        + simpl in Hres. discriminate Hres.
      - apply H_correct in Hres. rewrite Hres. reflexivity.
    Qed.

  End OracleHypothesis.

End HyperThiele_Halting.

(* End of HyperThiele_Halting.v *)
