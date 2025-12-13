From Coq Require Import List Arith Bool Nat.
Import ListNotations.

From ThieleMachine Require Import HyperThiele_Oracle ThieleMachine Oracle PartitionLogic.
Import HyperThieleOracleMinimal ThieleMachine.ThieleMachine.

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

    Variable H_correct : forall e, H e = true <-> Halts e.

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

    (** Compile the solver into the concrete Thiele instruction stream. *)
    Definition halting_solver_prog (e : nat) : Prog :=
      compile H (halting_solver e).

    Definition halting_solver_trace (e : nat) : list bool :=
      map obs_to_bool (map obs_of_instr (code (halting_solver_prog e))).

    Definition halting_solver_t1_state (e : nat) (partition : Partition) : T1_State :=
      t1_bootstrap_state (halting_solver_prog e) partition.

    Definition halting_solver_canonical_actions (e : nat) (partition : Partition)
      : list T1_Action :=
      t1_closed_trace_mu_actions (halting_solver_t1_state e partition).

    Definition halting_solver_canonical_receipt (e : nat) (partition : Partition)
      : T1_Receipt :=
      t1_trace_receipt (halting_solver_t1_state e partition)
                       (halting_solver_canonical_actions e partition).

    Lemma halting_solver_canonical_receipt_witness :
      forall e partition,
        T1_ReceiptWitness (halting_solver_canonical_receipt e partition).
    Proof.
      intros e partition.
      unfold halting_solver_canonical_receipt,
             halting_solver_canonical_actions,
             halting_solver_t1_state.
      apply t1_trace_receipt_closed_witness_canonical.
    Qed.

    Theorem hyper_thiele_decides_halting_trace :
      forall e, halting_solver_trace e = [true] <-> Halts e.
      Proof.
        intro e.
        unfold halting_solver_trace, halting_solver_prog.
        cbn [HyperThieleOracleMinimal.compile code].
        rewrite <- compile_preserves_oracle_outputs.
        apply hyper_thiele_decides_halting_bool.
      Qed.

    Corollary hyper_thiele_compiled_solver_sound :
      forall e, halting_solver_trace e = [true] -> Halts e.
    Proof.
      intros e. apply -> hyper_thiele_decides_halting_trace.
    Qed.

    Corollary hyper_thiele_compiled_solver_complete :
      forall e, Halts e -> halting_solver_trace e = [true].
    Proof.
      intros e. apply <- hyper_thiele_decides_halting_trace.
    Qed.

  End OracleHypothesis.

End HyperThiele_Halting.

(* End of HyperThiele_Halting.v *)
