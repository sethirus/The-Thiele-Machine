From Coq Require Import List Arith Bool Nat.
Import ListNotations.

(* Minimal oracle-to-instruction embedding for the Thiele machine.
   This file provides a small high-level language with `Ask` and
   `Compute`, a compiler that encodes oracle replies into `Instr`
   certificates, and a correctness lemma linking high-level
   oracle outputs to `obs_of_instr` on the compiled code. *)
From ThieleMachine Require Import ThieleMachine.
Import ThieleMachine.ThieleMachine.

Module HyperThieleOracleMinimal.

  Definition Oracle := nat -> bool.

  Inductive Cmd := Compute (n : nat) | Ask (q : nat).
  Definition Program := list Cmd.

  Fixpoint run_program (O : Oracle) (p : Program) : list bool :=
    match p with
    | [] => []
    | Compute _ :: tl => run_program O tl
    | Ask q :: tl => (O q) :: run_program O tl
    end.

  Fixpoint compile_code (O : Oracle) (p : Program) : list Instr :=
    match p with
    | [] => []
    | Compute _ :: tl => compile_code O tl
    | Ask q :: tl =>
        let reply := if O q then 1%nat else 0%nat in
        ({| instr_kind := InstrLASSERT; instr_event := Some q; instr_cert := reply |}
         :: compile_code O tl)
    end.

  Definition compile (O : Oracle) (p : Program) : Prog :=
    {| code := compile_code O p |}.

  Definition obs_to_bool (obs : StepObs) : bool := Nat.eqb (cert obs) 1%nat.

  (** [compile_preserves_oracle_outputs]: formal specification. *)
  Theorem compile_preserves_oracle_outputs :
    forall (O : Oracle) (p : Program),
      run_program O p = map obs_to_bool (map obs_of_instr (compile_code O p)).
  Proof.
    intros O p. induction p as [|cmd tl IH]; simpl.
    - reflexivity.
    - destruct cmd as [n | q].
      + simpl. apply IH.
      + simpl. unfold obs_to_bool. simpl. destruct (O q) eqn:Eq; simpl; rewrite IH; reflexivity.
  Qed.

End HyperThieleOracleMinimal.

(* End of HyperThiele_Oracle.v *)
